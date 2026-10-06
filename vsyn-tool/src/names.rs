//! Naming a trace's values: `seq_scaling_list_present_flag[3] = 1`. This
//! replays the program over the trace (the encoder's walk, without the
//! bits), using vsyn's expression evaluator for indices.
use vsyn::raw::RawProg;
use vsyn::xir::*;

pub struct Named {
    pub name: String,
    pub value: i64,
    /// Bit position in the RBSP, and length of the code.
    pub pos: usize,
    pub len: usize,
    /// Its index in the trace.
    pub ti: usize,
}

fn ue_len(v: u64) -> usize {
    let m = v + 1;
    2 * (63 - m.leading_zeros() as usize) + 1
}

/// The bytes a `leb128()` of `v` takes at the least.
pub fn leb_min(v: u64) -> usize {
    let mut n = 1;
    let mut x = v;
    while x >= 128 { x /= 128; n += 1; }
    n
}

/// `ns(n)`'s code length for `x`.
pub fn ns_len(n: u64, x: u64) -> usize {
    let w = 64 - n.leading_zeros() as usize;
    let m = (1u64 << w) - n;
    if x < m { w - 1 } else { w }
}

struct Walk<'a> {
    raw: &'a RawProg,
    p: &'a ProgX,
    ctx: &'a Vec<Vec<i64>>,
    tr: &'a [i64],
    ch: &'a [u64],
    ti: usize,
    env: Vec<i64>,
    out: Vec<Named>,
    pos: usize,
}

impl<'a> Walk<'a> {
    fn label(&self, blk: usize, i: usize) -> (&'static str, u32) {
        let (s, _) = self.raw.blocks[blk];
        let lab = self.raw.sts[s as usize + i].6 as usize;
        self.raw.labels.get(lab).copied().unwrap_or(("?", u32::MAX))
    }

    fn name(&self, blk: usize, i: usize, flat: Option<i64>) -> String {
        let (n, vi) = self.label(blk, i);
        match flat {
            None => n.to_string(),
            Some(f) => {
                let dims: &[u32] = if vi == u32::MAX { &[] } else { self.raw.vars[vi as usize].2 };
                if dims.is_empty() { return n.to_string(); }
                let mut idx = Vec::new();
                let mut f = f;
                for d in dims.iter().rev() { idx.push(f % *d as i64); f /= *d as i64; }
                idx.reverse();
                let mut s = n.to_string();
                for x in idx { s.push_str(&format!("[{x}]")); }
                s
            }
        }
    }

    fn blk(&mut self, fuel: u32, b: usize) -> Option<()> {
        let n = self.p.blocks.get(b)?.len();
        for i in 0..n {
            self.stmt(fuel, b, i)?;
        }
        Some(())
    }

    fn stmt(&mut self, fuel: u32, b: usize, i: usize) -> Option<()> {
        let p = self.p;
        match &p.blocks[b][i] {
            StX::Read(d, ds) => {
                let v = *self.tr.get(self.ti)?;
                let c = self.ch.get(self.ti).copied().unwrap_or(0) as usize;
                self.ti += 1;
                let flat = match d { DstX::Elem(_, _, ix) => eval_x(&p.xs, &self.env, self.ctx, *ix), _ => None };
                let name = self.name(b, i, flat);
                let ev = |w: &usize| eval_x(&p.xs, &self.env, self.ctx, *w);
                let len = match ds {
                    DescX::U(w) | DescX::SU(w) => ev(w)? as usize,
                    DescX::UE => ue_len(v as u64),
                    DescX::SE => ue_len(if v > 0 { (2 * v - 1) as u64 } else { (-2 * v) as u64 }),
                    DescX::FF => 8 * (v as usize / 255 + 1),
                    DescX::NS(w) => ns_len(ev(w)? as u64, v as u64),
                    DescX::LE(w) => 8 * ev(w)? as usize,
                    DescX::UVLC => if v >= 4294967295 { 33 + c } else { ue_len(v as u64) },
                    DescX::LEB128 => 8 * (leb_min(v as u64) + c),
                };
                self.out.push(Named { name, value: v, pos: self.pos, len, ti: self.ti - 1 });
                self.pos += len;
                if !store_x(&p.xs, &mut self.env, self.ctx, d, v) { return None; }
            }
            StX::Let(d, e) => {
                let v = eval_x(&p.xs, &self.env, self.ctx, *e)?;
                if !store_x(&p.xs, &mut self.env, self.ctx, d, v) { return None; }
            }
            StX::Assert(_) | StX::Conf(_) => {}
            StX::Align => { self.pos += 1; while self.pos % 8 != 0 { self.pos += 1; } }
            StX::ZAlign => { while self.pos % 8 != 0 { self.pos += 1; } }
            StX::Pos(d) => { if !store_x(&p.xs, &mut self.env, self.ctx, d, self.pos as i64) { return None; } }
            StX::If(c, t, f) => {
                let v = eval_x(&p.xs, &self.env, self.ctx, *c)?;
                self.blk(fuel.checked_sub(1)?, if v != 0 { *t } else { *f })?;
            }
            StX::While(c, body) => {
                while eval_x(&p.xs, &self.env, self.ctx, *c)? != 0 {
                    self.blk(fuel.checked_sub(1)?, *body)?;
                }
            }
            StX::More(_, _, body) => {
                let n = *self.tr.get(self.ti)?;
                self.ti += 1;
                for _ in 0..n { self.blk(fuel.checked_sub(1)?, *body)?; }
            }
            StX::Call(blk) => self.blk(fuel.checked_sub(1)?, *blk)?,
        }
        Some(())
    }
}

/// The syntax elements of a trace, named, in order.
pub fn annotate(raw: &RawProg, p: &ProgX, ctx: &Vec<Vec<i64>>, tr: &[i64]) -> Vec<Named> {
    annotate_ch(raw, p, ctx, tr, &[])
}

/// The same, with the choices the encoding made (missing ones are 0).
pub fn annotate_ch(raw: &RawProg, p: &ProgX, ctx: &Vec<Vec<i64>>, tr: &[i64], ch: &[u64]) -> Vec<Named> {
    annotate_at(raw, p, ctx, vec![0; p.nslots], tr, ch)
}

/// The same, the variables starting as `env` (a format whose variables
/// carry over from one structure to the next).
pub fn annotate_at(raw: &RawProg, p: &ProgX, ctx: &Vec<Vec<i64>>, env: Vec<i64>, tr: &[i64], ch: &[u64]) -> Vec<Named> {
    let mut w = Walk { raw, p, ctx, tr, ch, ti: 0, env, out: Vec::new(), pos: 0 };
    let _ = w.blk(64, p.main);
    w.out
}

/// The value of a scalar variable of an environment.
pub fn get(raw: &RawProg, env: &[i64], name: &str) -> Option<i64> {
    raw.slot(name).map(|s| env[s])
}
