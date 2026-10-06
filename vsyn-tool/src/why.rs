//! Why a NAL unit was rejected: an unverified re-run of the decoder that
//! stops at the statement the verified one fails at, and says which it is.
//! For triage only; verdicts come from vsyn.
use vsyn::raw::RawProg;
use vsyn::xir::*;

struct Bits<'a> { b: &'a [u8], pos: usize, end: usize }

impl<'a> Bits<'a> {
    fn bit(&mut self) -> Option<u64> {
        if self.pos >= self.end { return None; }
        let v = (self.b[self.pos / 8] >> (7 - self.pos % 8)) & 1;
        self.pos += 1;
        Some(v as u64)
    }
    fn u(&mut self, n: usize) -> Option<u64> {
        let mut v = 0;
        for _ in 0..n { v = v * 2 + self.bit()?; }
        Some(v)
    }
    fn ue(&mut self) -> Option<u64> {
        let mut z = 0;
        while self.bit()? == 0 { z += 1; if z >= 32 { return None; } }
        Some((1u64 << z) - 1 + self.u(z)?)
    }
    fn uvlc(&mut self) -> Option<u64> {
        let mut z = 0;
        while self.bit()? == 0 { z += 1; }
        if z >= 32 { return Some(4294967295); }
        Some((1u64 << z) - 1 + self.u(z)?)
    }
    fn ns(&mut self, n: u64) -> Option<u64> {
        let w = 64 - n.leading_zeros() as usize;
        let m = (1u64 << w) - n;
        let v = self.u(w - 1)?;
        if v < m { return Some(v); }
        Some((v << 1) - m + self.bit()?)
    }
    fn le(&mut self, n: usize) -> Option<u64> {
        let mut t = 0;
        for i in 0..n { t += self.u(8)? << (8 * i); }
        Some(t)
    }
    fn leb128(&mut self) -> Result<u64, &'static str> {
        let mut v = 0u64;
        for i in 0..8 {
            let b = self.u(8).ok_or("out of data")?;
            v |= (b & 0x7f) << (7 * i);
            if b & 0x80 == 0 {
                return if v > 4294967295 { Err("leb128( ) above 2^32 - 1") } else { Ok(v) };
            }
        }
        Err("leb128( ): an 8th byte with its top bit set")
    }
}

struct W<'a> {
    raw: &'a RawProg,
    p: &'a ProgX,
    ctx: &'a Vec<Vec<i64>>,
    r: Bits<'a>,
    env: Vec<i64>,
    sealed: bool,
    last: String,
    hist: Vec<String>,
    confs: Vec<String>,
}

impl<'a> W<'a> {
    fn label(&self, blk: usize, i: usize) -> &'static str {
        let (s, _) = self.raw.blocks[blk];
        let lab = self.raw.sts[s as usize + i].6 as usize;
        self.raw.labels.get(lab).map(|l| l.0).unwrap_or("?")
    }
    fn fail(&self, what: String) -> Result<(), String> {
        Err(format!("{what} (at bit {}, after {})", self.r.pos, self.hist.join(", ")))
    }
    fn blk(&mut self, fuel: u32, b: usize) -> Result<(), String> {
        if fuel == 0 { return self.fail("nesting too deep".into()); }
        for i in 0..self.p.blocks[b].len() { self.stmt(fuel, b, i)?; }
        Ok(())
    }
    fn ev(&self, e: usize) -> Option<i64> { eval_x(&self.p.xs, &self.env, self.ctx, e) }
    fn stmt(&mut self, fuel: u32, b: usize, i: usize) -> Result<(), String> {
        let p = self.p;
        match &p.blocks[b][i] {
            StX::Read(d, ds) => {
                let name = self.label(b, i);
                if self.sealed { return self.fail(format!("{name}: read after more_rbsp_data( )")); }
                let v = match ds {
                    DescX::U(w) => match self.ev(*w) {
                        Some(n) if (0..=48).contains(&n) => self.r.u(n as usize).map(|v| v as i64),
                        _ => return self.fail(format!("{name}: width")),
                    },
                    DescX::UE => self.r.ue().map(|v| v as i64),
                    DescX::SU(w) => match self.ev(*w) {
                        Some(n) if (1..=48).contains(&n) => self.r.u(n as usize).map(|v| {
                            let v = v as i64;
                            if v >= 1 << (n - 1) { v - (1 << n) } else { v }
                        }),
                        _ => return self.fail(format!("{name}: width")),
                    },
                    DescX::NS(w) => match self.ev(*w) {
                        Some(n) if (1..=1 << 40).contains(&n) => self.r.ns(n as u64).map(|v| v as i64),
                        _ => return self.fail(format!("{name}: range")),
                    },
                    DescX::LE(w) => match self.ev(*w) {
                        Some(n) if (0..=6).contains(&n) => self.r.le(n as usize).map(|v| v as i64),
                        _ => return self.fail(format!("{name}: bytes")),
                    },
                    DescX::UVLC => self.r.uvlc().map(|v| v as i64),
                    DescX::LEB128 => match self.r.leb128() {
                        Ok(v) => Some(v as i64),
                        Err(e) => return self.fail(format!("{name}: {e}")),
                    },
                    DescX::SE => self.r.ue().map(|k| if k % 2 == 1 { ((k + 1) / 2) as i64 } else { -((k / 2) as i64) }),
                    DescX::FF => {
                        let mut acc = 0i64;
                        loop {
                            match self.r.u(8) { Some(255) => acc += 255, Some(x) => break Some(acc + x as i64), None => break None }
                        }
                    }
                };
                let v = match v { Some(v) => v, None => return self.fail(format!("{name}: out of data")) };
                if !store_x(&p.xs, &mut self.env, self.ctx, d, v) { return self.fail(format!("{name} = {v}: index out of range")); }
                self.last = format!("{name} = {v}");
                self.hist.push(self.last.clone());
                if self.hist.len() > 8 { self.hist.remove(0); }
            }
            StX::Let(d, e) => {
                let v = match self.ev(*e) { Some(v) => v, None => return self.fail("an assignment's expression fails".into()) };
                if !store_x(&p.xs, &mut self.env, self.ctx, d, v) { return self.fail(format!("assignment of {v}: index out of range")); }
            }
            StX::Assert(e) => match self.ev(*e) {
                Some(0) => return self.fail(format!("constraint {} is false", render(self.raw, *e, 0))),
                None => return self.fail(format!("constraint #{e} fails to evaluate")),
                _ => {}
            },
            StX::Conf(e) => {
                if self.ev(*e) == Some(0) {
                    let c = format!("{} (after {})", render(self.raw, *e, 0), self.last);
                    if !self.confs.contains(&c) { self.confs.push(c); }
                }
            }
            StX::If(c, t, f) => match self.ev(*c) {
                Some(v) => self.blk(fuel - 1, if v != 0 { *t } else { *f })?,
                None => return self.fail("an if's condition fails".into()),
            },
            StX::While(c, body) => loop {
                match self.ev(*c) {
                    Some(0) => break,
                    Some(_) => self.blk(fuel - 1, *body)?,
                    None => return self.fail("a loop's condition fails".into()),
                }
            },
            StX::More(mn, mx, body) => {
                let mut n = 0;
                while !(n >= *mn && (n >= *mx || self.r.pos == self.r.end)) {
                    let p0 = self.r.pos;
                    self.blk(fuel - 1, *body)?;
                    if self.r.pos <= p0 { return self.fail("an empty more_rbsp_data( ) iteration".into()); }
                    n += 1;
                }
                self.sealed = true;
            }
            StX::Call(blk) => self.blk(fuel - 1, *blk)?,
            StX::Align => {
                if self.r.bit() != Some(1) { return self.fail("byte_alignment( ): no 1".into()); }
                while self.r.pos % 8 != 0 { if self.r.bit() != Some(0) { return self.fail("byte_alignment( ): not 0".into()); } }
            }
            StX::ZAlign => {
                while self.r.pos % 8 != 0 { if self.r.bit() != Some(0) { return self.fail("byte_alignment( ): not 0".into()); } }
            }
            StX::Pos(d) => {
                let v = self.r.pos as i64;
                if !store_x(&p.xs, &mut self.env, self.ctx, d, v) { return self.fail("get_position( ): index out of range".into()); }
            }
        }
        Ok(())
    }
}

/// An expression, written out with variable names.
pub fn render(raw: &RawProg, e: usize, depth: u32) -> String {
    let xs = raw.xs;
    if e >= xs.len() || depth > 12 { return "…".into(); }
    let name = |slot: u64| -> String {
        let mut best: Option<&(&str, u32, &[u32])> = None;
        for v in raw.vars {
            if (v.1 as u64) <= slot && best.map_or(true, |b| b.1 < v.1) { best = Some(v); }
        }
        best.map(|b| b.0.to_string()).unwrap_or(format!("slot{slot}"))
    };
    let (t, a, b, c, d) = xs[e];
    let r = |x: u64| render(raw, x as usize, depth + 1);
    match t {
        0 => a.to_string(),
        1 => name(b),
        2 => format!("{}[{}]", name(b), r(d)),
        3 => format!("ctx{}.slot{}", a, b),
        4 => format!("ctx{}.arr{}[{}]", a, b, r(d)),
        5 => format!("{}({})", ["-", "!", "Abs", "CeilLog2", "FloorLog2"][a.min(4) as usize], r(b)),
        6 => format!("({} {} {})", r(b), ["+", "-", "*", "/", "%", "<<", ">>", "<", "<=", ">", ">=", "==", "!=", "&&", "||", "min", "max", "&", "|", "^"][a.min(19) as usize], r(c)),
        _ => format!("({} ? {} : {})", r(b), r(c), r(d)),
    }
}

/// Where decoding `rbsp` (to bit `end`) fails, if it does.
pub fn why(raw: &RawProg, p: &ProgX, ctx: &Vec<Vec<i64>>, rbsp: &[u8], end: usize) -> String {
    why_at(raw, p, ctx, vec![0; p.nslots], rbsp, end, true)
}

/// The same, the variables starting as `env`. With `whole`, the structure
/// is all of the data; without, it is at its front.
pub fn why_at(raw: &RawProg, p: &ProgX, ctx: &Vec<Vec<i64>>, env: Vec<i64>, rbsp: &[u8], end: usize, whole: bool) -> String {
    let mut w = W { raw, p, ctx, r: Bits { b: rbsp, pos: 0, end }, env, sealed: false, last: "the start".into(), hist: vec![], confs: vec![] };
    match w.blk(64, p.main) {
        Err(e) => e,
        Ok(()) if whole && w.r.pos != end => format!("{} bits left over (after {})", end - w.r.pos, w.last),
        Ok(()) => "no failure found".into(),
    }
}

/// The "decoders shall ignore" constraints decoding `rbsp` breaks.
pub fn nonconf(raw: &RawProg, p: &ProgX, ctx: &Vec<Vec<i64>>, rbsp: &[u8], end: usize) -> Vec<String> {
    nonconf_at(raw, p, ctx, vec![0; p.nslots], rbsp, end)
}

pub fn nonconf_at(raw: &RawProg, p: &ProgX, ctx: &Vec<Vec<i64>>, env: Vec<i64>, rbsp: &[u8], end: usize) -> Vec<String> {
    let mut w = W { raw, p, ctx, r: Bits { b: rbsp, pos: 0, end }, env, sealed: false, last: "the start".into(), hist: vec![], confs: vec![] };
    let _ = w.blk(64, p.main);
    w.confs
}

/// The SODB length of an RBSP, if it ends in trailing bits.
pub fn sodb_end(r: &[u8]) -> Option<usize> {
    let last = *r.last()?;
    if last == 0 { return None; }
    Some(8 * r.len() - 1 - last.trailing_zeros() as usize)
}
