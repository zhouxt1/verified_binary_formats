//! Random well-formed syntax structures, for structure-aware fuzzing.
//!
//! The generator walks a program as the encoder does, but chooses each
//! syntax element's value. A `range(lo, hi)` or `eq(v)` constraint right
//! after an element compiles to `lo <= x && x <= hi` or `x == v`; the
//! generator recognises those shapes and draws from the interval, so most
//! draws satisfy the tables. Whatever it produces is then encoded by vsyn's
//! verified encoder, which refuses anything the tables do not allow: a
//! generated stream is always a conforming encoding of its trace.
use std::collections::HashMap;
use vsyn::ir::BOp;
use vsyn::raw::RawProg;
use vsyn::xir::*;

pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        // xorshift64*
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    pub fn below(&mut self, n: u64) -> u64 { if n == 0 { 0 } else { self.next() % n } }
    pub fn chance(&mut self, num: u64, den: u64) -> bool { self.below(den) < num }
    /// A value in [lo, hi], biased toward the ends and small offsets.
    pub fn within(&mut self, lo: i64, hi: i64) -> i64 {
        if hi <= lo { return lo; }
        let span = (hi - lo) as u64;
        match self.below(10) {
            0 => lo,
            1 => hi,
            2..=5 => lo + self.below(span.min(4) + 1) as i64,
            6 => hi - self.below(span.min(4) + 1) as i64,
            _ => lo + self.below(span.saturating_add(1)) as i64,
        }
    }
}

pub struct Gen<'a> {
    pub raw: &'a RawProg,
    pub p: &'a ProgX,
    pub ctx: &'a Vec<Vec<i64>>,
    pub rng: &'a mut Rng,
    /// Values to use for syntax elements, by name.
    pub force: &'a HashMap<&'static str, i64>,
    env: Vec<i64>,
    tr: Vec<i64>,
    /// Encoded length so far, a rough bound on the structure's size.
    bits: usize,
    /// The exact bit position, for `get_position( )`.
    pos: usize,
    /// Keep the "decoders shall ignore" constraints too (a conforming
    /// structure), not only those a decoder checks.
    pub conforming: bool,
}

enum Bound { Range(i64, i64), Eq(i64) }

impl<'a> Gen<'a> {
    pub fn new(raw: &'a RawProg, p: &'a ProgX, ctx: &'a Vec<Vec<i64>>, rng: &'a mut Rng,
               force: &'a HashMap<&'static str, i64>) -> Gen<'a> {
        Gen { raw, p, ctx, rng, force, env: vec![0; p.nslots], tr: vec![], bits: 0, pos: 0, conforming: true }
    }

    fn label(&self, b: usize, i: usize) -> &'static str {
        let (s, _) = self.raw.blocks[b];
        let lab = self.raw.sts[s as usize + i].6 as usize;
        self.raw.labels.get(lab).map(|l| l.0).unwrap_or("?")
    }

    fn ev(&self, e: usize) -> Option<i64> { eval_x(&self.p.xs, &self.env, self.ctx, e) }

    /// Does expression `e` load the destination `d` (at its current index)?
    fn is_dst(&self, e: usize, d: &DstX) -> bool {
        match (&self.p.xs[e], d) {
            (ExX::Slot(s), DstX::Slot(t)) => s == t,
            (ExX::Elem(b, _, i), DstX::Elem(c, _, j)) => b == c && self.ev(*i) == self.ev(*j),
            _ => false,
        }
    }

    /// The interval an Assert right after a Read puts the element in.
    fn bound(&self, e: usize, d: &DstX) -> Option<Bound> {
        match &self.p.xs[e] {
            ExX::Bin(BOp::And, a, b) => match (&self.p.xs[*a], &self.p.xs[*b]) {
                (ExX::Bin(BOp::Le, lo, x), ExX::Bin(BOp::Le, x2, hi)) if self.is_dst(*x, d) && self.is_dst(*x2, d) => {
                    Some(Bound::Range(self.ev(*lo)?, self.ev(*hi)?))
                }
                _ => None,
            },
            ExX::Bin(BOp::Eq, x, v) if self.is_dst(*x, d) => Some(Bound::Eq(self.ev(*v)?)),
            _ => None,
        }
    }

    fn draw(&mut self, ds: &DescX) -> Option<i64> {
        Some(match ds {
            DescX::U(w) => {
                let n = self.ev(*w)?;
                if n <= 0 { return Some(0); }
                let max = if n >= 63 { i64::MAX } else { (1i64 << n) - 1 };
                self.rng.within(0, max)
            }
            DescX::UE => match self.rng.below(20) {
                0..=9 => self.rng.below(4) as i64,
                10..=16 => self.rng.below(32) as i64,
                17..=18 => self.rng.below(1024) as i64,
                _ => self.rng.below(1 << 20) as i64,
            },
            DescX::SE => {
                let m = match self.rng.below(20) {
                    0..=11 => self.rng.below(4) as i64,
                    12..=17 => self.rng.below(64) as i64,
                    _ => self.rng.below(1 << 16) as i64,
                };
                if self.rng.chance(1, 2) { -m } else { m }
            }
            DescX::FF => match self.rng.below(4) {
                0 => 255 + self.rng.below(300) as i64,
                _ => self.rng.below(255) as i64,
            },
            DescX::SU(w) => {
                let n = self.ev(*w)?;
                if !(1..=48).contains(&n) { return None; }
                let h = 1i64 << (n - 1);
                self.rng.within(-h, h - 1)
            }
            DescX::NS(w) => {
                let n = self.ev(*w)?;
                if n < 1 { return None; }
                self.rng.within(0, n - 1)
            }
            DescX::LE(w) => {
                let n = self.ev(*w)?;
                if !(0..=6).contains(&n) { return None; }
                if n == 0 { 0 } else { self.rng.within(0, (1i64 << (8 * n)) - 1) }
            }
            DescX::UVLC => match self.rng.below(20) {
                0..=9 => self.rng.below(4) as i64,
                10..=16 => self.rng.below(1024) as i64,
                _ => self.rng.below(1 << 32) as i64,
            },
            DescX::LEB128 => match self.rng.below(20) {
                0..=9 => self.rng.below(128) as i64,
                10..=16 => self.rng.below(1 << 14) as i64,
                _ => self.rng.below(1 << 32) as i64,
            },
        })
    }

    /// The length of a value's canonical code.
    fn code_len(&self, ds: &DescX, v: i64) -> Option<usize> {
        let ue_len = |m: u64| 2 * (63 - (m + 1).leading_zeros() as usize) + 1;
        Some(match ds {
            DescX::U(w) => self.ev(*w)? as usize,
            DescX::UE => ue_len(v as u64),
            DescX::SE => ue_len(if v > 0 { (2 * v - 1) as u64 } else { (-2 * v) as u64 }),
            DescX::FF => 8 * (v as usize / 255 + 1),
            DescX::SU(w) => self.ev(*w)? as usize,
            DescX::NS(w) => crate::names::ns_len(self.ev(*w)? as u64, v as u64),
            DescX::LE(w) => 8 * self.ev(*w)? as usize,
            DescX::UVLC => if v >= 4294967295 { 33 } else { ue_len(v as u64) },
            DescX::LEB128 => 8 * crate::names::leb_min(v as u64),
        })
    }

    fn blk(&mut self, fuel: u32, b: usize) -> Option<()> {
        if fuel == 0 || self.bits > 1 << 16 { return None; }
        let n = self.p.blocks.get(b)?.len();
        let mut i = 0;
        while i < n {
            i = self.stmt(fuel, b, i)?;
        }
        Some(())
    }

    /// Run statement `i`; return the next one to run.
    fn stmt(&mut self, fuel: u32, b: usize, i: usize) -> Option<usize> {
        let p = self.p;
        match &p.blocks[b][i] {
            StX::Read(d, ds) => {
                let name = self.label(b, i);
                // the constraints right after the element
                let mut asserts = vec![];
                let mut k = i + 1;
                while k < p.blocks[b].len() {
                    match &p.blocks[b][k] {
                        StX::Assert(e) => asserts.push(*e),
                        StX::Conf(e) => if self.conforming { asserts.push(*e) },
                        _ => break,
                    }
                    k += 1;
                }
                let saved = self.env.clone();
                for attempt in 0..24 {
                    self.env = saved.clone();
                    let mut v = match self.force.get(name) { Some(&v) => v, None => self.draw(ds)? };
                    if attempt > 0 && !self.force.contains_key(name) {
                        // a first try that failed: draw inside the bound, if there is one
                        if let Some(bd) = asserts.first().and_then(|&e| {
                            if !store_x(&p.xs, &mut self.env, self.ctx, d, 0) { return None; }
                            self.bound(e, d)
                        }) {
                            self.env = saved.clone();
                            v = match bd { Bound::Range(lo, hi) => self.rng.within(lo, hi), Bound::Eq(x) => x };
                        }
                    }
                    if !store_x(&p.xs, &mut self.env, self.ctx, d, v) { continue; }
                    if asserts.iter().all(|&e| self.ev(e).map_or(false, |x| x != 0)) {
                        self.tr.push(v);
                        self.bits += 8;
                        self.pos += self.code_len(ds, v)?;
                        return Some(k);
                    }
                }
                return None;
            }
            StX::Let(d, e) => {
                let v = self.ev(*e)?;
                if !store_x(&p.xs, &mut self.env, self.ctx, d, v) { return None; }
            }
            StX::Assert(e) => { if self.ev(*e)? == 0 { return None; } }
            StX::Conf(e) => { if self.conforming && self.ev(*e)? == 0 { return None; } }
            StX::Align => { self.pos += 1; while self.pos % 8 != 0 { self.pos += 1; } }
            StX::ZAlign => { while self.pos % 8 != 0 { self.pos += 1; } }
            StX::Pos(d) => { if !store_x(&p.xs, &mut self.env, self.ctx, d, self.pos as i64) { return None; } }
            StX::If(c, t, f) => { let v = self.ev(*c)?; self.blk(fuel - 1, if v != 0 { *t } else { *f })?; }
            StX::While(c, body) => {
                let mut n = 0;
                while self.ev(*c)? != 0 {
                    self.blk(fuel - 1, *body)?;
                    n += 1;
                    if n > 1 << 16 { return None; }
                }
            }
            StX::More(mn, mx, body) => {
                let extra = if self.rng.chance(1, 3) { 0 } else { self.rng.below(4) };
                let n = (*mn + extra).min(*mx);
                self.tr.push(n as i64);
                for _ in 0..n { self.blk(fuel - 1, *body)?; }
            }
            StX::Call(blk) => self.blk(fuel - 1, *blk)?,
        }
        Some(i + 1)
    }

    /// A trace, if the walk found one (the encoder has the last word).
    pub fn run(mut self) -> Option<Vec<i64>> {
        self.blk(64, self.p.main)?;
        Some(self.tr)
    }
}
