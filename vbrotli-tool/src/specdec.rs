//! `vbrotli::spec`, transcribed into plain Rust function by function, so the
//! spec can be run and tested against other decoders before (and while) the
//! verified decoder is proved against it. Names and structure follow
//! spec.rs; the one liberty is prefix-code decoding, which counts codes per
//! length (as puff.c) instead of searching all symbols, and computes the
//! same symbol for every code that is not over-subscribed (the only codes
//! the spec lets through).
//!
//! Integers are u64 (spec `nat`) or i64 (spec `int`); bit positions are
//! u64 offsets into the LSB-first bits of the input.

use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

/// Coverage counters, printed by `vbrotli-tool` when VB_COVER is set.
pub const COVER: [&str; 24] = [
    "simple code nsym=1", "simple code nsym=2", "simple code nsym=3", "simple code nsym=4 ts=0",
    "simple code nsym=4 ts=1", "complex code", "complex hskip=2", "complex hskip=3",
    "cl code of one symbol", "repeat 16 extended", "repeat 17 extended", "context map with rle",
    "context map imtf", "nbltypes >= 2 switch", "switch symbol 0 (prev)", "switch symbol 1 (next)",
    "short distance 0 explicit", "short distance 1..15", "direct distance", "npostfix > 0",
    "dictionary word", "transform not identity", "uncompressed meta-block", "metadata meta-block",
];
pub static HITS: [AtomicU64; 24] = [const { AtomicU64::new(0) }; 24];
fn hit(i: usize) {
    HITS[i].fetch_add(1, Relaxed);
}

pub struct Bits<'a> {
    pub buf: &'a [u8],
}

impl<'a> Bits<'a> {
    pub fn len(&self) -> u64 {
        8 * self.buf.len() as u64
    }
    fn bit(&self, p: u64) -> u64 {
        ((self.buf[(p / 8) as usize] >> (p % 8)) & 1) as u64
    }
    /// `getbits`: `n` bits at `p`, the first the least significant.
    pub fn getbits(&self, p: u64, n: u64) -> Option<u64> {
        if p + n > self.len() {
            return None;
        }
        let mut v = 0u64;
        for j in 0..n {
            v |= self.bit(p + j) << j;
        }
        Some(v)
    }
    /// `codebits`: `l` bits at `p`, the first the most significant.
    fn codebits(&self, p: u64, l: u64) -> u64 {
        let mut v = 0u64;
        for j in 0..l {
            v = 2 * v + self.bit(p + j);
        }
        v
    }
}

pub fn align8(p: u64) -> u64 {
    if p % 8 == 0 { p } else { p + (8 - p % 8) }
}

pub fn zero_fill(b: &Bits, p: u64) -> bool {
    b.getbits(p, align8(p) - p) == Some(0)
}

pub fn bytes_at(b: &Bits, q: u64, n: u64) -> Vec<u8> {
    (0..n).map(|j| b.getbits(q + 8 * j, 8).unwrap() as u8).collect()
}

// --------------------------------------------------------- prefix codes

fn nnz(lens: &[u8]) -> usize {
    lens.iter().filter(|&&l| l != 0).count()
}

fn first_nz(lens: &[u8]) -> u64 {
    lens.iter().position(|&l| l != 0).unwrap_or(lens.len()) as u64
}

/// `decode_sym` of vdeflate's spec: the canonical code's symbol whose code
/// the bits at `p` start with, shortest first.
fn decode_sym(lens: &[u8], b: &Bits, p: u64) -> Option<(u64, u64)> {
    let mut count = [0u64; 16];
    for &l in lens {
        count[l as usize] += 1;
    }
    // next_code[l] of RFC 1951 3.2.2 (bl_count[0] = 0).
    let mut next = [0u64; 16];
    let mut code = 0u64;
    for l in 1..16 {
        code = (code + if l >= 2 { count[l - 1] } else { 0 }) << 1;
        next[l] = code;
    }
    for l in 1..=15u64 {
        if p + l > b.len() {
            return None;
        }
        let v = b.codebits(p, l);
        if count[l as usize] > 0 && v >= next[l as usize] && v < next[l as usize] + count[l as usize] {
            // The (v - next)-th symbol of length l, in symbol order.
            let k = v - next[l as usize];
            let mut seen = 0;
            for (s, &ll) in lens.iter().enumerate() {
                if ll as u64 == l {
                    if seen == k {
                        return Some((s as u64, p + l));
                    }
                    seen += 1;
                }
            }
        }
    }
    None
}

pub fn dsym(lens: &[u8], b: &Bits, p: u64) -> Option<(u64, u64)> {
    if nnz(lens) == 1 { Some((first_nz(lens), p)) } else { decode_sym(lens, b, p) }
}

fn abits(asize: u64) -> u64 {
    let mut k = 1;
    while (1u64 << k) < asize && k < 11 {
        k += 1;
    }
    k
}

fn read_syms(b: &Bits, mut p: u64, asize: u64, n: u64) -> Option<(Vec<u64>, u64)> {
    let mut acc = vec![];
    while (acc.len() as u64) < n {
        let v = b.getbits(p, abits(asize))?;
        if v >= asize {
            return None;
        }
        acc.push(v);
        p += abits(asize);
    }
    Some((acc, p))
}

fn distinct(s: &[u64]) -> bool {
    (0..s.len()).all(|i| (i + 1..s.len()).all(|j| s[i] != s[j]))
}

fn simple_code(b: &Bits, p: u64, asize: u64) -> Option<(Vec<u8>, u64)> {
    let m = b.getbits(p, 2)?;
    let (s, q) = read_syms(b, p + 2, asize, m + 1)?;
    let mut z = vec![0u8; asize as usize];
    if !distinct(&s) {
        return None;
    }
    let set = |z: &mut Vec<u8>, ls: &[u8]| {
        for (i, &l) in ls.iter().enumerate() {
            z[s[i] as usize] = l;
        }
    };
    hit(m as usize + if m == 3 { b.getbits(q, 1).unwrap_or(0) as usize } else { 0 });
    if m == 0 {
        set(&mut z, &[1]);
        Some((z, q))
    } else if m == 1 {
        set(&mut z, &[1, 1]);
        Some((z, q))
    } else if m == 2 {
        set(&mut z, &[1, 2, 2]);
        Some((z, q))
    } else {
        let ts = b.getbits(q, 1)?;
        if ts == 0 { set(&mut z, &[2, 2, 2, 2]) } else { set(&mut z, &[1, 2, 3, 3]) }
        Some((z, q + 1))
    }
}

fn cl_len(b: &Bits, p: u64) -> Option<(u64, u64)> {
    let v = b.getbits(p, 2)?;
    if v == 0 {
        Some((0, p + 2))
    } else if v == 2 {
        Some((3, p + 2))
    } else if v == 1 {
        Some((4, p + 2))
    } else {
        let x = b.getbits(p + 2, 1)?;
        if x == 0 {
            Some((2, p + 3))
        } else {
            let y = b.getbits(p + 3, 1)?;
            if y == 0 { Some((1, p + 4)) } else { Some((5, p + 4)) }
        }
    }
}

const CL_ORDER: [usize; 18] = [1, 2, 3, 4, 0, 5, 17, 6, 16, 7, 8, 9, 10, 11, 12, 13, 14, 15];

fn read_cl(b: &Bits, mut p: u64, mut i: u64) -> Option<(Vec<u8>, u64)> {
    let mut acc = vec![0u8; 18];
    let mut space: i64 = 32;
    let mut num = 0;
    loop {
        if i >= 18 {
            return if num == 1 { Some((acc, p)) } else { None };
        }
        let (v, q) = cl_len(b, p)?;
        acc[CL_ORDER[i as usize]] = v as u8;
        p = q;
        if v != 0 {
            let s2 = space - (32 >> v);
            if s2 == 0 {
                return Some((acc, q));
            } else if s2 < 0 {
                return None;
            }
            space = s2;
            num += 1;
        }
        i += 1;
    }
}

fn read_lens(cl: &[u8], b: &Bits, mut p: u64, asize: u64) -> Option<(Vec<u8>, u64)> {
    let mut acc = vec![0u8; asize as usize];
    let (mut sym, mut space, mut prev, mut rep, mut rep_len) = (0u64, 32768i64, 8u64, 0u64, 0u64);
    loop {
        if sym >= asize || space <= 0 {
            return if space == 0 { Some((acc, p)) } else { None };
        }
        let (s, q) = dsym(cl, b, p)?;
        if s == 0 {
            sym += 1;
            rep = 0;
            p = q;
        } else if s < 16 {
            acc[sym as usize] = s as u8;
            sym += 1;
            space -= 32768 >> s;
            prev = s;
            rep = 0;
            p = q;
        } else {
            let nb = if s == 16 { 2 } else { 3 };
            let nl = if s == 16 { prev } else { 0 };
            let e = b.getbits(q, nb)?;
            let old = if rep_len == nl { rep } else { 0 };
            if old > 0 { hit(if s == 16 { 9 } else { 10 }) }
            let r = (if old > 0 { (old - 2) << nb } else { 0 }) + e + 3;
            let delta = r - old;
            if s > 17 || delta == 0 || sym + delta > asize {
                return None;
            }
            for j in sym..sym + delta {
                acc[j as usize] = nl as u8;
            }
            if nl != 0 {
                space -= delta as i64 * (32768 >> nl);
            }
            sym += delta;
            rep = r;
            rep_len = nl;
            p = q + nb;
        }
    }
}

pub fn read_code(b: &Bits, p: u64, asize: u64) -> Option<(Vec<u8>, u64)> {
    let h = b.getbits(p, 2)?;
    if h == 1 {
        simple_code(b, p + 2, asize)
    } else {
        hit(5);
        if h == 2 { hit(6) }
        if h == 3 { hit(7) }
        let (cl, q) = read_cl(b, p + 2, h)?;
        if nnz(&cl) == 1 { hit(8) }
        read_lens(&cl, b, q, asize)
    }
}

// ------------------------------------------------------------- integers

fn varlen8(b: &Bits, p: u64) -> Option<(u64, u64)> {
    if b.getbits(p, 1)? == 0 {
        return Some((0, p + 1));
    }
    let n = b.getbits(p + 1, 3)?;
    if n == 0 {
        return Some((1, p + 4));
    }
    let e = b.getbits(p + 4, n)?;
    Some(((1 << n) + e, p + 4 + n))
}

const BC_BASE: [u64; 26] = [1, 5, 9, 13, 17, 25, 33, 41, 49, 65, 81, 97, 113, 145, 177, 209, 241, 305, 369, 497,
    753, 1265, 2289, 4337, 8433, 16625];
const BC_EXTRA: [u64; 26] = [2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 7, 8, 9, 10, 11, 12, 13, 24];
const INS_BASE: [u64; 24] = [0, 1, 2, 3, 4, 5, 6, 8, 10, 14, 18, 26, 34, 50, 66, 98, 130, 194, 322, 578, 1090, 2114,
    6210, 22594];
const INS_EXTRA: [u64; 24] = [0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 8, 9, 10, 12, 14, 24];
const COPY_BASE: [u64; 24] = [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 18, 22, 30, 38, 54, 70, 102, 134, 198, 326, 582,
    1094, 2118];
const COPY_EXTRA: [u64; 24] = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 8, 9, 10, 24];
const CELL_INS: [u64; 11] = [0, 0, 0, 0, 8, 8, 0, 16, 8, 16, 16];
const CELL_COPY: [u64; 11] = [0, 8, 0, 8, 0, 8, 16, 0, 16, 8, 16];

fn ins_code(c: u64) -> u64 {
    CELL_INS[(c / 64) as usize] + (c / 8) % 8
}

fn copy_code(c: u64) -> u64 {
    CELL_COPY[(c / 64) as usize] + c % 8
}

fn read_count(code: &[u8], b: &Bits, p: u64) -> Option<(u64, u64)> {
    let (s, q) = dsym(code, b, p)?;
    if s >= 26 {
        return None;
    }
    let e = b.getbits(q, BC_EXTRA[s as usize])?;
    Some((BC_BASE[s as usize] + e, q + BC_EXTRA[s as usize]))
}

// ---------------------------------------------------- the context model

fn read_cmap_vals(code: &[u8], rlemax: u64, b: &Bits, mut p: u64, size: u64) -> Option<(Vec<u64>, u64)> {
    let mut acc = vec![];
    while (acc.len() as u64) < size {
        let (s, q) = dsym(code, b, p)?;
        if s == 0 {
            acc.push(0);
            p = q;
        } else if s <= rlemax {
            let e = b.getbits(q, s)?;
            if acc.len() as u64 + (1 << s) + e > size {
                return None;
            }
            for _ in 0..(1 << s) + e {
                acc.push(0);
            }
            p = q + s;
        } else {
            acc.push(s - rlemax);
            p = q;
        }
    }
    Some((acc, p))
}

fn imtf(v: &[u64]) -> Vec<u64> {
    let mut mtf: Vec<u64> = (0..256).collect();
    let mut out = vec![];
    for &i in v {
        let x = mtf.remove(i as usize);
        out.push(x);
        mtf.insert(0, x);
    }
    out
}

fn read_cmap(b: &Bits, p: u64, size: u64) -> Option<(Vec<u64>, u64, u64)> {
    let (t, q) = varlen8(b, p)?;
    if t == 0 {
        return Some((vec![0; size as usize], 1, q));
    }
    let ntrees = t + 1;
    let (rlemax, q2) = if b.getbits(q, 1)? == 0 { (0, q + 1) } else { (b.getbits(q + 1, 4)? + 1, q + 5) };
    if rlemax > 0 { hit(11) }
    let (code, q3) = read_code(b, q2, ntrees + rlemax)?;
    let (v, q4) = read_cmap_vals(&code, rlemax, b, q3, size)?;
    let x = b.getbits(q4, 1)?;
    if x == 1 { hit(12) }
    let map = if x == 1 { imtf(&v) } else { v };
    if map.iter().any(|&m| m >= ntrees) {
        return None; // not reached
    }
    Some((map, ntrees, q4 + 1))
}

fn p1(out: &[u8]) -> u8 {
    if !out.is_empty() { out[out.len() - 1] } else { 0 }
}

fn p2b(out: &[u8]) -> u8 {
    if out.len() >= 2 { out[out.len() - 2] } else { 0 }
}

fn lit_ctx(mode: u64, x1: u8, x2: u8) -> u64 {
    use vbrotli::tables::{LUT0, LUT1, LUT2};
    if mode == 0 {
        (x1 % 64) as u64
    } else if mode == 1 {
        (x1 / 4) as u64
    } else if mode == 2 {
        (LUT0[x1 as usize] | LUT1[x2 as usize]) as u64
    } else {
        (8 * LUT2[x1 as usize] + LUT2[x2 as usize]) as u64
    }
}

fn dist_ctx(clen: u64) -> u64 {
    if clen > 4 { 3 } else { clen - 2 }
}

// -------------------------------------------------------------- distances

fn dist_asize(npostfix: u64, ndirect: u64) -> u64 {
    16 + ndirect + (48 << npostfix)
}

fn short_dist(ring: &[i64; 4], c: u64) -> i64 {
    if c < 4 {
        ring[c as usize]
    } else {
        let base = if c < 10 { ring[0] } else { ring[1] };
        let k = if c < 10 { c - 4 } else { c - 10 } as i64;
        if k % 2 == 0 { base - (k / 2 + 1) } else { base + (k / 2 + 1) }
    }
}

fn dist_nbits(npostfix: u64, ndirect: u64, dcode: u64) -> u64 {
    1 + ((dcode - ndirect - 16) >> (npostfix + 1))
}

fn long_dist(npostfix: u64, ndirect: u64, dcode: u64, dextra: u64) -> u64 {
    let x = dcode - ndirect - 16;
    let hcode = x >> npostfix;
    let lcode = x & ((1 << npostfix) - 1);
    let offset = ((2 + hcode % 2) << dist_nbits(npostfix, ndirect, dcode)) - 4;
    ((offset + dextra) << npostfix) + lcode + ndirect + 1
}

// ----------------------------------------------------- static dictionary

fn doffset(len: u64) -> u64 {
    use vbrotli::tables::NDBITS;
    (0..len).map(|l| if l >= 4 { l << NDBITS[l as usize] } else { 0 }).sum()
}

fn dict_word(dict: &[u8], len: u64, idx: u64) -> Vec<u8> {
    let o = (doffset(len) + idx * len) as usize;
    dict[o..o + len as usize].to_vec()
}

fn ferment(w: &mut [u8], pos: usize) -> usize {
    if w[pos] < 192 {
        if (97..=122).contains(&w[pos]) {
            w[pos] ^= 32;
        }
        1
    } else if w[pos] < 224 {
        if pos + 1 < w.len() {
            w[pos + 1] ^= 32;
        }
        2
    } else {
        if pos + 2 < w.len() {
            w[pos + 2] ^= 5;
        }
        3
    }
}

fn elem(t: u64, mut w: Vec<u8>) -> Vec<u8> {
    if t == 0 {
        w
    } else if t == 1 {
        if !w.is_empty() {
            ferment(&mut w, 0);
        }
        w
    } else if t == 2 {
        let mut i = 0;
        while i < w.len() {
            i += ferment(&mut w, i);
        }
        w
    } else if t <= 11 {
        let k = (t - 2) as usize;
        if w.len() < k { vec![] } else { w[k..].to_vec() }
    } else {
        let k = (t - 11) as usize;
        if w.len() < k { vec![] } else { w[..w.len() - k].to_vec() }
    }
}

fn transform(id: u64, w: Vec<u8>) -> Vec<u8> {
    use vbrotli::tables::{TR_PRE, TR_PRE_OFF, TR_SUF, TR_SUF_OFF, TR_TYPE};
    let i = id as usize;
    let mut o = TR_PRE[TR_PRE_OFF[i] as usize..TR_PRE_OFF[i + 1] as usize].to_vec();
    o.extend(elem(TR_TYPE[i] as u64, w));
    o.extend(&TR_SUF[TR_SUF_OFF[i] as usize..TR_SUF_OFF[i + 1] as usize]);
    o
}

// ------------------------------------------------- the meta-block header

#[derive(Clone)]
struct Cat {
    n: u64,
    tcode: Vec<u8>,
    ccode: Vec<u8>,
    first: u64,
}

fn read_cat(b: &Bits, p: u64) -> Option<(Cat, u64)> {
    let (v, q) = varlen8(b, p)?;
    if v == 0 {
        return Some((Cat { n: 1, tcode: vec![], ccode: vec![], first: 1 << 24 }, q));
    }
    let (tcode, q2) = read_code(b, q, v + 3)?;
    let (ccode, q3) = read_code(b, q2, 26)?;
    let (first, q4) = read_count(&ccode, b, q3)?;
    Some((Cat { n: v + 1, tcode, ccode, first }, q4))
}

fn read_modes(b: &Bits, mut p: u64, n: u64) -> Option<(Vec<u64>, u64)> {
    let mut acc = vec![];
    while (acc.len() as u64) < n {
        acc.push(b.getbits(p, 2)?);
        p += 2;
    }
    Some((acc, p))
}

fn read_codes(b: &Bits, mut p: u64, asize: u64, n: u64) -> Option<(Vec<Vec<u8>>, u64)> {
    let mut acc = vec![];
    while (acc.len() as u64) < n {
        let (c, q) = read_code(b, p, asize)?;
        acc.push(c);
        p = q;
    }
    Some((acc, p))
}

struct Hdr {
    cl: Cat,
    ci: Cat,
    cd: Cat,
    npostfix: u64,
    ndirect: u64,
    modes: Vec<u64>,
    cmapl: Vec<u64>,
    cmapd: Vec<u64>,
    lit: Vec<Vec<u8>>,
    cmd: Vec<Vec<u8>>,
    dist: Vec<Vec<u8>>,
}

fn read_hdr(b: &Bits, p: u64) -> Option<(Hdr, u64)> {
    let (cl, p1) = read_cat(b, p)?;
    let (ci, p2) = read_cat(b, p1)?;
    let (cd, p3) = read_cat(b, p2)?;
    let npostfix = b.getbits(p3, 2)?;
    let nd4 = b.getbits(p3 + 2, 4)?;
    let ndirect = nd4 << npostfix;
    let (modes, p4) = read_modes(b, p3 + 6, cl.n)?;
    let (cmapl, ntl, p5) = read_cmap(b, p4, 64 * cl.n)?;
    let (cmapd, ntd, p6) = read_cmap(b, p5, 4 * cd.n)?;
    let (lit, p7) = read_codes(b, p6, 256, ntl)?;
    let (cmd, p8) = read_codes(b, p7, 704, ci.n)?;
    let (dist, p9) = read_codes(b, p8, dist_asize(npostfix, ndirect), ntd)?;
    Some((Hdr { cl, ci, cd, npostfix, ndirect, modes, cmapl, cmapd, lit, cmd, dist }, p9))
}

// -------------------------------------------------------------- commands

#[derive(Clone, Copy)]
struct Blk {
    t: u64,
    prev: u64,
    left: u64,
}

fn blk0(c: &Cat) -> Blk {
    Blk { t: 0, prev: 1, left: c.first }
}

fn next_blk(c: &Cat, k: Blk, b: &Bits, p: u64) -> Option<(Blk, u64)> {
    if k.left > 0 {
        return Some((Blk { t: k.t, prev: k.prev, left: k.left - 1 }, p));
    }
    if c.n < 2 {
        return None;
    }
    let (s, q) = dsym(&c.tcode, b, p)?;
    hit(13);
    if s == 0 { hit(14) }
    if s == 1 { hit(15) }
    let t = if s == 0 { k.prev } else if s == 1 { (k.t + 1) % c.n } else { s - 2 };
    let (cnt, r) = read_count(&c.ccode, b, q)?;
    Some((Blk { t, prev: k.t, left: cnt - 1 }, r))
}

/// `lits`, appending to `out` in place.
fn lits(h: &Hdr, b: &Bits, mut p: u64, n: u64, out: &mut Vec<u8>, mut bl: Blk) -> Option<(Blk, u64)> {
    for _ in 0..n {
        let (bl2, q) = next_blk(&h.cl, bl, b, p)?;
        let ctx = lit_ctx(h.modes[bl2.t as usize], p1(out), p2b(out));
        let (s, r) = dsym(&h.lit[h.cmapl[(64 * bl2.t + ctx) as usize] as usize], b, q)?;
        out.push(s as u8);
        bl = bl2;
        p = r;
    }
    Some((bl, p))
}

pub struct St {
    pub out: Vec<u8>,
    pub ring: [i64; 4],
    pub google: bool,
}

fn read_dist(h: &Hdr, ring: &[i64; 4], c: u64, clen: u64, b: &Bits, p: u64, bd: Blk) -> Option<(i64, bool, Blk, u64)> {
    if c < 128 {
        return Some((ring[0], false, bd, p));
    }
    let (bd2, q) = next_blk(&h.cd, bd, b, p)?;
    let (dc, q2) = dsym(&h.dist[h.cmapd[(4 * bd2.t + dist_ctx(clen)) as usize] as usize], b, q)?;
    if h.npostfix > 0 { hit(19) }
    if dc < 16 {
        hit(if dc == 0 { 16 } else { 17 });
        let d = short_dist(ring, dc);
        if d <= 0 { None } else { Some((d, dc != 0, bd2, q2)) }
    } else if dc < 16 + h.ndirect {
        hit(18);
        Some(((dc - 15) as i64, true, bd2, q2))
    } else {
        let nb = dist_nbits(h.npostfix, h.ndirect, dc);
        let e = b.getbits(q2, nb)?;
        Some((long_dist(h.npostfix, h.ndirect, dc, e) as i64, true, bd2, q2 + nb))
    }
}

/// `do_copy`, updating `st` in place; false where the spec has no result.
fn do_copy(dict: &[u8], window: u64, st: &mut St, d: i64, explicit: bool, clen: u64, end: u64) -> bool {
    let n = st.out.len() as u64;
    let maxd = if n < window { n as i64 } else { window as i64 };
    if d > maxd {
        let wid = (d - maxd - 1) as u64;
        if !(4..=24).contains(&clen) {
            return false;
        }
        let nw = 1u64 << vbrotli::tables::NDBITS[clen as usize];
        let tid = wid / nw;
        if tid > 120 {
            return false;
        }
        hit(20);
        if tid != 0 { hit(21) }
        let w = transform(tid, dict_word(dict, clen, wid % nw));
        if n + w.len() as u64 > end {
            return false;
        }
        st.google = st.google && !(w.is_empty() && d <= 120);
        st.out.extend(w);
        true
    } else if n + clen > end {
        false
    } else {
        for _ in 0..clen {
            let x = st.out[st.out.len() - d as usize];
            st.out.push(x);
        }
        if explicit {
            st.ring = [d, st.ring[0], st.ring[1], st.ring[2]];
        }
        true
    }
}

#[allow(clippy::too_many_arguments)]
fn commands(dict: &[u8], window: u64, h: &Hdr, b: &Bits, mut p: u64, end: u64, st: &mut St,
            mut bl: Blk, mut bi: Blk, mut bd: Blk) -> Option<u64> {
    loop {
        let (bi2, q) = next_blk(&h.ci, bi, b, p)?;
        let (c, q1) = dsym(&h.cmd[bi2.t as usize], b, q)?;
        let (ic, cc) = (ins_code(c) as usize, copy_code(c) as usize);
        let e1 = b.getbits(q1, INS_EXTRA[ic])?;
        let q2 = q1 + INS_EXTRA[ic];
        let e2 = b.getbits(q2, COPY_EXTRA[cc])?;
        let q3 = q2 + COPY_EXTRA[cc];
        let ilen = INS_BASE[ic] + e1;
        let clen = COPY_BASE[cc] + e2;
        let n0 = st.out.len() as u64;
        if n0 + ilen > end {
            return None;
        }
        let (bl2, q4) = lits(h, b, q3, ilen, &mut st.out, bl)?;
        if st.out.len() as u64 >= end {
            return Some(q4);
        }
        let (d, explicit, bd2, q5) = read_dist(h, &st.ring, c, clen, b, q4, bd)?;
        if !do_copy(dict, window, st, d, explicit, clen, end) {
            return None;
        }
        if st.out.len() as u64 >= end {
            return Some(q5);
        }
        let n2 = st.out.len() as u64;
        if !((n2 > n0) || (n2 == n0 && p < q5 && q5 <= b.len()) || (n2 == n0 && q5 == p && bi2.left < bi.left)) {
            return None; // not reached
        }
        p = q5;
        bl = bl2;
        bi = bi2;
        bd = bd2;
    }
}

// ------------------------------------------------------------ the stream

/// `metablock`: the position after it and whether it is the last.
fn metablock(dict: &[u8], window: u64, b: &Bits, p: u64, st: &mut St) -> Option<(u64, bool)> {
    let islast = b.getbits(p, 1)?;
    let e = if islast == 1 { b.getbits(p + 1, 1)? } else { 0 };
    if e == 1 {
        return Some((p + 2, true));
    }
    let q = if islast == 1 { p + 2 } else { p + 1 };
    let m = b.getbits(q, 2)?;
    if m == 3 {
        return metadata(b, q + 2, islast == 1);
    }
    let nib = m + 4;
    let v = b.getbits(q + 2, 4 * nib)?;
    if nib > 4 && v >> (4 * (nib - 1)) == 0 {
        return None;
    }
    data(dict, window, b, q + 2 + 4 * nib, st, v + 1, islast == 1)
}

fn metadata(b: &Bits, p: u64, last: bool) -> Option<(u64, bool)> {
    let reserved = b.getbits(p, 1)?;
    let nbytes = b.getbits(p + 1, 2)?;
    let n = if nbytes == 0 {
        0
    } else {
        let v = b.getbits(p + 3, 8 * nbytes)?;
        if nbytes > 1 && v >> (8 * (nbytes - 1)) == 0 {
            return None;
        }
        v + 1
    };
    let r = p + 3 + 8 * nbytes;
    hit(23);
    if reserved != 0 || !zero_fill(b, r) || align8(r) + 8 * n > b.len() {
        return None;
    }
    Some((align8(r) + 8 * n, last))
}

#[allow(clippy::too_many_arguments)]
fn data(dict: &[u8], window: u64, b: &Bits, p: u64, st: &mut St, mlen: u64, last: bool) -> Option<(u64, bool)> {
    let u = if last { 0 } else { b.getbits(p, 1)? };
    let r = if last { p } else { p + 1 };
    if u == 1 {
        if !zero_fill(b, r) || align8(r) + 8 * mlen > b.len() {
            return None;
        }
        hit(22);
        st.out.extend(bytes_at(b, align8(r), mlen));
        return Some((align8(r) + 8 * mlen, false));
    }
    let (h, r2) = read_hdr(b, r)?;
    let end = st.out.len() as u64 + mlen;
    let (bl, bi, bd) = (blk0(&h.cl), blk0(&h.ci), blk0(&h.cd));
    let r3 = commands(dict, window, &h, b, r2, end, st, bl, bi, bd)?;
    Some((r3, last))
}

fn metablocks(dict: &[u8], window: u64, b: &Bits, mut p: u64, st: &mut St) -> Option<u64> {
    loop {
        let (q, last) = metablock(dict, window, b, p, st)?;
        if last {
            return if zero_fill(b, q) { Some(align8(q)) } else { None };
        }
        if q <= p || q > b.len() {
            return None; // not reached
        }
        p = q;
    }
}

fn wbits(b: &Bits) -> Option<(u64, u64)> {
    if b.getbits(0, 1)? == 0 {
        return Some((16, 1));
    }
    let n = b.getbits(1, 3)?;
    if n != 0 {
        return Some((17 + n, 4));
    }
    let m = b.getbits(4, 3)?;
    if m == 1 {
        None
    } else if m != 0 {
        Some((8 + m, 7))
    } else {
        Some((17, 7))
    }
}

/// `brotli(dict, lbits(buf))`: the data, the bits the stream took, and
/// whether Google's decoder accepts it.
pub fn brotli(dict: &[u8], buf: &[u8]) -> Option<(Vec<u8>, u64, bool)> {
    let b = Bits { buf };
    let (w, p) = wbits(&b)?;
    let mut st = St { out: vec![], ring: [4, 11, 15, 16], google: true };
    let q = metablocks(dict, (1 << w) - 16, &b, p, &mut st)?;
    Some((st.out, q, st.google))
}
