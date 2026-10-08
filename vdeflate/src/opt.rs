//! Near-optimal parsing: the compressor's most thorough setting.
//!
//! The input is planned a window at a time. Every position's matches are
//! listed (the longest at each distance that beats all nearer ones, through
//! the hash chains), then the cheapest parse of the window under a bit-cost
//! model is found by a shortest-path search, backward over the window. The
//! model is the code lengths of the previous parse, re-estimated `passes`
//! times, as zopfli and libdeflate's level 12 do.
//!
//! None of that is proved, and none of it needs to be: each match the parse
//! chose is checked byte by byte when its token is made, and the tokens go
//! to `put_block`, which picks and checks the block's codes. So the round
//! trip is proved exactly as for `deflate_level`.
use vstd::prelude::*;
use vbits::lsb::*;
use crate::spec::*;
use crate::step::*;
use crate::inflate::*;
use crate::enc::*;
use crate::enc2::*;

verus! {

/// Match candidates kept per position.
pub const K: usize = 24;
/// The largest window.
pub const WMAX: usize = 131072;
/// Costs are capped here, so that sums of them cannot overflow.
pub const CAP: u64 = 0x100_0000_0000;

/// How hard to look.
#[derive(Clone, Copy)]
pub struct Opt {
    /// candidates tried per position
    pub chain: usize,
    /// a match this long ends the search, and the positions it covers are not
    /// searched (259: never)
    pub nice: usize,
    /// parses per window (each after the first with the previous one's code lengths)
    pub passes: usize,
    /// bytes per window
    pub win: usize,
    /// tokens per segment of the block split (0: blocks of 32768 tokens)
    pub seg: usize,
    /// the bits a block costs besides its symbols, in the split's estimate
    pub hbits: usize,
    /// parses of each block by its own statistics, after the split
    pub reopt: usize,
    /// steps along the three-byte chains for the nearest three-byte match
    pub steps3: usize,
    /// the cost models a window's parse starts from, as a bit set (the parse
    /// that codes smallest is kept): 1 the previous window's, 2 the fixed
    /// codes', 4 the fixed codes' with literals by the window's bytes
    pub tries: usize,
    /// match finding by binary trees (else hash chains); `chain` is then the depth
    pub bt: bool,
    /// rounds of moving each block end to where it costs least, exactly
    pub refine: usize,
    /// parses from the best model perturbed at random, and by how many bits
    pub rand: usize,
    pub amp: u32,
    /// cost models by entropy (zopfli's), else by Huffman code lengths
    pub frac: bool,
}

pub open spec fn opt_ok(o: Opt) -> bool {
    o.chain <= 65536 && 3 <= o.nice <= 259 && 1 <= o.passes <= 16 && 1 <= o.win <= WMAX
        && o.seg <= 32768 && o.hbits <= 100000 && o.reopt <= 8 && o.steps3 <= 4096 && o.refine <= 8 && o.rand <= 64 && o.amp <= 16
}

/// Segments of a window, at most.
pub const MS: usize = 4098;

/// The settings measured best (README): binary trees 128 deep, 3 passes from
/// two starting models and two random restarts, each plan scored whole, 128K
/// windows, blocks split at 512-token segments and refined by exact costs.
pub fn opt_max() -> (o: Opt)
    ensures opt_ok(o),
{
    Opt { chain: 128, nice: 258, passes: 3, win: WMAX, seg: 512, hbits: 120, reopt: 1, steps3: 16, tries: 3, bt: true,
          refine: 1, rand: 2, amp: 2, frac: false }
}

/// The planner's state: the hash chains, the current window's candidates and
/// parse, and the cost model.
pub struct Planner {
    pub ch: Box<Chains>,
    pub tabs: SymTabs,
    /// the positions below this are in the chains
    pub ins: usize,
    /// the window planned, `[s, e)`, and how far its parse has been taken
    pub s: usize,
    pub e: usize,
    pub cur: usize,
    /// candidates at window position `q`: `mc[q]` of them, at `ml`/`md[q * K ..]`
    pub mc: Vec<u8>,
    pub ml: Vec<u16>,
    pub md: Vec<u16>,
    /// the parse: the cheapest cost from each position to the window's end, and
    /// the length (0: a literal) and distance chosen there
    pub cost: Vec<u64>,
    pub cl: Vec<u16>,
    pub cd: Vec<u16>,
    /// bits per literal, per match length (with extra bits), per distance symbol
    pub litc: Vec<u32>,
    pub lenc: Vec<u32>,
    pub dsc: Vec<u32>,
    /// `x log2 x` in 1/256 bits, for counts up to `WMAX`
    pub lg: Vec<u64>,
    /// the window's blocks: where each ends (window offsets), how many, the next
    pub bnd: Vec<u32>,
    pub nb: usize,
    pub bi: usize,
    /// chains of three-byte hashes (a larger table than `ch`'s, walked a few steps)
    pub h3: Vec<u32>,
    pub p3: Vec<u32>,
    /// binary trees of the positions with each four-byte hash, sorted by what
    /// follows them (libdeflate's `bt_matchfinder`): roots, and two children a position
    pub bth: Vec<u32>,
    pub btc: Vec<u32>,
}

impl Planner {
    pub open spec fn wf(&self) -> bool {
        &&& tabs_wf(&self.tabs)
        &&& self.mc@.len() == WMAX && self.ml@.len() == WMAX * K && self.md@.len() == WMAX * K
        &&& self.cost@.len() == WMAX + 1 && self.cl@.len() == WMAX && self.cd@.len() == WMAX
        &&& self.litc@.len() == 256 && self.lenc@.len() == 259 && self.dsc@.len() == 30
        &&& forall|j: int| 0 <= j < 256 ==> #[trigger] self.litc@[j] <= 1024
        &&& forall|j: int| 0 <= j < 259 ==> #[trigger] self.lenc@[j] <= 1024
        &&& forall|j: int| 0 <= j < 30 ==> #[trigger] self.dsc@[j] <= 1024
        &&& forall|j: int| 0 <= j <= WMAX ==> #[trigger] self.cost@[j] <= CAP
        &&& self.lg@.len() == WMAX + 1 && forall|j: int| 0 <= j <= WMAX ==> #[trigger] self.lg@[j] <= 0x4000_0000
        &&& self.bnd@.len() == MS && self.nb <= MS
        &&& self.h3@.len() == 65536 && self.p3@.len() == 32768
        &&& self.bth@.len() == 65536 && self.btc@.len() == 65536
    }
}

pub fn planner_new() -> (p: Planner)
    ensures p.wf(),
{
    let mut p = Planner {
        ch: chains_new(), tabs: sym_tabs(), ins: 0, s: 0, e: 0, cur: 0,
        mc: vec![0u8; WMAX], ml: vec![0u16; WMAX * K], md: vec![0u16; WMAX * K],
        cost: vec![0u64; WMAX + 1], cl: vec![0u16; WMAX], cd: vec![0u16; WMAX],
        litc: vec![0u32; 256], lenc: vec![0u32; 259], dsc: vec![0u32; 30],
        lg: lg_table(), bnd: vec![0u32; MS], nb: 0, bi: 0, h3: vec![0u32; 65536], p3: vec![0u32; 32768],
        bth: vec![0u32; 65536], btc: vec![0u32; 65536],
    };
    costs_fixed(&mut p);
    p
}

// ---------------------------------------------------------------- costs

/// `log2 x` in 1/65536 bits (by repeated squaring).
fn log2_fp(x: u64) -> (r: u64)
    requires 1 <= x <= WMAX,
    ensures r < 18 * 65536,
{
    let mut k: u64 = 0;
    while k < 17 && (x >> (k + 1)) != 0
        invariant k <= 17,
        decreases 17 - k,
    {
        k = k + 1;
    }
    // `x / 2^k` in [1, 2), with 30 fractional bits
    let mut y: u64 = x << (30 - k);
    if y >= 0x8000_0000 {
        y = 0x7fff_ffff;
    }
    let mut r: u64 = k * 65536;
    let mut b: u64 = 0;
    while b < 16
        invariant b <= 16, y < 0x8000_0000, k <= 17, r <= k * 65536 + 65535,
        decreases 16 - b,
    {
        assert(y * y < 0x4000_0000_0000_0000) by (nonlinear_arith) requires y < 0x8000_0000;
        y = (y * y) >> 30;
        if y >= 0x8000_0000 {
            y = y >> 1;
            let inc: u64 = 0x8000u64 >> b;
            assert(inc <= 0x8000) by (bit_vector) requires inc == 0x8000u64 >> b;
            if r + inc <= k * 65536 + 65535 {
                r = r + inc;
            }
        }
        if y >= 0x8000_0000 {
            y = 0x7fff_ffff;
        }
        b = b + 1;
    }
    r
}

/// `x log2 x` in 1/256 bits, for `x` up to `WMAX`.
fn lg_table() -> (t: Vec<u64>)
    ensures t@.len() == WMAX + 1, forall|j: int| 0 <= j <= WMAX ==> #[trigger] t@[j] <= 0x4000_0000,
{
    let mut t: Vec<u64> = vec![0u64; WMAX + 1];
    let mut x: usize = 1;
    while x <= WMAX
        invariant 1 <= x <= WMAX + 1, t@.len() == WMAX + 1,
            forall|j: int| 0 <= j <= WMAX ==> #[trigger] t@[j] <= 0x4000_0000,
        decreases WMAX + 1 - x,
    {
        let l = log2_fp(x as u64);
        assert((x as u64) * l < 0x40_0000_0000) by (nonlinear_arith) requires x <= WMAX, l < 18 * 65536;
        t.set(x, (x as u64) * l / 256);
        x = x + 1;
    }
    t
}

/// The cost model of the fixed codes: a first guess.
fn costs_fixed(p: &mut Planner)
    requires old(p).litc@.len() == 256, old(p).lenc@.len() == 259, old(p).dsc@.len() == 30, tabs_wf(&old(p).tabs),
    ensures
        final(p).litc@.len() == 256, final(p).lenc@.len() == 259, final(p).dsc@.len() == 30,
        forall|j: int| 0 <= j < 256 ==> #[trigger] final(p).litc@[j] <= 1024,
        forall|j: int| 0 <= j < 259 ==> #[trigger] final(p).lenc@[j] <= 1024,
        forall|j: int| 0 <= j < 30 ==> #[trigger] final(p).dsc@[j] <= 1024,
        final(p).tabs == old(p).tabs, final(p).ch == old(p).ch, final(p).ins == old(p).ins,
        final(p).s == old(p).s, final(p).e == old(p).e, final(p).cur == old(p).cur,
        final(p).mc == old(p).mc, final(p).ml == old(p).ml, final(p).md == old(p).md,
        final(p).cost == old(p).cost, final(p).cl == old(p).cl, final(p).cd == old(p).cd,
        final(p).lg == old(p).lg, final(p).bnd == old(p).bnd, final(p).nb == old(p).nb, final(p).bi == old(p).bi, final(p).h3 == old(p).h3, final(p).p3 == old(p).p3, final(p).bth == old(p).bth, final(p).btc == old(p).btc,
{
    let mut lit: Vec<u8> = vec![8u8; 286];
    let mut j: usize = 144;
    while j < 256
        invariant 144 <= j <= 256, lit@.len() == 286,
            forall|t: int| 0 <= t < 286 ==> #[trigger] lit@[t] <= 15,
        decreases 256 - j,
    {
        lit.set(j, 9);
        j = j + 1;
    }
    let mut j: usize = 256;
    while j < 280
        invariant 256 <= j <= 280, lit@.len() == 286,
            forall|t: int| 0 <= t < 286 ==> #[trigger] lit@[t] <= 15,
        decreases 280 - j,
    {
        lit.set(j, 7);
        j = j + 1;
    }
    let dist: Vec<u8> = vec![5u8; 30];
    costs_from(p, &lit, &dist);
}

/// The cost model of code lengths `lit` and `dist` (an unused symbol costs 15 bits).
fn costs_from(p: &mut Planner, lit: &Vec<u8>, dist: &Vec<u8>)
    requires
        old(p).litc@.len() == 256, old(p).lenc@.len() == 259, old(p).dsc@.len() == 30, tabs_wf(&old(p).tabs),
        lit@.len() == 286, dist@.len() == 30,
        forall|t: int| 0 <= t < 286 ==> #[trigger] lit@[t] <= 15,
        forall|t: int| 0 <= t < 30 ==> #[trigger] dist@[t] <= 15,
    ensures
        final(p).litc@.len() == 256, final(p).lenc@.len() == 259, final(p).dsc@.len() == 30,
        forall|j: int| 0 <= j < 256 ==> #[trigger] final(p).litc@[j] <= 1024,
        forall|j: int| 0 <= j < 259 ==> #[trigger] final(p).lenc@[j] <= 1024,
        forall|j: int| 0 <= j < 30 ==> #[trigger] final(p).dsc@[j] <= 1024,
        final(p).tabs == old(p).tabs, final(p).ch == old(p).ch, final(p).ins == old(p).ins,
        final(p).s == old(p).s, final(p).e == old(p).e, final(p).cur == old(p).cur,
        final(p).mc == old(p).mc, final(p).ml == old(p).ml, final(p).md == old(p).md,
        final(p).cost == old(p).cost, final(p).cl == old(p).cl, final(p).cd == old(p).cd,
        final(p).lg == old(p).lg, final(p).bnd == old(p).bnd, final(p).nb == old(p).nb, final(p).bi == old(p).bi, final(p).h3 == old(p).h3, final(p).p3 == old(p).p3, final(p).bth == old(p).bth, final(p).btc == old(p).btc,
{
    let mut j: usize = 0;
    while j < 256
        invariant j <= 256, p.litc@.len() == 256, lit@.len() == 286,
            forall|t: int| 0 <= t < 286 ==> #[trigger] lit@[t] <= 15,
            forall|t: int| 0 <= t < j ==> #[trigger] p.litc@[t] <= 1024,
            p.tabs == old(p).tabs, p.ch == old(p).ch, p.ins == old(p).ins, p.s == old(p).s, p.e == old(p).e,
            p.cur == old(p).cur, p.mc == old(p).mc, p.ml == old(p).ml, p.md == old(p).md,
            p.cost == old(p).cost, p.cl == old(p).cl, p.cd == old(p).cd, p.lg == old(p).lg, p.bnd == old(p).bnd, p.nb == old(p).nb, p.bi == old(p).bi, p.h3 == old(p).h3, p.p3 == old(p).p3, p.bth == old(p).bth, p.btc == old(p).btc, p.lenc == old(p).lenc, p.dsc == old(p).dsc,
        decreases 256 - j,
    {
        let b = lit[j];
        p.litc.set(j, 16 * if b == 0 { 15 } else { b as u32 });
        j = j + 1;
    }
    let mut l: usize = 0;
    while l < 259
        invariant l <= 259, p.lenc@.len() == 259, lit@.len() == 286, tabs_wf(&p.tabs),
            forall|t: int| 0 <= t < 286 ==> #[trigger] lit@[t] <= 15,
            forall|t: int| 0 <= t < l ==> #[trigger] p.lenc@[t] <= 1024,
            forall|t: int| 0 <= t < 256 ==> #[trigger] p.litc@[t] <= 1024, p.litc@.len() == 256,
            p.tabs == old(p).tabs, p.ch == old(p).ch, p.ins == old(p).ins, p.s == old(p).s, p.e == old(p).e,
            p.cur == old(p).cur, p.mc == old(p).mc, p.ml == old(p).ml, p.md == old(p).md,
            p.cost == old(p).cost, p.cl == old(p).cl, p.cd == old(p).cd, p.lg == old(p).lg, p.bnd == old(p).bnd, p.nb == old(p).nb, p.bi == old(p).bi, p.h3 == old(p).h3, p.p3 == old(p).p3, p.bth == old(p).bth, p.btc == old(p).btc, p.dsc == old(p).dsc,
        decreases 259 - l,
    {
        let mut c: u32 = 1024;
        if l >= 3 {
            match len_code_t(&p.tabs, l as u64) {
                Some((s, _, x)) => {
                    let b = lit[s as usize];
                    c = 16 * ((if b == 0 { 15 } else { b as u32 }) + x as u32);
                }
                None => {}
            }
        }
        p.lenc.set(l, c);
        l = l + 1;
    }
    let mut s: usize = 0;
    while s < 30
        invariant s <= 30, p.dsc@.len() == 30, dist@.len() == 30,
            forall|t: int| 0 <= t < 30 ==> #[trigger] dist@[t] <= 15,
            forall|t: int| 0 <= t < s ==> #[trigger] p.dsc@[t] <= 1024,
            forall|t: int| 0 <= t < 259 ==> #[trigger] p.lenc@[t] <= 1024, p.lenc@.len() == 259,
            forall|t: int| 0 <= t < 256 ==> #[trigger] p.litc@[t] <= 1024, p.litc@.len() == 256,
            p.tabs == old(p).tabs, p.ch == old(p).ch, p.ins == old(p).ins, p.s == old(p).s, p.e == old(p).e,
            p.cur == old(p).cur, p.mc == old(p).mc, p.ml == old(p).ml, p.md == old(p).md,
            p.cost == old(p).cost, p.cl == old(p).cl, p.cd == old(p).cd, p.lg == old(p).lg, p.bnd == old(p).bnd, p.nb == old(p).nb, p.bi == old(p).bi, p.h3 == old(p).h3, p.p3 == old(p).p3, p.bth == old(p).bth, p.btc == old(p).btc,
        decreases 30 - s,
    {
        let b = dist[s];
        p.dsc.set(s, 16 * if b == 0 { 15 } else { b as u32 });
        s = s + 1;
    }
}

/// The cost of distance `d`: its symbol's bits and its extra bits.
#[inline(always)]
fn dist_cost(p: &Planner, d: usize) -> (c: u64)
    requires p.wf(),
    ensures c <= 2048,
{
    if 1 <= d && d <= 32768 {
        match dist_code_t(&p.tabs, d as u64) {
            Some((s, _, x)) => p.dsc[s as usize] as u64 + 16 * x,
            None => 2048,
        }
    } else {
        2048
    }
}

// ---------------------------------------------------------------- matches

/// Put position `i` into the chains; the chains' entries for it before: the
/// last position with its hash, and with its three-byte hash.
#[inline(always)]
fn insert(data: &[u8], ch: &mut Chains, i: usize) -> (r: (usize, usize))
    requires i + 3 <= data.len(), data.len() < 0x1000_0000,
{
    let h = hash4(data, i);
    let g = hash3(data, i);
    let c3 = ch.head3[g] as usize;
    ch.head3[g] = (i + 1) as u32;
    let pi = i & 0x7fff;
    assert(pi < 32768) by (bit_vector) requires pi == i & 0x7fff;
    let first = ch.head[h] as usize;
    ch.prev[pi] = ch.head[h];
    ch.head[h] = (i + 1) as u32;
    (first, c3)
}

/// Put position `i` into the three-byte chains, and find the nearest earlier
/// position whose three bytes match (plus 1; 0: none in `steps` steps).
#[inline(always)]
fn insert3(data: &[u8], h3: &mut Vec<u32>, p3: &mut Vec<u32>, i: usize, steps: usize) -> (c: usize)
    requires i + 3 <= data.len(), data.len() < 0x1000_0000, old(h3)@.len() == 65536, old(p3)@.len() == 32768,
    ensures final(h3)@.len() == 65536, final(p3)@.len() == 32768,
{
    let x: u32 = (data[i] as u32) | ((data[i + 1] as u32) << 8u32) | ((data[i + 2] as u32) << 16u32);
    let hx = (x as u64 * 0x9E3779B1u64) >> 16u64;
    let h = (hx & 0xffff) as usize;
    assert(hx & 0xffff < 65536) by (bit_vector);
    let first = h3[h] as usize;
    let pi = i & 0x7fff;
    assert(pi < 32768) by (bit_vector) requires pi == i & 0x7fff;
    p3.set(pi, h3[h]);
    h3.set(h, (i + 1) as u32);
    let mut cand = first;
    let mut k: usize = 0;
    while k < steps && cand != 0 && cand <= i && i + 1 - cand <= 32768
        invariant i + 3 <= data.len(), h3@.len() == 65536, p3@.len() == 32768,
        decreases steps - k,
    {
        let d = i + 1 - cand;
        if data[i] == data[i - d] && data[i + 1] == data[i + 1 - d] && data[i + 2] == data[i + 2 - d] {
            return cand;
        }
        let cm = cand - 1;
        let ci = cm & 0x7fff;
        assert(ci < 32768) by (bit_vector) requires ci == cm & 0x7fff;
        let nxt = p3[ci] as usize;
        if nxt >= cand {
            return 0;
        }
        cand = nxt;
        k = k + 1;
    }
    0
}

/// Put position `i` into the binary trees, and (if `record`) its candidates
/// into `ml`/`md` from `base`, as `find` does: each longer than all before it.
/// `c3` is the nearest three-byte match (plus 1), tried first.
fn bt_find(data: &[u8], i: usize, bth: &mut Vec<u32>, btc: &mut Vec<u32>, depth: usize, nice: usize,
           record: bool, c3: usize, ml: &mut Vec<u16>, md: &mut Vec<u16>, base: usize) -> (r: (usize, usize))
    requires i + 3 <= data.len(), data.len() < 0x1000_0000, old(bth)@.len() == 65536, old(btc)@.len() == 65536,
        base + K <= old(ml)@.len(), old(ml)@.len() == old(md)@.len(), base < 0x1_0000_0000,
        depth <= 65536, nice <= 259,
    ensures r.0 <= K, r.1 <= 258, final(ml)@.len() == old(ml)@.len(), final(md)@.len() == old(md)@.len(),
        final(bth)@.len() == 65536, final(btc)@.len() == 65536,
{
    let n = data.len();
    let max: usize = if n - i < 258 { n - i } else { 258 };
    let mut cnt: usize = 0;
    let mut best: usize = 2;
    if record && c3 != 0 && c3 <= i && i + 1 - c3 <= 32768 {
        let d = i + 1 - c3;
        let m = match_len(data, i, d, max);
        if m >= 3 {
            ml.set(base, m as u16);
            md.set(base, d as u16);
            cnt = 1;
            best = m;
        }
    }
    let x: u32 = if n - i >= 4 {
        (data[i] as u32) | ((data[i + 1] as u32) << 8u32) | ((data[i + 2] as u32) << 16u32) | ((data[i + 3] as u32) << 24u32)
    } else {
        (data[i] as u32) | ((data[i + 1] as u32) << 8u32) | ((data[i + 2] as u32) << 16u32)
    };
    let hx = (x as u64 * 2654435761u64) >> 16u64;
    let h = (hx & 0xffff) as usize;
    assert(hx & 0xffff < 65536) by (bit_vector);
    let mut cand = bth[h] as usize;
    bth.set(h, (i + 1) as u32);
    let ii = i & 0x7fff;
    assert(ii < 32768) by (bit_vector) requires ii == i & 0x7fff;
    // the slots to link the next smaller and larger node into
    let mut plt: usize = 2 * ii;
    let mut pgt: usize = 2 * ii + 1;
    // what the current position shares with everything below each side
    let mut blt: usize = 0;
    let mut bgt: usize = 0;
    let mut len: usize = 0;
    let mut dep: usize = depth;
    loop
        invariant plt < 65536, pgt < 65536, btc@.len() == 65536, bth@.len() == 65536, len <= max,
            blt <= max, bgt <= max, max <= 258, i + max <= n, n == data.len(),
            i + 3 <= n, cnt <= K, 2 <= best <= 258, base + K <= ml@.len(), ml@.len() == md@.len(),
            ml@.len() == old(ml)@.len(), md@.len() == old(md)@.len(), base < 0x1_0000_0000, max >= 3,
        decreases dep,
    {
        if cand == 0 || cand > i || i + 1 - cand > 32768 || dep == 0 {
            btc.set(plt, 0);
            btc.set(pgt, 0);
            break;
        }
        let d = i + 1 - cand;
        let mut m = len;
        while m < max && data[i + m] == data[i + m - d]
            invariant m <= max, i + max <= data.len(), 1 <= d <= i,
            decreases max - m,
        {
            m = m + 1;
        }
        len = m;
        if record && len > best {
            if cnt < K {
                ml.set(base + cnt, len as u16);
                md.set(base + cnt, d as u16);
                cnt = cnt + 1;
            } else {
                ml.set(base + K - 1, len as u16);
                md.set(base + K - 1, d as u16);
            }
            best = len;
        }
        let cm = cand - 1;
        let ci = cm & 0x7fff;
        assert(ci < 32768) by (bit_vector) requires ci == cm & 0x7fff;
        let node = 2 * ci;
        if len >= max || len >= nice {
            // the same as far as can be told: the new node takes its place
            let a = btc[node];
            let b = btc[node + 1];
            btc.set(plt, a);
            btc.set(pgt, b);
            break;
        }
        if data[i + len - d] < data[i + len] {
            btc.set(plt, cand as u32);
            plt = node + 1;
            cand = btc[plt] as usize;
            blt = len;
        } else {
            btc.set(pgt, cand as u32);
            pgt = node;
            cand = btc[pgt] as usize;
            bgt = len;
        }
        len = if blt < bgt { blt } else { bgt };
        dep = dep - 1;
    }
    (cnt, if cnt == 0 { 0 } else { best })
}

/// The length of the match at `i` with distance `d`, up to `max`.
#[inline(always)]
fn match_len(data: &[u8], i: usize, d: usize, max: usize) -> (m: usize)
    requires 1 <= d <= i, i + max <= data.len(),
    ensures m <= max,
{
    let mut m: usize = 0;
    while m < max && data[i + m] == data[i + m - d]
        invariant m <= max, i + max <= data.len(), 1 <= d <= i,
        decreases max - m,
    {
        m = m + 1;
    }
    m
}

/// The candidates at `i`, into `ml`/`md` from `base`: each the first (nearest)
/// to be longer than all before it, so lengths and distances increase. Their
/// count, and the longest length.
fn find(data: &[u8], i: usize, first: usize, c3: usize, prev: &[u32; 32768], chain: usize, nice: usize,
        ml: &mut Vec<u16>, md: &mut Vec<u16>, base: usize) -> (r: (usize, usize))
    requires i < data.len(), data.len() < 0x1000_0000, base + K <= old(ml)@.len(), old(ml)@.len() == old(md)@.len(),
        base < 0x1_0000_0000,
        chain <= 65536, nice <= 259,
    ensures r.0 <= K, r.1 <= 258, final(ml)@.len() == old(ml)@.len(), final(md)@.len() == old(md)@.len(),
{
    let n = data.len();
    let max: usize = if n - i < 258 { n - i } else { 258 };
    let mut cnt: usize = 0;
    let mut best: usize = 2;
    // the nearest three-byte match, which four-byte chains miss
    if c3 != 0 && c3 <= i && i + 1 - c3 <= 32768 {
        let d = i + 1 - c3;
        let m = match_len(data, i, d, max);
        if m >= 3 {
            ml.set(base, m as u16);
            md.set(base, d as u16);
            cnt = 1;
            best = m;
        }
    }
    let mut cand = first;
    let mut depth: usize = 0;
    while depth < chain && cand != 0 && cand <= i && i + 1 - cand <= 32768 && best < max && best < nice
        invariant
            i < n, n == data.len(), cnt <= K, 2 <= best <= 258, best <= max || cnt == 0, max <= 258, i + max <= n,
            base + K <= ml@.len(), ml@.len() == md@.len(), ml@.len() == old(ml)@.len(), base < 0x1_0000_0000,
            md@.len() == old(md)@.len(),
        decreases chain - depth,
    {
        let d = i + 1 - cand;
        // only a candidate that matches at the length to beat can beat it
        if best < max && data[i + best] == data[i + best - d] {
            let m = match_len(data, i, d, max);
            if m > best {
                if cnt < K {
                    ml.set(base + cnt, m as u16);
                    md.set(base + cnt, d as u16);
                    cnt = cnt + 1;
                } else {
                    ml.set(base + K - 1, m as u16);
                    md.set(base + K - 1, d as u16);
                }
                best = m;
            }
        }
        let cm = cand - 1;
        let ci = cm & 0x7fff;
        assert(ci < 32768) by (bit_vector) requires ci == cm & 0x7fff;
        let nxt = prev[ci] as usize;
        if nxt >= cand {
            break;
        }
        cand = nxt;
        depth = depth + 1;
    }
    (cnt, if cnt == 0 { 0 } else { best })
}

// ---------------------------------------------------------------- the parse

/// The cheapest parse of `[s, e)` under the cost model, into `cost`, `cl`, `cd`.
fn dp(data: &[u8], p: &mut Planner, s: usize, a: usize, e: usize)
    requires old(p).wf(), s < e <= data.len(), e - s <= WMAX, a < e - s,
    ensures final(p).wf(), final(p).ch == old(p).ch, final(p).tabs == old(p).tabs, final(p).ins == old(p).ins,
        final(p).lg == old(p).lg, final(p).bnd == old(p).bnd, final(p).nb == old(p).nb, final(p).bi == old(p).bi, final(p).h3 == old(p).h3, final(p).p3 == old(p).p3, final(p).bth == old(p).bth, final(p).btc == old(p).btc,
        final(p).mc == old(p).mc, final(p).ml == old(p).ml, final(p).md == old(p).md,
        final(p).litc == old(p).litc, final(p).lenc == old(p).lenc, final(p).dsc == old(p).dsc,
        final(p).s == old(p).s, final(p).e == old(p).e, final(p).cur == old(p).cur,
{
    let w = e - s;
    p.cost.set(w, 0);
    let mut q: usize = w;
    while q > a
        invariant
            p.wf(), a <= q <= w, w == e - s, s < e <= data.len(), w <= WMAX, p.lg == old(p).lg, p.bnd == old(p).bnd, p.nb == old(p).nb, p.bi == old(p).bi, p.h3 == old(p).h3, p.p3 == old(p).p3, p.bth == old(p).bth, p.btc == old(p).btc,
            p.ch == old(p).ch, p.tabs == old(p).tabs, p.ins == old(p).ins,
            p.mc == old(p).mc, p.ml == old(p).ml, p.md == old(p).md,
            p.litc == old(p).litc, p.lenc == old(p).lenc, p.dsc == old(p).dsc,
            p.s == old(p).s, p.e == old(p).e, p.cur == old(p).cur,
        decreases q,
    {
        q = q - 1;
        let lit = data[s + q] as usize;
        let mut best: u64 = p.litc[lit] as u64 + p.cost[q + 1];
        let mut bl: u16 = 0;
        let mut bd: u16 = 0;
        let cnt = p.mc[q] as usize;
        let mut k: usize = 0;
        let mut done: usize = 2;
        let room = w - q;
        while k < cnt && k < K
            invariant
                p.wf(), q < w, w <= WMAX, room == w - q, k <= K, best <= CAP + 4096, 2 <= done <= 258, p.lg == old(p).lg, p.bnd == old(p).bnd, p.nb == old(p).nb, p.bi == old(p).bi, p.h3 == old(p).h3, p.p3 == old(p).p3, p.bth == old(p).bth, p.btc == old(p).btc,
                p.ch == old(p).ch, p.tabs == old(p).tabs, p.ins == old(p).ins,
                p.mc == old(p).mc, p.ml == old(p).ml, p.md == old(p).md,
                p.litc == old(p).litc, p.lenc == old(p).lenc, p.dsc == old(p).dsc,
                p.s == old(p).s, p.e == old(p).e, p.cur == old(p).cur,
            decreases K - k,
        {
            let ml = p.ml[q * K + k] as usize;
            let d16 = p.md[q * K + k];
            let d = d16 as usize;
            let dc = dist_cost(p, d);
            let top = if ml > room { room } else { ml };
            let top = if top > 258 { 258 } else { top };
            let mut l = done + 1;
            while l <= top
                invariant
                    p.wf(), q < w, w <= WMAX, room == w - q, top <= room, top <= 258, best <= CAP + 4096, dc <= 2048,
                    3 <= l, p.cost@.len() == WMAX + 1,
                decreases top + 1 - l,
            {
                let c = p.lenc[l] as u64 + dc + p.cost[q + l];
                if c < best {
                    best = c;
                    bl = l as u16;
                    bd = d16;
                }
                l = l + 1;
            }
            if top > done {
                done = top;
            }
            k = k + 1;
        }
        p.cost.set(q, if best > CAP { CAP } else { best });
        p.cl.set(q, bl);
        p.cd.set(q, bd);
    }
}

/// The symbol counts of the parse of `[s, e)`.
fn stats(data: &[u8], p: &Planner, s: usize, a: usize, e: usize) -> (r: (Vec<u32>, Vec<u32>))
    requires p.wf(), s < e <= data.len(), e - s <= WMAX, a < e - s,
    ensures r.0@.len() == 286, r.1@.len() == 30,
{
    let w = e - s;
    let mut lf: Vec<u32> = vec![0u32; 286];
    let mut df: Vec<u32> = vec![0u32; 30];
    let mut q: usize = a;
    while q < w
        invariant q <= w + 258, w == e - s, w <= WMAX, p.wf(), s < e <= data.len(), lf@.len() == 286, df@.len() == 30,
            forall|t: int| 0 <= t < 286 ==> #[trigger] lf@[t] <= q,
            forall|t: int| 0 <= t < 30 ==> #[trigger] df@[t] <= q,
        decreases w + 258 - q,
    {
        let l = p.cl[q] as usize;
        if l < 3 || l > 258 {
            let x = data[s + q] as usize;
            lf.set(x, lf[x] + 1);
            q = q + 1;
        } else {
            let d = p.cd[q] as u64;
            let d = if d == 0 || d > 32768 { 1 } else { d };
            match (len_code_t(&p.tabs, l as u64), dist_code_t(&p.tabs, d)) {
                (Some((ls, _, _)), Some((ds, _, _))) => {
                    lf.set(ls as usize, lf[ls as usize] + 1);
                    df.set(ds as usize, df[ds as usize] + 1);
                }
                _ => {}
            }
            q = q + l;
        }
    }
    lf.set(256, 1);
    (lf, df)
}

/// `log2 x` in 1/65536 bits, for any `x >= 1` (the low bits dropped above `WMAX`).
fn log2_big(x: u64) -> (r: u64)
    requires x >= 1,
    ensures r < 82 * 65536,
{
    let mut y = x;
    let mut sh: u64 = 0;
    while y > WMAX as u64
        invariant y >= 1, sh <= 64,
        decreases y,
    {
        y = y / 2;
        sh = if sh < 64 { sh + 1 } else { 64 };
    }
    log2_fp(y) + sh * 65536
}

/// The entropy cost model of the counts `lf`, `df` (each count made a little
/// larger): `-log2(f / total)` per symbol, in 1/16 bits, as zopfli's.
fn refit_frac(p: &mut Planner, lf: &Vec<u32>, df: &Vec<u32>)
    requires old(p).wf(), lf@.len() == 286, df@.len() == 30,
    ensures final(p).wf(), final(p).ch == old(p).ch, final(p).tabs == old(p).tabs, final(p).ins == old(p).ins,
        final(p).s == old(p).s, final(p).e == old(p).e, final(p).cur == old(p).cur,
        final(p).mc == old(p).mc, final(p).ml == old(p).ml, final(p).md == old(p).md,
        final(p).cost == old(p).cost, final(p).cl == old(p).cl, final(p).cd == old(p).cd,
        final(p).lg == old(p).lg, final(p).bnd == old(p).bnd, final(p).nb == old(p).nb, final(p).bi == old(p).bi, final(p).h3 == old(p).h3, final(p).p3 == old(p).p3, final(p).bth == old(p).bth, final(p).btc == old(p).btc,
{
    let mut lit: Vec<u32> = vec![0u32; 286];
    let mut tl: u64 = 0;
    let mut t: usize = 0;
    while t < 286
        invariant t <= 286, lf@.len() == 286, tl <= t * 0x4000_0000,
        decreases 286 - t,
    {
        tl = tl + (if lf[t] < 0x1000_0000 { lf[t] as u64 } else { 0x1000_0000 }) + 1;
        t = t + 1;
    }
    let mut td: u64 = 0;
    let mut t: usize = 0;
    while t < 30
        invariant t <= 30, df@.len() == 30, td <= t * 0x4000_0000,
        decreases 30 - t,
    {
        td = td + (if df[t] < 0x1000_0000 { df[t] as u64 } else { 0x1000_0000 }) + 1;
        t = t + 1;
    }
    let ll = log2_big(tl + 1);
    let ld = log2_big(td + 1);
    let mut t: usize = 0;
    while t < 286
        invariant t <= 286, lf@.len() == 286, lit@.len() == 286, forall|j: int| 0 <= j < 286 ==> #[trigger] lit@[j] <= 1024,
        decreases 286 - t,
    {
        let f = (if lf[t] < 0x1000_0000 { lf[t] as u64 } else { 0x1000_0000 }) + 1;
        let lfv = log2_big(f);
        let c = if ll > lfv { (ll - lfv) / 4096 } else { 0 };
        lit.set(t, if c < 16 { 16 } else if c > 1024 { 1024 } else { c as u32 });
        t = t + 1;
    }
    let mut j: usize = 0;
    while j < 256
        invariant j <= 256, p.litc@.len() == 256, lit@.len() == 286,
            forall|t: int| 0 <= t < 286 ==> #[trigger] lit@[t] <= 1024,
            forall|t: int| 0 <= t < j ==> #[trigger] p.litc@[t] <= 1024,
            p.lenc@.len() == 259, p.dsc@.len() == 30, tabs_wf(&p.tabs),
            forall|t: int| 0 <= t < 259 ==> #[trigger] p.lenc@[t] <= 1024,
            forall|t: int| 0 <= t < 30 ==> #[trigger] p.dsc@[t] <= 1024,
            p.tabs == old(p).tabs, p.ch == old(p).ch, p.ins == old(p).ins, p.s == old(p).s, p.e == old(p).e,
            p.cur == old(p).cur, p.mc == old(p).mc, p.ml == old(p).ml, p.md == old(p).md,
            p.cost == old(p).cost, p.cl == old(p).cl, p.cd == old(p).cd, p.lg == old(p).lg, p.bnd == old(p).bnd, p.nb == old(p).nb, p.bi == old(p).bi, p.h3 == old(p).h3, p.p3 == old(p).p3, p.bth == old(p).bth, p.btc == old(p).btc,
            old(p).wf(),
        decreases 256 - j,
    {
        p.litc.set(j, lit[j]);
        j = j + 1;
    }
    let mut l: usize = 0;
    while l < 259
        invariant l <= 259, p.lenc@.len() == 259, lit@.len() == 286, tabs_wf(&p.tabs), p.litc@.len() == 256, p.dsc@.len() == 30,
            forall|t: int| 0 <= t < 286 ==> #[trigger] lit@[t] <= 1024,
            forall|t: int| 0 <= t < l ==> #[trigger] p.lenc@[t] <= 1024,
            forall|t: int| l <= t < 259 ==> #[trigger] p.lenc@[t] <= 1024,
            forall|t: int| 0 <= t < 256 ==> #[trigger] p.litc@[t] <= 1024,
            forall|t: int| 0 <= t < 30 ==> #[trigger] p.dsc@[t] <= 1024,
            p.tabs == old(p).tabs, p.ch == old(p).ch, p.ins == old(p).ins, p.s == old(p).s, p.e == old(p).e,
            p.cur == old(p).cur, p.mc == old(p).mc, p.ml == old(p).ml, p.md == old(p).md,
            p.cost == old(p).cost, p.cl == old(p).cl, p.cd == old(p).cd, p.lg == old(p).lg, p.bnd == old(p).bnd, p.nb == old(p).nb, p.bi == old(p).bi, p.h3 == old(p).h3, p.p3 == old(p).p3, p.bth == old(p).bth, p.btc == old(p).btc,
            old(p).wf(),
        decreases 259 - l,
    {
        let mut c: u32 = 1024;
        if l >= 3 {
            match len_code_t(&p.tabs, l as u64) {
                Some((sy, _, x)) => {
                    let v = lit[sy as usize] + 16 * x as u32;
                    c = if v > 1024 { 1024 } else { v };
                }
                None => {}
            }
        }
        p.lenc.set(l, c);
        l = l + 1;
    }
    let mut sy: usize = 0;
    while sy < 30
        invariant sy <= 30, p.dsc@.len() == 30, df@.len() == 30, p.lenc@.len() == 259, p.litc@.len() == 256, tabs_wf(&p.tabs),
            forall|t: int| 0 <= t < 30 ==> #[trigger] p.dsc@[t] <= 1024,
            forall|t: int| 0 <= t < 259 ==> #[trigger] p.lenc@[t] <= 1024,
            forall|t: int| 0 <= t < 256 ==> #[trigger] p.litc@[t] <= 1024,
            p.tabs == old(p).tabs, p.ch == old(p).ch, p.ins == old(p).ins, p.s == old(p).s, p.e == old(p).e,
            p.cur == old(p).cur, p.mc == old(p).mc, p.ml == old(p).ml, p.md == old(p).md,
            p.cost == old(p).cost, p.cl == old(p).cl, p.cd == old(p).cd, p.lg == old(p).lg, p.bnd == old(p).bnd, p.nb == old(p).nb, p.bi == old(p).bi, p.h3 == old(p).h3, p.p3 == old(p).p3, p.bth == old(p).bth, p.btc == old(p).btc,
            old(p).wf(),
        decreases 30 - sy,
    {
        let f = (if df[sy] < 0x1000_0000 { df[sy] as u64 } else { 0x1000_0000 }) + 1;
        let lfv = log2_big(f);
        let c = if ld > lfv { (ld - lfv) / 4096 } else { 0 };
        p.dsc.set(sy, if c < 16 { 16 } else if c > 1024 { 1024 } else { c as u32 });
        sy = sy + 1;
    }
}

/// The cost model of the code for counts `lf`, `df` (every symbol made a
/// little probable, so that unused ones have a finite cost).
fn refit(p: &mut Planner, lf: &Vec<u32>, df: &Vec<u32>)
    requires old(p).wf(), lf@.len() == 286, df@.len() == 30,
    ensures final(p).wf(), final(p).ch == old(p).ch, final(p).tabs == old(p).tabs, final(p).ins == old(p).ins,
        final(p).s == old(p).s, final(p).e == old(p).e, final(p).cur == old(p).cur,
        final(p).mc == old(p).mc, final(p).ml == old(p).ml, final(p).md == old(p).md,
        final(p).cost == old(p).cost, final(p).cl == old(p).cl, final(p).cd == old(p).cd,
        final(p).lg == old(p).lg, final(p).bnd == old(p).bnd, final(p).nb == old(p).nb, final(p).bi == old(p).bi, final(p).h3 == old(p).h3, final(p).p3 == old(p).p3, final(p).bth == old(p).bth, final(p).btc == old(p).btc,
{
    let mut lf1: Vec<u32> = vec![0u32; 286];
    let mut df1: Vec<u32> = vec![0u32; 30];
    let mut t: usize = 0;
    while t < 286
        invariant t <= 286, lf@.len() == 286, lf1@.len() == 286,
        decreases 286 - t,
    {
        lf1.set(t, if lf[t] < 0x1000_0000 { 2 * lf[t] + 1 } else { 0x2000_0001 });
        t = t + 1;
    }
    let mut t: usize = 0;
    while t < 30
        invariant t <= 30, df@.len() == 30, df1@.len() == 30,
        decreases 30 - t,
    {
        df1.set(t, if df[t] < 0x1000_0000 { 2 * df[t] + 1 } else { 0x2000_0001 });
        t = t + 1;
    }
    let lit = heur_lens(&lf1, 15);
    let dist = heur_lens(&df1, 15);
    costs_from(p, &lit, &dist);
}

/// A cost model: bits per literal, per length, per distance symbol.
pub type Model = (Vec<u32>, Vec<u32>, Vec<u32>);

pub open spec fn model_ok(m: &Model) -> bool {
    &&& m.0@.len() == 256 && m.1@.len() == 259 && m.2@.len() == 30
    &&& forall|j: int| 0 <= j < 256 ==> #[trigger] m.0@[j] <= 1024
    &&& forall|j: int| 0 <= j < 259 ==> #[trigger] m.1@[j] <= 1024
    &&& forall|j: int| 0 <= j < 30 ==> #[trigger] m.2@[j] <= 1024
}

/// `m` with each cost moved by up to `amp` bits at random (`rng`, xorshift).
fn perturb(m: &Model, rng: u64, amp: u32) -> (r: (Model, u64))
    requires model_ok(m), amp <= 16,
    ensures model_ok(&r.0),
{
    let mut x = rng;
    let mut a: Vec<u32> = m.0.clone();
    let mut b: Vec<u32> = m.1.clone();
    let mut c: Vec<u32> = m.2.clone();
    let mut t: usize = 0;
    while t < 256
        invariant t <= 256, a@.len() == 256, amp <= 16, forall|j: int| 0 <= j < 256 ==> #[trigger] a@[j] <= 1024,
        decreases 256 - t,
    {
        x = x ^ (x << 13); x = x ^ (x >> 7); x = x ^ (x << 17);
        a.set(t, jiggle(a[t], x, amp));
        t = t + 1;
    }
    let mut t: usize = 0;
    while t < 259
        invariant t <= 259, b@.len() == 259, amp <= 16, forall|j: int| 0 <= j < 259 ==> #[trigger] b@[j] <= 1024,
        decreases 259 - t,
    {
        x = x ^ (x << 13); x = x ^ (x >> 7); x = x ^ (x << 17);
        b.set(t, jiggle(b[t], x, amp));
        t = t + 1;
    }
    let mut t: usize = 0;
    while t < 30
        invariant t <= 30, c@.len() == 30, amp <= 16, forall|j: int| 0 <= j < 30 ==> #[trigger] c@[j] <= 1024,
        decreases 30 - t,
    {
        x = x ^ (x << 13); x = x ^ (x >> 7); x = x ^ (x << 17);
        c.set(t, jiggle(c[t], x, amp));
        t = t + 1;
    }
    ((a, b, c), x)
}

#[inline(always)]
fn jiggle(v: u32, x: u64, amp: u32) -> (r: u32)
    requires v <= 1024, amp <= 16,
    ensures r <= 1024,
{
    let a = 16 * amp;
    let span = 2 * a as u64 + 1;
    let d = (x % span) as u32;
    let up = v + d;
    let r = if up >= a + 16 { up - a } else { 16 };
    if r > 1024 { 1024 } else { r }
}

fn set_model(p: &mut Planner, m: &Model)
    requires old(p).wf(), model_ok(m),
    ensures final(p).wf(), final(p).ch == old(p).ch, final(p).tabs == old(p).tabs, final(p).ins == old(p).ins,
        final(p).s == old(p).s, final(p).e == old(p).e, final(p).cur == old(p).cur,
        final(p).mc == old(p).mc, final(p).ml == old(p).ml, final(p).md == old(p).md,
        final(p).cost == old(p).cost, final(p).cl == old(p).cl, final(p).cd == old(p).cd,
        final(p).lg == old(p).lg, final(p).bnd == old(p).bnd, final(p).nb == old(p).nb, final(p).bi == old(p).bi, final(p).h3 == old(p).h3, final(p).p3 == old(p).p3, final(p).bth == old(p).bth, final(p).btc == old(p).btc,
{
    p.litc = m.0.clone();
    p.lenc = m.1.clone();
    p.dsc = m.2.clone();
}

/// Start a parse of `[s, e)` from model `init` (see `Opt::tries`); `m0` is the
/// previous window's.
fn start_model(data: &[u8], p: &mut Planner, s: usize, e: usize, init: usize, m0: &Model)
    requires old(p).wf(), s < e <= data.len(), e - s <= WMAX, model_ok(m0),
    ensures final(p).wf(), final(p).ch == old(p).ch, final(p).tabs == old(p).tabs, final(p).ins == old(p).ins,
        final(p).s == old(p).s, final(p).e == old(p).e, final(p).cur == old(p).cur,
        final(p).mc == old(p).mc, final(p).ml == old(p).ml, final(p).md == old(p).md,
        final(p).cost == old(p).cost, final(p).cl == old(p).cl, final(p).cd == old(p).cd,
        final(p).lg == old(p).lg, final(p).bnd == old(p).bnd, final(p).nb == old(p).nb, final(p).bi == old(p).bi, final(p).h3 == old(p).h3, final(p).p3 == old(p).p3, final(p).bth == old(p).bth, final(p).btc == old(p).btc,
{
    if init == 1 {
        costs_fixed(p);
    } else if init == 2 {
        let mut lf: Vec<u32> = vec![0u32; 286];
        let mut q: usize = 0;
        while q < e - s
            invariant lf@.len() == 286, s < e <= data.len(), e - s <= WMAX,
                forall|t: int| 0 <= t < 286 ==> #[trigger] lf@[t] <= q,
            decreases e - s - q,
        {
            let x = data[s + q] as usize;
            lf.set(x, lf[x] + 1);
            q = q + 1;
        }
        // the lengths and distances about as in the fixed codes
        let mut t: usize = 256;
        while t < 286
            invariant 256 <= t <= 286, lf@.len() == 286, s < e, e - s <= WMAX,
            decreases 286 - t,
        {
            lf.set(t, ((e - s) / 64) as u32);
            t = t + 1;
        }
        let df: Vec<u32> = vec![((e - s) / 64) as u32; 30];
        refit(p, &lf, &df);
    } else {
        set_model(p, m0);
    }
}

/// `passes` parses of `[s, e)`, each after the first by the previous one's codes.
fn passes(data: &[u8], p: &mut Planner, s: usize, e: usize, o: Opt)
    requires old(p).wf(), s < e <= data.len(), e - s <= WMAX, opt_ok(o),
    ensures final(p).wf(), final(p).ch == old(p).ch, final(p).tabs == old(p).tabs, final(p).ins == old(p).ins,
        final(p).s == old(p).s, final(p).e == old(p).e, final(p).cur == old(p).cur,
        final(p).mc == old(p).mc, final(p).ml == old(p).ml, final(p).md == old(p).md,
        final(p).lg == old(p).lg, final(p).bnd == old(p).bnd, final(p).nb == old(p).nb, final(p).bi == old(p).bi, final(p).h3 == old(p).h3, final(p).p3 == old(p).p3, final(p).bth == old(p).bth, final(p).btc == old(p).btc,
{
    let mut pass: usize = 0;
    while pass < o.passes
        invariant p.wf(), s < e <= data.len(), e - s <= WMAX, opt_ok(o),
            p.ch == old(p).ch, p.tabs == old(p).tabs, p.ins == old(p).ins, p.s == old(p).s, p.e == old(p).e,
            p.cur == old(p).cur, p.mc == old(p).mc, p.ml == old(p).ml, p.md == old(p).md,
            p.lg == old(p).lg, p.bnd == old(p).bnd, p.nb == old(p).nb, p.bi == old(p).bi, p.h3 == old(p).h3, p.p3 == old(p).p3, p.bth == old(p).bth, p.btc == old(p).btc,
        decreases o.passes - pass,
    {
        dp(data, p, s, 0, e);
        if pass + 1 < o.passes {
            let (lf, df) = stats(data, p, s, 0, e);
            if o.frac { refit_frac(p, &lf, &df); } else { refit(p, &lf, &df); }
        }
        pass = pass + 1;
    }
}

/// The bits the parse of `[s, e)` takes with its own Huffman codes (no header).
fn parse_bits(data: &[u8], p: &Planner, s: usize, e: usize) -> (b: u64)
    requires p.wf(), s < e <= data.len(), e - s <= WMAX,
{
    let w = e - s;
    let mut lf: Vec<u32> = vec![0u32; 286];
    let mut df: Vec<u32> = vec![0u32; 30];
    let mut ex: u64 = 0;
    let mut q: usize = 0;
    while q < w
        invariant q <= w + 258, w == e - s, w <= WMAX, p.wf(), s < e <= data.len(), lf@.len() == 286, df@.len() == 30,
            forall|t: int| 0 <= t < 286 ==> #[trigger] lf@[t] <= q,
            forall|t: int| 0 <= t < 30 ==> #[trigger] df@[t] <= q,
            ex <= 18 * q,
        decreases w + 258 - q,
    {
        let (ls, ds, x, len) = tok_syms(data, p, s, q);
        lf.set(ls, lf[ls] + 1);
        if ds < 30 {
            df.set(ds, df[ds] + 1);
        }
        ex = ex + x;
        q = q + len;
    }
    lf.set(256, 1);
    let ll = heur_lens(&lf, 15);
    let dl = heur_lens(&df, 15);
    let mut b: u64 = if ex > CAP { CAP } else { ex };
    let mut t: usize = 0;
    while t < 286
        invariant t <= 286, lf@.len() == 286, ll@.len() == 286, b <= CAP,
        decreases 286 - t,
    {
        let x = lf[t] as u64;
        let y = ll[t] as u64;
        assert(x * y < 0x100_0000_0000) by (nonlinear_arith) requires x < 0x1_0000_0000, y < 256;
        let v = x * y;
        b = if b + v > CAP { CAP } else { b + v };
        t = t + 1;
    }
    let mut t: usize = 0;
    while t < 30
        invariant t <= 30, df@.len() == 30, dl@.len() == 30, b <= CAP,
        decreases 30 - t,
    {
        let x = df[t] as u64;
        let y = dl[t] as u64;
        assert(x * y < 0x100_0000_0000) by (nonlinear_arith) requires x < 0x1_0000_0000, y < 256;
        let v = x * y;
        b = if b + v > CAP { CAP } else { b + v };
        t = t + 1;
    }
    b
}

/// Split the window's parse into blocks, then parse each again by its own
/// statistics.
fn split_reparse(data: &[u8], p: &mut Planner, i: usize, e: usize, o: Opt)
    requires old(p).wf(), opt_ok(o), i < e <= data.len(), e - i <= WMAX,
    ensures final(p).wf(),
{
    if o.seg != 0 {
        blocks(data, p, i, e, if o.seg < 32 { 32 } else { o.seg }, o.hbits, o.refine);
    } else {
        p.nb = 0;
        p.bi = 0;
    }
    let mut r: usize = 0;
    while r < o.reopt
        invariant p.wf(), i < e <= data.len(), e - i <= WMAX, opt_ok(o),
        decreases o.reopt - r,
    {
        let mut b: usize = 0;
        let mut a: usize = 0;
        while b < p.nb
            invariant p.wf(), i < e <= data.len(), e - i <= WMAX, opt_ok(o), b <= p.nb,
            decreases p.nb - b,
        {
            let z = p.bnd[b] as usize;
            if a < z && z <= e - i {
                let (lf, df) = stats(data, p, i, a, i + z);
                if o.frac { refit_frac(p, &lf, &df); } else { refit(p, &lf, &df); }
                dp(data, p, i, a, i + z);
            }
            a = z;
            b = b + 1;
        }
        r = r + 1;
    }
}

/// The bits of the parse of `[s + a, s + z)` as one block: the least of a
/// dynamic block (our header for its codes), a fixed one and a stored one.
fn range_cost(data: &[u8], p: &Planner, s: usize, a: usize, z: usize) -> (c: u64)
    requires p.wf(), a < z, s + z <= data.len(), z <= WMAX,
    ensures c <= 4 * CAP,
{
    let mut f: Vec<u32> = vec![0u32; 316];
    let mut ex: u64 = 0;
    let mut q: usize = a;
    while q < z
        invariant a <= q <= z + 258, z <= WMAX, s + z <= data.len(), p.wf(), f@.len() == 316, ex <= 18 * q,
            forall|t: int| 0 <= t < 316 ==> #[trigger] f@[t] <= q,
        decreases z + 258 - q,
    {
        let (ls, ds, x, len) = tok_syms(data, p, s, q);
        f.set(ls, f[ls] + 1);
        if ds < 30 {
            f.set(286 + ds, f[286 + ds] + 1);
        }
        ex = ex + x;
        q = q + len;
    }
    if f[256] == 0 { f.set(256, 1); }
    let mut lens: Vec<u8> = vec![0u8; 316];
    let dl = huff_est(&f, 0, 286, &mut lens);
    let dd = huff_est(&f, 286, 316, &mut lens);
    let (ops, _) = plan_ops(&lens, 7);
    let (_, hb) = cl_for(&ops);
    let dynamic = dl + dd + ex + hb + 3;
    let mut fx: u64 = 0;
    let mut t: usize = 0;
    while t < 316
        invariant t <= 316, f@.len() == 316, fx <= t * 9 * 0x1_0000_0000,
        decreases 316 - t,
    {
        let x = f[t] as u64;
        let fl: u64 = if t < 144 { 8 } else if t < 256 { 9 } else if t < 280 { 7 } else if t < 286 { 8 } else { 5 };
        assert(x * fl <= 9 * 0x1_0000_0000) by (nonlinear_arith) requires x < 0x1_0000_0000, fl <= 9;
        fx = fx + x * fl;
        t = t + 1;
    }
    let fixed = fx + ex + 3;
    let nbytes = (z - a) as u64;
    let stored = 8 * nbytes + 40 * (nbytes / 65535 + 1);
    let c = if dynamic < fixed { dynamic } else { fixed };
    if stored < c { stored } else { c }
}

/// The bits of the window's plan: its blocks', by `range_cost`.
fn plan_cost(data: &[u8], p: &Planner, s: usize, e: usize) -> (c: u64)
    requires p.wf(), s < e <= data.len(), e - s <= WMAX,
{
    let w = e - s;
    if p.nb == 0 {
        return range_cost(data, p, s, 0, w);
    }
    let mut c: u64 = 0;
    let mut a: usize = 0;
    let mut b: usize = 0;
    while b < p.nb
        invariant b <= p.nb, p.wf(), s < e <= data.len(), e - s <= WMAX, w == e - s, c <= CAP,
        decreases p.nb - b,
    {
        let z = p.bnd[b] as usize;
        if a < z && z <= w {
            let x = range_cost(data, p, s, a, z);
            c = if c + x > CAP { CAP } else { c + x };
            a = z;
        }
        b = b + 1;
    }
    c
}

/// Plan the window from `i`: its candidates, then `passes` parses.
fn plan_window(data: &[u8], p: &mut Planner, i: usize, o: Opt)
    requires old(p).wf(), opt_ok(o), i < data.len(), data.len() < 0x1000_0000,
    ensures final(p).wf(), final(p).s == i, final(p).cur == i, i < final(p).e <= data.len(), final(p).e - i <= WMAX,
{
    let n = data.len();
    let e = if n - i < o.win { n } else { i + o.win };
    // the candidates
    let mut q: usize = 0;
    let mut skip: usize = 0;
    while q < e - i
        invariant p.wf(), i < e <= n, e - i <= WMAX, n == data.len(), n < 0x1000_0000, opt_ok(o),
        decreases e - i - q,
    {
        let at = i + q;
        let mut cnt: usize = 0;
        if at + 3 <= n && at >= p.ins {
            let c3 = insert3(data, &mut p.h3, &mut p.p3, at, o.steps3);
            if o.bt {
                let (c, best) = bt_find(data, at, &mut p.bth, &mut p.btc, o.chain, o.nice, skip == 0, c3,
                                        &mut p.ml, &mut p.md, q * K);
                if skip == 0 {
                    cnt = c;
                    if best >= o.nice {
                        skip = best - 1;
                    }
                } else {
                    skip = skip - 1;
                }
            } else {
                let (first, _) = insert(data, &mut p.ch, at);
                if skip == 0 {
                    let (c, best) = find(data, at, first, c3, &p.ch.prev, o.chain, o.nice, &mut p.ml, &mut p.md, q * K);
                    cnt = c;
                    if best >= o.nice {
                        skip = best - 1;
                    }
                } else {
                    skip = skip - 1;
                }
            }
            p.ins = at + 1;
        }
        p.mc.set(q, cnt as u8);
        q = q + 1;
    }
    // whole plans (parse, split, re-parse) from each starting model; the one
    // that codes smallest is kept
    let w = e - i;
    let m0 = (p.litc.clone(), p.lenc.clone(), p.dsc.clone());
    let mut best: u64 = u64::MAX;
    let mut bcl: Vec<u16> = vec![0u16; WMAX];
    let mut bcd: Vec<u16> = vec![0u16; WMAX];
    let mut bbnd: Vec<u32> = vec![0u32; MS];
    let mut bnb: usize = 0;
    let mut bm = (p.litc.clone(), p.lenc.clone(), p.dsc.clone());
    let mut init: usize = 0;
    // and from the best model so far, perturbed at random (zopfli's way out of a local optimum)
    let mut rng: u64 = (i as u64) ^ 0x9E37_79B9_7F4A_7C15;
    while init < 3 + o.rand
        invariant p.wf(), i < e <= n, e - i <= WMAX, w == e - i, n == data.len(), opt_ok(o), init <= 3 + o.rand,
            bcl@.len() == WMAX, bcd@.len() == WMAX, bbnd@.len() == MS, bnb <= MS, model_ok(&m0), model_ok(&bm),
        decreases 3 + o.rand - init,
    {
        if init >= 3 || (o.tries >> init) & 1 == 1 || (init == 0 && o.tries & 7 == 0) {
            if init < 3 {
                start_model(data, p, i, e, init, &m0);
            } else {
                let (m, r2) = perturb(&bm, rng, o.amp);
                rng = r2;
                set_model(p, &m);
            }
            passes(data, p, i, e, o);
            let wm = (p.litc.clone(), p.lenc.clone(), p.dsc.clone());
            split_reparse(data, p, i, e, o);
            let b = plan_cost(data, p, i, e);
            if b < best {
                best = b;
                let mut q: usize = 0;
                while q < w
                    invariant q <= w, w <= WMAX, bcl@.len() == WMAX, bcd@.len() == WMAX, p.wf(),
                    decreases w - q,
                {
                    bcl.set(q, p.cl[q]);
                    bcd.set(q, p.cd[q]);
                    q = q + 1;
                }
                let mut k: usize = 0;
                while k < p.nb
                    invariant k <= p.nb, p.wf(), bbnd@.len() == MS,
                    decreases p.nb - k,
                {
                    bbnd.set(k, p.bnd[k]);
                    k = k + 1;
                }
                bnb = p.nb;
                bm = wm;
            }
        }
        init = init + 1;
    }
    let mut q: usize = 0;
    while q < w
        invariant q <= w, w <= WMAX, bcl@.len() == WMAX, bcd@.len() == WMAX, p.wf(),
            i < e <= n, e - i <= WMAX, w == e - i, n == data.len(), opt_ok(o), model_ok(&bm),
            bbnd@.len() == MS, bnb <= MS,
        decreases w - q,
    {
        p.cl.set(q, bcl[q]);
        p.cd.set(q, bcd[q]);
        q = q + 1;
    }
    let mut k: usize = 0;
    while k < bnb
        invariant k <= bnb, bnb <= MS, p.wf(), bbnd@.len() == MS, i < e <= n, e - i <= WMAX, n == data.len(),
            model_ok(&bm),
        decreases bnb - k,
    {
        p.bnd.set(k, bbnd[k]);
        k = k + 1;
    }
    p.nb = bnb;
    p.bi = 0;
    set_model(p, &bm);
    p.s = i;
    p.e = e;
    p.cur = i;
}

/// The symbols of the token the parse chose at window offset `q` (`s + q`):
/// its literal/length symbol, its distance symbol (30: none), its extra bits,
/// and its length.
#[inline(always)]
fn tok_syms(data: &[u8], p: &Planner, s: usize, q: usize) -> (r: (usize, usize, u64, usize))
    requires p.wf(), q < WMAX, s + q < data.len(),
    ensures r.0 < 286, r.1 <= 30, r.2 <= 18, 1 <= r.3 <= 258,
{
    let l = p.cl[q] as usize;
    if 3 <= l && l <= 258 {
        let d = p.cd[q] as u64;
        let d = if d == 0 || d > 32768 { 1 } else { d };
        match (len_code_t(&p.tabs, l as u64), dist_code_t(&p.tabs, d)) {
            (Some((ls, _, lx)), Some((ds, _, dx))) => return (ls as usize, ds as usize, lx + dx, l),
            _ => {}
        }
    }
    (data[s + q] as usize, 30, 0, 1)
}

/// The estimated bits (in 1/256) of a block with symbol counts `f` (286
/// literal/length, then 30 distance) and `ex` extra bits.
fn est(p: &Planner, f: &Vec<u32>, ex: u64, hbits: u64, nbytes: u64) -> (c: u64)
    requires p.wf(), f@.len() == 316, ex <= CAP, hbits <= 100000, nbytes <= WMAX + 258,
    ensures c <= CAP,
{
    let mut tl: u64 = 0;
    let mut td: u64 = 0;
    let mut sl: u64 = 0;
    let mut used: u64 = 0;
    // the bits with the fixed codes
    let mut fx: u64 = 0;
    let mut t: usize = 0;
    while t < 316
        invariant t <= 316, f@.len() == 316, p.wf(), tl <= t * 0x1_0000_0000, td <= t * 0x1_0000_0000,
            sl <= t * 0x4000_0000, used <= t, fx <= t * 9 * 0x1_0000_0000,
        decreases 316 - t,
    {
        let x = f[t] as u64;
        let fl: u64 = if t < 144 { 8 } else if t < 256 { 9 } else if t < 280 { 7 } else if t < 286 { 8 } else { 5 };
        assert(x * fl <= 9 * 0x1_0000_0000) by (nonlinear_arith) requires x < 0x1_0000_0000, fl <= 9;
        fx = fx + x * fl;
        if x > 0 {
            used = used + 1;
            let xi = if x > WMAX as u64 { WMAX } else { x as usize };
            sl = sl + p.lg[xi];
            if t < 286 { tl = tl + x; } else { td = td + x; }
        }
        t = t + 1;
    }
    let li = if tl > WMAX as u64 { WMAX } else { tl as usize };
    let di = if td > WMAX as u64 { WMAX } else { td as usize };
    let tot = p.lg[li] + p.lg[di];
    let sym = if tot > sl { tot - sl } else { 0 };
    let dynamic = sym + 256 * (ex + hbits + 4 * used);
    let fixed = 256 * (fx + ex + 3);
    let stored = 256 * (8 * nbytes + 40 * (nbytes / 65535 + 1));
    let c = if dynamic < fixed { dynamic } else { fixed };
    let c = if stored < c { stored } else { c };
    if c > CAP { CAP } else { c }
}

// ------------------------------------------------- exact block costs

/// Sort `w`/`id` (the first `m`) by `w`, ascending (heap sort).
fn heap_sort(w: &mut Vec<u64>, id: &mut Vec<usize>, m: usize)
    requires m <= old(w)@.len(), old(w)@.len() == old(id)@.len(), old(w)@.len() <= 1024,
    ensures final(w)@.len() == old(w)@.len(), final(id)@.len() == old(id)@.len(),
{
    // sift down from `r` within the first `n`
    let mut start = m / 2;
    while start > 0
        invariant start <= m / 2, m <= w@.len(), w@.len() == id@.len(), w@.len() <= 1024, w@.len() == old(w)@.len(),
            id@.len() == old(id)@.len(),
        decreases start,
    {
        start = start - 1;
        sift(w, id, start, m);
    }
    let mut n = m;
    while n > 1
        invariant n <= m, m <= w@.len(), w@.len() == id@.len(), w@.len() <= 1024, w@.len() == old(w)@.len(),
            id@.len() == old(id)@.len(),
        decreases n,
    {
        n = n - 1;
        let a = w[0];
        let b = w[n];
        w.set(0, b);
        w.set(n, a);
        let a = id[0];
        let b = id[n];
        id.set(0, b);
        id.set(n, a);
        sift(w, id, 0, n);
    }
}

fn sift(w: &mut Vec<u64>, id: &mut Vec<usize>, r: usize, n: usize)
    requires n <= old(w)@.len(), old(w)@.len() == old(id)@.len(), old(w)@.len() <= 1024, r < 1024,
    ensures final(w)@.len() == old(w)@.len(), final(id)@.len() == old(id)@.len(),
{
    let mut x = r;
    let mut guard: usize = 0;
    while 2 * x + 1 < n && guard < 64
        invariant n <= w@.len(), w@.len() == id@.len(), w@.len() <= 1024, w@.len() == old(w)@.len(),
            id@.len() == old(id)@.len(), x < 1024,
        decreases 64 - guard,
    {
        let mut c = 2 * x + 1;
        if c + 1 < n && w[c + 1] > w[c] {
            c = c + 1;
        }
        if x >= n || w[c] <= w[x] {
            break;
        }
        let a = w[x];
        let b = w[c];
        w.set(x, b);
        w.set(c, a);
        let a = id[x];
        let b = id[c];
        id.set(x, b);
        id.set(c, a);
        x = c;
        guard = guard + 1;
    }
}

/// Huffman's code for the counts `f[lo..hi)`: its lengths (capped at 15) into
/// `lens[lo..hi)`, and its cost in bits.
fn huff_est(f: &Vec<u32>, lo: usize, hi: usize, lens: &mut Vec<u8>) -> (c: u64)
    requires lo <= hi <= f@.len(), f@.len() == old(lens)@.len(), hi - lo <= 512,
        forall|t: int| 0 <= t < old(lens)@.len() ==> #[trigger] old(lens)@[t] <= 15,
    ensures final(lens)@.len() == old(lens)@.len(), c <= CAP,
        forall|t: int| 0 <= t < final(lens)@.len() ==> #[trigger] final(lens)@[t] <= 15,
{
    let mut w: Vec<u64> = vec![0u64; 512];
    let mut id: Vec<usize> = vec![0usize; 512];
    let mut m: usize = 0;
    let mut t = lo;
    while t < hi
        invariant lo <= t <= hi, hi <= f@.len(), f@.len() == lens@.len(), m <= t - lo, hi - lo <= 512,
            w@.len() == 512, id@.len() == 512,
            forall|j: int| 0 <= j < lens@.len() ==> #[trigger] lens@[j] <= 15,
        decreases hi - t,
    {
        lens.set(t, 0);
        if f[t] != 0 {
            w.set(m, f[t] as u64);
            id.set(m, t);
            m = m + 1;
        }
        t = t + 1;
    }
    if m == 0 {
        return 0;
    }
    if m == 1 {
        let i = id[0];
        if i < lens.len() { lens.set(i, 1); }
        return if w[0] > CAP { CAP } else { w[0] };
    }
    heap_sort(&mut w, &mut id, m);
    // two queues: the sorted leaves, and the merged nodes (made in weight order)
    let mut iw: Vec<u64> = vec![0u64; 512];
    let mut ipar: Vec<usize> = vec![0usize; 512];
    let mut lpar: Vec<usize> = vec![0usize; 512];
    let mut li: usize = 0;
    let mut qh: usize = 0;
    let mut ni: usize = 0;
    let mut cost: u64 = 0;
    while ni + 1 < m
        invariant ni + 1 <= m, m <= 512, li <= m, qh <= ni, w@.len() == 512, iw@.len() == 512, ipar@.len() == 512,
            lpar@.len() == 512, cost <= CAP,
            forall|j: int| 0 <= j < 512 ==> #[trigger] iw@[j] <= CAP,
        decreases m - ni,
    {
        // the two lightest, each a leaf (`< 512`) or a merged node (`512 +`)
        let mut a: usize = 0;
        let mut b: usize = 0;
        let mut k: usize = 0;
        while k < 2
            invariant k <= 2, li <= m, m <= 512, qh <= ni, ni + 1 < m || k == 2, w@.len() == 512, iw@.len() == 512,
                forall|j: int| 0 <= j < 512 ==> #[trigger] iw@[j] <= CAP,
            decreases 2 - k,
        {
            let x;
            if li < m && (qh >= ni || w[li] <= iw[qh]) {
                x = li;
                li = li + 1;
            } else if qh < ni {
                x = 512 + qh;
                qh = qh + 1;
            } else {
                x = 0;
            }
            if k == 0 { a = x; } else { b = x; }
            k = k + 1;
        }
        let wa = if a < 512 { if w[a] > CAP { CAP } else { w[a] } } else if a - 512 < 512 { iw[a - 512] } else { 0 };
        let wb = if b < 512 { if w[b] > CAP { CAP } else { w[b] } } else if b - 512 < 512 { iw[b - 512] } else { 0 };
        let sw = if wa + wb > CAP { CAP } else { wa + wb };
        iw.set(ni, sw);
        if a < 512 { lpar.set(a, ni); } else if a - 512 < 512 { ipar.set(a - 512, ni); }
        if b < 512 { lpar.set(b, ni); } else if b - 512 < 512 { ipar.set(b - 512, ni); }
        cost = if cost + sw > CAP { CAP } else { cost + sw };
        ni = ni + 1;
    }
    // depths, from the root (the last node made) down
    let mut d: Vec<u8> = vec![0u8; 512];
    let mut k = ni;
    while k > 1
        invariant k <= ni, ni < 512, d@.len() == 512, ipar@.len() == 512,
        decreases k,
    {
        k = k - 1;
        let pk = ipar[k - 1];
        let dp = if pk < 512 { d[pk] } else { 0 };
        d.set(k - 1, if dp < 200 { dp + 1 } else { 200 });
    }
    let mut j: usize = 0;
    while j < m
        invariant j <= m, m <= 512, d@.len() == 512, lpar@.len() == 512, id@.len() == 512, lens@.len() == f@.len(),
            forall|t: int| 0 <= t < lens@.len() ==> #[trigger] lens@[t] <= 15,
        decreases m - j,
    {
        let pj = lpar[j];
        let dj = if pj < 512 { d[pj] as usize + 1 } else { 15 };
        let i = id[j];
        if i < lens.len() {
            lens.set(i, if dj > 15 { 15 } else { dj as u8 });
        }
        j = j + 1;
    }
    cost
}

/// The bits of a block of the segments `[a, b)` (prefix sums `pre`, `prex`;
/// `nbytes` bytes): the least of a dynamic block (our header for its codes),
/// a fixed one and a stored one.
fn exact(pre: &Vec<u32>, prex: &Vec<u64>, a: usize, b: usize, nbytes: u64) -> (c: u64)
    requires a <= b < MS, pre@.len() == MS * 316, prex@.len() == MS, nbytes <= WMAX + 258,
    ensures c <= 4 * CAP,
{
    let mut f: Vec<u32> = vec![0u32; 316];
    let mut t: usize = 0;
    while t < 316
        invariant t <= 316, f@.len() == 316, pre@.len() == MS * 316, a <= b < MS,
        decreases 316 - t,
    {
        let x = pre[b * 316 + t];
        let y = pre[a * 316 + t];
        f.set(t, if x >= y { x - y } else { 0 });
        t = t + 1;
    }
    if f[256] == 0 { f.set(256, 1); }
    let ex0 = if prex[b] >= prex[a] { prex[b] - prex[a] } else { 0 };
    let ex = if ex0 > CAP { CAP } else { ex0 };
    let mut lens: Vec<u8> = vec![0u8; 316];
    let dl = huff_est(&f, 0, 286, &mut lens);
    let dd = huff_est(&f, 286, 316, &mut lens);
    let (ops, _) = plan_ops(&lens, 7);
    let (_, hb) = cl_for(&ops);
    let dynamic = dl + dd + ex + hb + 3;
    let mut fx: u64 = 0;
    let mut t: usize = 0;
    while t < 316
        invariant t <= 316, f@.len() == 316, fx <= t * 9 * 0x1_0000_0000,
        decreases 316 - t,
    {
        let x = f[t] as u64;
        let fl: u64 = if t < 144 { 8 } else if t < 256 { 9 } else if t < 280 { 7 } else if t < 286 { 8 } else { 5 };
        assert(x * fl <= 9 * 0x1_0000_0000) by (nonlinear_arith) requires x < 0x1_0000_0000, fl <= 9;
        fx = fx + x * fl;
        t = t + 1;
    }
    let fixed = fx + ex + 3;
    let stored = 8 * nbytes + 40 * (nbytes / 65535 + 1);
    let c = if dynamic < fixed { dynamic } else { fixed };
    if stored < c { stored } else { c }
}

/// Move or drop each block end of `cs` (segment indices, increasing, the last
/// `nseg`) to where the two blocks around it cost least, exactly.
fn refine(pre: &Vec<u32>, prex: &Vec<u64>, segend: &Vec<u32>, cs: &Vec<usize>, nseg: usize, span: usize) -> (r: Vec<usize>)
    requires pre@.len() == MS * 316, prex@.len() == MS, segend@.len() == MS, nseg < MS, span >= 1,
        cs@.len() <= MS,
    ensures r@.len() <= cs@.len(), forall|k: int| 0 <= k < r@.len() ==> #[trigger] r@[k] <= nseg,
{
    let mut out: Vec<usize> = Vec::new();
    let mut a: usize = 0;
    let mut k: usize = 0;
    while k + 1 < cs.len()
        invariant k <= cs@.len(), cs@.len() <= MS, a <= nseg, nseg < MS, out@.len() <= k,
            cs@.len() == 0 || k < cs@.len(),
            pre@.len() == MS * 316, prex@.len() == MS, segend@.len() == MS, span >= 1,
            forall|j: int| 0 <= j < out@.len() ==> #[trigger] out@[j] <= nseg,
        decreases cs@.len() - k,
    {
        let x0 = cs[k];
        let b = cs[k + 1];
        if a < x0 && x0 < b && b <= nseg {
            let ba = bytes_of(segend, a);
            let bx0 = bytes_of(segend, x0);
            let bb = bytes_of(segend, b);
            let mut best = exact(pre, prex, a, x0, sub_b(bx0, ba)) + exact(pre, prex, x0, b, sub_b(bb, bx0));
            let mut bx = x0;
            let mut merge = false;
            if b - a <= span {
                let c = exact(pre, prex, a, b, sub_b(bb, ba));
                if c < best {
                    best = c;
                    merge = true;
                }
            }
            let mut x = a + 1;
            while x < b
                invariant a < x <= b, b <= nseg, nseg < MS, pre@.len() == MS * 316, prex@.len() == MS,
                    segend@.len() == MS, bx <= nseg, best <= 8 * CAP,
                decreases b - x,
            {
                if x != x0 && x - a <= span && b - x <= span {
                    let bxx = bytes_of(segend, x);
                    let c = exact(pre, prex, a, x, sub_b(bxx, ba)) + exact(pre, prex, x, b, sub_b(bb, bxx));
                    if c < best {
                        best = c;
                        bx = x;
                        merge = false;
                    }
                }
                x = x + 1;
            }
            if !merge {
                out.push(bx);
                a = bx;
            }
        } else if x0 <= nseg {
            out.push(x0);
            a = x0;
        }
        k = k + 1;
    }
    if cs.len() > 0 {
        let last = cs[cs.len() - 1];
        out.push(if last <= nseg { last } else { nseg });
    }
    out
}

/// Bytes up to the end of segment `j - 1` (0 for `j == 0`).
#[inline(always)]
fn bytes_of(segend: &Vec<u32>, j: usize) -> (r: u64)
    requires segend@.len() == MS, j < MS,
{
    if j == 0 { 0 } else { segend[j - 1] as u64 }
}

#[inline(always)]
fn sub_b(x: u64, y: u64) -> (r: u64)
    ensures r <= WMAX + 258,
{
    if x >= y && x - y <= (WMAX + 258) as u64 { x - y } else { 0 }
}

/// Split the parse of `[s, e)` into blocks: segments of `g` tokens, then the
/// cheapest cut at segment ends (of at most 32768 tokens a block), by `est`.
fn blocks(data: &[u8], p: &mut Planner, s: usize, e: usize, g: usize, hbits: usize, rounds: usize)
    requires old(p).wf(), s < e <= data.len(), e - s <= WMAX, 32 <= g <= 32768, hbits <= 100000, rounds <= 8,
    ensures final(p).wf(), final(p).ch == old(p).ch, final(p).tabs == old(p).tabs, final(p).ins == old(p).ins,
        final(p).cl == old(p).cl, final(p).cd == old(p).cd,
{
    let w = e - s;
    // the segments: their counts and extra bits, and where each ends
    let mut segc: Vec<u32> = vec![0u32; MS * 316];
    let mut segx: Vec<u64> = vec![0u64; MS];
    let mut segend: Vec<u32> = vec![0u32; MS];
    let mut q: usize = 0;
    let mut nt: usize = 0;
    while q < w
        invariant q <= w + 258, w == e - s, w <= WMAX, s < e <= data.len(), p.wf(), nt <= q, nt <= w, 32 <= g, g <= 32768,
            segc@.len() == MS * 316, segx@.len() == MS, segend@.len() == MS,
            forall|j: int| 0 <= j < MS * 316 ==> #[trigger] segc@[j] <= nt,
            forall|j: int| 0 <= j < MS ==> #[trigger] segx@[j] <= 18 * nt,
        decreases w + 258 - q,
    {
        let (ls, ds, ex, len) = tok_syms(data, p, s, q);
        let m = nt / g;
        assert(m < MS - 1) by (nonlinear_arith) requires m as int == (nt as int) / (g as int), nt < WMAX, 32 <= g;
        segc.set(m * 316 + ls, segc[m * 316 + ls] + 1);
        if ds < 30 {
            segc.set(m * 316 + 286 + ds, segc[m * 316 + 286 + ds] + 1);
        }
        segx.set(m, segx[m] + ex);
        q = q + len;
        nt = nt + 1;
        segend.set(m, if q > w { w as u32 } else { q as u32 });
    }
    let nseg = (nt + g - 1) / g;
    assert(nseg < MS) by (nonlinear_arith) requires nseg as int == (nt as int + g as int - 1) / (g as int), nt <= WMAX, 32 <= g;
    // the cheapest split: best[j] for the first j segments
    let mut best: Vec<u64> = vec![0u64; MS];
    let mut from: Vec<usize> = vec![0usize; MS];
    let span = 32768 / g;
    assert(span >= 1) by (nonlinear_arith) requires span as int == 32768int / (g as int), g <= 32768, 32 <= g;
    let mut f: Vec<u32> = vec![0u32; 316];
    let mut j: usize = 1;
    while j <= nseg
        invariant 1 <= j <= nseg + 1, nseg < MS, best@.len() == MS, from@.len() == MS, f@.len() == 316,
            segc@.len() == MS * 316, segx@.len() == MS, p.wf(), hbits <= 100000, span >= 1, segend@.len() == MS,
            forall|t: int| 0 <= t < MS ==> #[trigger] best@[t] <= CAP,
            forall|t: int| 0 <= t < MS ==> #[trigger] from@[t] < MS,
        decreases nseg + 1 - j,
    {
        let mut t: usize = 0;
        while t < 316
            invariant t <= 316, f@.len() == 316,
            decreases 316 - t,
        {
            f.set(t, 0);
            t = t + 1;
        }
        let mut ex: u64 = 0;
        let mut bj: u64 = CAP;
        let mut fj: usize = j - 1;
        let lo = if j > span { j - span } else { 0 };
        let mut i = j;
        while i > lo
            invariant lo <= i <= j, 1 <= j <= nseg, nseg < MS, f@.len() == 316, segc@.len() == MS * 316, segx@.len() == MS,
                segend@.len() == MS,
                best@.len() == MS, p.wf(), hbits <= 100000, ex <= CAP, bj <= CAP, fj < MS,
                forall|t: int| 0 <= t < MS ==> #[trigger] best@[t] <= CAP,
            decreases i,
        {
            i = i - 1;
            let mut t: usize = 0;
            while t < 316
                invariant t <= 316, f@.len() == 316, segc@.len() == MS * 316, i < MS,
                decreases 316 - t,
            {
                let a = f[t];
                let b = segc[i * 316 + t];
                f.set(t, if a < 0x1000_0000 && b < 0x1000_0000 { a + b } else { 0x2000_0000 });
                t = t + 1;
            }
            ex = if segx[i] > CAP || ex > CAP - segx[i] { CAP } else { ex + segx[i] };
            let lo_b: u64 = if i == 0 { 0 } else { segend[i - 1] as u64 };
            let hi_b: u64 = segend[j - 1] as u64;
            let nb: u64 = if hi_b > lo_b && hi_b - lo_b <= (WMAX + 258) as u64 { hi_b - lo_b } else { 0 };
            let c = best[i] + est(p, &f, ex, hbits as u64, nb);
            if c < bj {
                bj = c;
                fj = i;
            }
        }
        best.set(j, bj);
        from.set(j, fj);
        j = j + 1;
    }
    // the cut, back from the end: the blocks' last segments (plus 1)
    let mut rev: Vec<usize> = Vec::new();
    let mut j = nseg;
    while j > 0
        invariant j < MS, from@.len() == MS, rev@.len() <= nseg - j, nseg < MS,
            forall|t: int| 0 <= t < MS ==> #[trigger] from@[t] < MS,
            forall|t: int| 0 <= t < rev@.len() ==> #[trigger] rev@[t] <= nseg,
        decreases j,
    {
        rev.push(j);
        let fj = from[j];
        j = if fj < j { fj } else { j - 1 };
    }
    let mut cs: Vec<usize> = Vec::new();
    let mut k = rev.len();
    while k > 0
        invariant k <= rev@.len(), rev@.len() < MS, cs@.len() == rev@.len() - k, nseg < MS,
            forall|t: int| 0 <= t < rev@.len() ==> #[trigger] rev@[t] <= nseg,
            forall|t: int| 0 <= t < cs@.len() ==> #[trigger] cs@[t] <= nseg,
        decreases k,
    {
        k = k - 1;
        cs.push(rev[k]);
    }
    // each end moved to where it costs least, exactly
    let mut r: usize = 0;
    if rounds > 0 {
        // the prefix sums of the segments
        let mut pre: Vec<u32> = vec![0u32; MS * 316];
        let mut prex: Vec<u64> = vec![0u64; MS];
        let mut m: usize = 0;
        while m < nseg
            invariant m <= nseg, nseg < MS, pre@.len() == MS * 316, prex@.len() == MS, segc@.len() == MS * 316,
                segx@.len() == MS,
            decreases nseg - m,
        {
            let mut t: usize = 0;
            while t < 316
                invariant t <= 316, m < nseg, nseg < MS, pre@.len() == MS * 316, segc@.len() == MS * 316,
                decreases 316 - t,
            {
                let x = pre[m * 316 + t];
                let y = segc[m * 316 + t];
                pre.set((m + 1) * 316 + t, if x < 0x4000_0000 && y < 0x4000_0000 { x + y } else { 0x8000_0000 });
                t = t + 1;
            }
            let x = prex[m];
            let y = segx[m];
            prex.set(m + 1, if x < CAP && y < CAP { x + y } else { 2 * CAP });
            m = m + 1;
        }
        while r < rounds
            invariant pre@.len() == MS * 316, prex@.len() == MS, segend@.len() == MS, nseg < MS, span >= 1,
                cs@.len() < MS, forall|t: int| 0 <= t < cs@.len() ==> #[trigger] cs@[t] <= nseg,
            decreases rounds - r,
        {
            cs = refine(&pre, &prex, &segend, &cs, nseg, span);
            r = r + 1;
        }
    }
    let nb = cs.len();
    let mut k: usize = 0;
    while k < nb
        invariant k <= nb, nb == cs@.len(), nb < MS, p.bnd@.len() == MS, p.wf(), segend@.len() == MS, nseg < MS,
            forall|t: int| 0 <= t < cs@.len() ==> #[trigger] cs@[t] <= nseg,
            p.ch == old(p).ch, p.tabs == old(p).tabs, p.ins == old(p).ins, p.cl == old(p).cl, p.cd == old(p).cd,
        decreases nb - k,
    {
        let c = cs[k];
        p.bnd.set(k, if c == 0 { 0 } else { segend[c - 1] });
        k = k + 1;
    }
    p.nb = nb;
    p.bi = 0;
}

/// Whether the match at `i` of length `l` and distance `d` is real.
fn check_match(data: &[u8], i: usize, l: usize, d: usize) -> (ok: bool)
    requires i < data.len(),
    ensures ok ==> (3 <= l <= 258 && 1 <= d <= i && d <= 32768 && i + l <= data.len()
        && forall|j: int| 0 <= j < l ==> #[trigger] data@[i + j] == data@[i + j - d]),
{
    if l < 3 || l > 258 || d < 1 || d > i || d > 32768 || l > data.len() - i {
        return false;
    }
    let mut m: usize = 0;
    while m < l
        invariant m <= l, l <= 258, i + l <= data.len(), 1 <= d <= i,
            forall|j: int| 0 <= j < m ==> #[trigger] data@[i + j] == data@[i + j - d],
        decreases l - m,
    {
        if data[i + m] != data[i + m - d] {
            return false;
        }
        m = m + 1;
    }
    true
}

/// Up to `tok_block()` tokens from `i0`, by the plan (planning a window there
/// first if the plan is not at `i0`). Each match is checked.
pub fn plan_chunk(data: &[u8], i0: usize, p: &mut Planner, o: Opt) -> (r: (Vec<Tok>, usize, Ghost<Seq<int>>))
    requires old(p).wf(), opt_ok(o), i0 < data.len(), data.len() < 0x1000_0000,
    ensures
        final(p).wf(),
        ({
            let (toks, i1, pos) = r;
            &&& i0 < i1 <= data.len() && toks@.len() >= 1 && toks@.len() <= tok_block()
            &&& toks_ok(data@, toks@, pos@) && pos@[0] == i0 && pos@[toks@.len() as int] == i1
        }),
{
    let n = data.len();
    if !(p.s <= i0 && i0 < p.e && p.cur == i0 && p.e <= n && p.e - p.s <= WMAX) {
        plan_window(data, p, i0, o);
    }
    let s = p.s;
    let e = p.e;
    let mut toks: Vec<Tok> = Vec::new();
    let mut i = i0;
    let ghost mut pos: Seq<int> = seq![i0 as int];
    // the end of the current block, if the window was split
    let stop: usize = if p.bi < p.nb { s + p.bnd[p.bi] as usize } else { e };
    while i < e && toks.len() < 32768 && (toks.len() == 0 || i < stop)
        invariant
            p.wf(), s <= i0, i0 < e, e <= n, e - s <= WMAX, p.s == s, p.e == e,
            i0 <= i <= n, n == data.len(), n < 0x1000_0000, toks@.len() <= 32768,
            toks_ok(data@, toks@, pos), pos[0] == i0, pos[toks@.len() as int] == i,
            toks@.len() == 0 ==> i == i0, toks@.len() > 0 ==> i > i0,
        decreases n - i,
    {
        let q = i - s;
        let l = p.cl[q] as usize;
        let d = p.cd[q] as usize;
        let mut tok = Tok { len: 0, lit: data[i], dist: 0, ls: 0, le: 0, lx: 0, ds: 0, de: 0, dx: 0 };
        if l != 0 && check_match(data, i, l, d) {
            match (len_code_t(&p.tabs, l as u64), dist_code_t(&p.tabs, d as u64)) {
                (Some((ls, le, lx)), Some((ds, de, dx))) => {
                    tok = Tok { len: l as u16, lit: 0, dist: d as u16, ls: ls as u16, le: le as u16,
                                lx: lx as u8, ds: ds as u8, de: de as u16, dx: dx as u8 };
                    proof { reveal_with_fuel(vbits::bitspec::p2, 14); }
                }
                _ => {}
            }
        }
        let ghost pos0 = pos;
        let ghost toks0 = toks@;
        let step: usize = if tok.len == 0 { 1 } else { tok.len as usize };
        proof {
            assert(tok_ok(data@, i as int, tok));
            pos = pos0.push(i + step);
        }
        toks.push(tok);
        proof {
            assert forall|k: int| 0 <= k < toks@.len() implies
                tok_ok(data@, pos[k], #[trigger] toks@[k]) && pos[k + 1] == pos[k] + tok_len(toks@[k]) by {
                if k < toks0.len() { assert(toks@[k] == toks0[k]); }
            }
        }
        i = i + step;
    }
    p.cur = i;
    if p.bi < p.nb && i >= stop {
        p.bi = p.bi + 1;
    }
    (toks, i, Ghost(pos))
}

/// Compression with near-optimal parsing.
pub fn deflate_opt(data: &[u8], o: Opt) -> (r: Option<Vec<u8>>)
    requires data.len() < 0x1000_0000, opt_ok(o),
    ensures r matches Some(out) ==> deflate_ok(data@, out@),
{
    let n = data.len();
    if n == 0 {
        return deflate_level(data, level(9));
    }
    let fl = match enc_code(fixed_lit_x()) { None => return None, Some(c) => c };
    let fd = match enc_code(fixed_dist_x()) { None => return None, Some(c) => c };
    let mut w = bw_new();
    let ghost mut st = true;
    proof {
        assert forall|b: Seq<bool>| #[trigger] is_prefix(w.bits(), b) implies
            inflate_blocks(b, 0, Seq::empty(), true) == inflate_blocks(b, w.bits().len() as int, data@.take(0), true) by {
            assert(data@.take(0) =~= Seq::<u8>::empty());
        }
    }
    let mut p = planner_new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n, n == data.len(), n < 0x1000_0000, w.wf(), st, w.pre@.len() == 0, opt_ok(o), p.wf(),
            w.buf@.len() <= 3500 * i,
            enc_ok(&fl, fixed_lit()), enc_ok(&fd, fixed_dist()),
            i < n ==> str_inv(w.bits(), data@, i as int, st),
            i == n ==> str_after(w.bits(), data@, n as int, st, true),
        decreases n - i,
    {
        let (toks, i1, Ghost(pos)) = plan_chunk(data, i, &mut p, o);
        proof { lemma_toks_len(data@, toks@, pos, toks@.len() as int); }
        let last = i1 == n;
        let src = vstd::slice::slice_subrange(data, i, i1);
        let g = put_block(&mut w, &fl, &fd, &toks, Ghost(pos), src, Ghost(data@), Ghost(i as int), last, Ghost(st));
        proof { st = g@; }
        i = i1;
    }
    let ghost wf = w.bits();
    let out = finish(w);
    proof {
        assert(data@.take(n as int) =~= data@);
        let q = wf.len();
        assert forall|b: Seq<bool>| #[trigger] is_prefix(lbits(out@), b) implies inflate(b) == Some((data@, q, st)) by {
            lemma_prefix_trans_b(wf, lbits(out@), b);
            assert(inflate_blocks(b, 0, Seq::empty(), true) == Some((data@.take(n as int), wf.len() as int, st)));
        }
        assert(inflate_q(out@, q, st));
    }
    Some(out)
}

} // verus!
