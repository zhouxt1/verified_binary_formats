//! Compression with dynamic Huffman codes, proved to round-trip.
//!
//! The input is cut into blocks of up to 32768 tokens (literals and matches
//! from hash chains, with zlib's parameters for the level). Each block gets
//! Huffman code lengths from its symbols' counts, by code the proof does not
//! look at: the lengths are checked before they are used (at most 15, not
//! over-subscribed, a code for every symbol the block uses), and a block
//! whose lengths fail, or that is smaller that way, is written with the fixed
//! codes. The dynamic header sends the lengths as zlib does (runs as 16, 17,
//! 18) with a code length code in which all 19 symbols have codes.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
use vbits::lsb::*;
use crate::spec::*;
use crate::huff::*;
use crate::step::*;
use crate::inflate::*;
use crate::enc::*;

verus! {

// ------------------------------------------------------------- tokens

/// A literal (`len == 0`) or a match, with its symbols and extra bits.
#[derive(Clone, Copy)]
pub struct Tok {
    pub len: u16,
    pub lit: u8,
    pub dist: u16,
    pub ls: u16,
    pub le: u16,
    pub lx: u8,
    pub ds: u8,
    pub de: u16,
    pub dx: u8,
}

pub open spec fn tok_len(t: Tok) -> int { if t.len == 0 { 1 } else { t.len as int } }

/// A token is right for the input at `i`.
pub open spec fn tok_ok(data: Seq<u8>, i: int, t: Tok) -> bool {
    if t.len == 0 {
        0 <= i < data.len() && data[i] == t.lit
    } else {
        &&& 3 <= t.len <= 258 && 0 <= i && i + t.len <= data.len()
        &&& 1 <= t.dist <= i && t.dist <= 32768
        &&& forall|j: int| 0 <= j < t.len ==> #[trigger] data[i + j] == data[i + j - t.dist]
        &&& 257 <= t.ls <= 285 && t.lx as nat == len_extra(t.ls as nat) && t.lx <= 5
        &&& t.le < p2(t.lx as nat) && len_base(t.ls as nat) + t.le == t.len
        &&& t.ds <= 29 && t.dx as nat == dist_extra(t.ds as nat) && t.dx <= 13
        &&& t.de < p2(t.dx as nat) && dist_base(t.ds as nat) + t.de == t.dist
    }
}

/// `toks` cover `data` from `pos[0]` to `pos[toks.len()]`.
pub open spec fn toks_ok(data: Seq<u8>, toks: Seq<Tok>, pos: Seq<int>) -> bool {
    &&& pos.len() == toks.len() + 1
    &&& forall|k: int| 0 <= k < toks.len() ==>
        tok_ok(data, pos[k], #[trigger] toks[k]) && pos[k + 1] == pos[k] + tok_len(toks[k])
}

pub open spec fn tok_block() -> nat { 32768 }

/// Every token covers at least a byte.
pub proof fn lemma_toks_len(data: Seq<u8>, toks: Seq<Tok>, pos: Seq<int>, k: int)
    requires toks_ok(data, toks, pos), 0 <= k <= toks.len(),
    ensures pos[k] - pos[0] >= k,
    decreases k,
{
    if k > 0 {
        lemma_toks_len(data, toks, pos, k - 1);
        assert(tok_ok(data, pos[k - 1], toks[k - 1]));
    }
}

#[inline(always)]
fn hash3(data: &[u8], i: usize) -> (h: usize)
    requires i + 3 <= data.len(),
    ensures h < 32768,
{
    let hx = ((data[i] as usize) << 10) ^ ((data[i + 1] as usize) << 5) ^ (data[i + 2] as usize);
    let h = hx & 0x7fff;
    assert(h < 32768) by (bit_vector) requires h == hx & 0x7fff;
    h
}

/// The hash chains: `head` the last position (plus 1) of each three-byte
/// hash, `prev` the one before each position (modulo 32K). Arrays, so that
/// the masked indexes need no bounds checks. Nothing is proved of their
/// contents: every candidate is checked byte by byte.
pub struct Chains {
    pub head: [u32; 32768],
    pub prev: [u32; 32768],
    /// with four-byte chains: the last position of each three-byte hash
    pub head3: [u32; 32768],
}

pub fn chains_new() -> Box<Chains> {
    Box::new(Chains { head: [0u32; 32768], prev: [0u32; 32768], head3: [0u32; 32768] })
}

/// How hard to look for matches (zlib's configuration table).
#[derive(Clone, Copy)]
pub struct Level {
    /// candidates tried
    pub chain: usize,
    /// look one position ahead for a longer match below this length (0: never)
    pub lazy: usize,
    /// the lookahead tries a quarter of the candidates after a match this long
    pub good: usize,
    /// stop looking at a match this long
    pub nice: usize,
    /// put the positions inside a match into the chains up to this length
    pub ins: usize,
    /// chains of four-byte hashes (and a table of three-byte ones)
    pub h4: bool,
}

pub open spec fn level_ok(lv: Level) -> bool {
    lv.chain <= 4096 && lv.nice <= 258 && lv.lazy <= 258
}

/// zlib's levels (its configuration table in deflate.c: good, lazy, nice,
/// chain), 1 to 9; 0 and anything above 9 are taken as 6. Levels 1 to 3
/// take the first match (and put the positions inside a match of up to
/// `lazy` bytes into the chains, as zlib's `max_insert_length`); 4 to 9 look
/// one position ahead, with chains of four-byte hashes.
pub fn level(n: u32) -> (lv: Level)
    ensures level_ok(lv),
{
    if n == 1 {
        Level { chain: 4, lazy: 0, good: 4, nice: 8, ins: 4, h4: false }
    } else if n == 2 {
        Level { chain: 8, lazy: 0, good: 4, nice: 16, ins: 5, h4: false }
    } else if n == 3 {
        Level { chain: 32, lazy: 0, good: 4, nice: 32, ins: 6, h4: false }
    } else if n == 4 {
        Level { chain: 16, lazy: 4, good: 4, nice: 16, ins: 258, h4: true }
    } else if n == 5 {
        Level { chain: 32, lazy: 16, good: 8, nice: 32, ins: 258, h4: true }
    } else if n == 7 {
        Level { chain: 256, lazy: 32, good: 8, nice: 128, ins: 258, h4: true }
    } else if n == 8 {
        Level { chain: 1024, lazy: 128, good: 32, nice: 258, ins: 258, h4: true }
    } else if n == 9 {
        Level { chain: 4096, lazy: 258, good: 32, nice: 258, ins: 258, h4: true }
    } else {
        Level { chain: 128, lazy: 16, good: 8, nice: 128, ins: 258, h4: true }
    }
}

/// A hash of the four bytes at `i` (three at the end).
#[inline(always)]
fn hash4(data: &[u8], i: usize) -> (h: usize)
    requires i + 3 <= data.len(),
    ensures h < 32768,
{
    let x: u32 = if data.len() - i >= 4 {
        (data[i] as u32) | ((data[i + 1] as u32) << 8u32) | ((data[i + 2] as u32) << 16u32) | ((data[i + 3] as u32) << 24u32)
    } else {
        (data[i] as u32) | ((data[i + 1] as u32) << 8u32) | ((data[i + 2] as u32) << 16u32)
    };
    let hx = (x as u64 * 2654435761u64) >> 17u64;
    assert(hx & 0x7fff < 32768) by (bit_vector);
    (hx & 0x7fff) as usize
}

/// The chains' hash at `i`: four bytes or three.
#[inline(always)]
fn hkey(data: &[u8], i: usize, h4: bool) -> (h: usize)
    requires i + 3 <= data.len(),
    ensures h < 32768,
{
    if h4 { hash4(data, i) } else { hash3(data, i) }
}

/// The longest match at `i` (up to `nice`, and longer than `lo`, or none)
/// among up to `chain` earlier positions with the same hash, found through
/// `head` and `prev`, each checked byte by byte.
#[inline(always)]
fn best_match(data: &[u8], i: usize, first: usize, prev: &[u32; 32768], chain: usize, lo: usize, nice: usize, c3: usize) -> (r: (usize, usize))
    requires i < data.len(), chain <= 4096, lo <= 258,
    ensures
        ({
            let (m, d) = r;
            m == 0 || (m > lo && 3 <= m <= 258 && 1 <= d <= i && d <= 32768 && i + m <= data.len()
                && forall|j: int| 0 <= j < m ==> #[trigger] data@[i + j] == data@[i + j - d])
        }),
{
    let n = data.len();
    let mut cand = first;
    let mut best: usize = 0;
    let mut bd: usize = 0;
    let mut depth: usize = 0;
    // the length to beat
    let mut thr: usize = if lo > n - i { n - i } else { lo };
    while depth < chain && cand != 0 && cand <= i && i + 1 - cand <= 32768
        invariant
            i < n, n == data.len(), depth <= chain, chain <= 4096, lo <= 258,
            thr <= n - i, best == 0 ==> thr <= lo || thr == n - i, best != 0 ==> best == thr,
            best == 0 || (best > lo && 3 <= best <= 258 && 1 <= bd <= i && bd <= 32768 && i + best <= n
                && forall|j: int| 0 <= j < best ==> #[trigger] data@[i + j] == data@[i + j - bd]),
        decreases chain - depth,
    {
        let d = i + 1 - cand;
        // a candidate can only do better if it matches at the length to beat
        if thr < n - i && data[i + thr] == data[i + thr - d] {
            let mut m: usize = 0;
            while m < 258 && i + m < n && data[i + m] == data[i + m - d]
                invariant
                    m <= 258, i + m <= n, 1 <= d <= i, n == data.len(),
                    forall|j: int| 0 <= j < m ==> #[trigger] data@[i + j] == data@[i + j - d],
                decreases 258 - m,
            {
                m = m + 1;
            }
            if m >= 3 && m > thr && m > lo {
                best = m;
                bd = d;
                thr = m;
                if m >= nice {
                    break;
                }
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
    // a three-byte match the four-byte chains cannot see
    if best == 0 && lo < 3 && c3 != 0 && c3 <= i && i + 1 - c3 <= 32768 {
        let d = i + 1 - c3;
        let mut m: usize = 0;
        while m < 258 && i + m < n && data[i + m] == data[i + m - d]
            invariant
                m <= 258, i + m <= n, 1 <= d <= i, n == data.len(),
                forall|j: int| 0 <= j < m ==> #[trigger] data@[i + j] == data@[i + j - d],
            decreases 258 - m,
        {
            m = m + 1;
        }
        if m >= 3 && m > lo {
            best = m;
            bd = d;
        }
    }
    (best, bd)
}

/// Up to `tok_block()` tokens from `i0`, starting before `end` (a match may
/// reach past it), with the hash chains.
pub fn tokenize(data: &[u8], i0: usize, end: usize, ch: &mut Chains, lv: Level, tabs: &SymTabs) -> (r: (Vec<Tok>, usize, Ghost<Seq<int>>))
    requires level_ok(lv), tabs_wf(tabs), i0 < end <= data.len(), data.len() < 0x1000_0000,
    ensures
        ({
            let (toks, i1, pos) = r;
            &&& i0 < i1 <= data.len() && toks@.len() >= 1 && toks@.len() <= tok_block()
            &&& toks_ok(data@, toks@, pos@) && pos@[0] == i0 && pos@[toks@.len() as int] == i1
        }),
{
    let n = data.len();
    let mut toks: Vec<Tok> = Vec::new();
    let mut i = i0;
    let ghost mut pos: Seq<int> = seq![i0 as int];
    // the lazy check's match at `i`, when the last token was a literal it chose
    let mut cached = false;
    let mut cm: usize = 0;
    let mut cd: usize = 0;
    while i < end && toks.len() < 32768
        invariant
            end <= n,
            cached ==> (cm == 0 || (3 <= cm <= 258 && 1 <= cd <= i && cd <= 32768 && i + cm <= n
                && forall|j: int| 0 <= j < cm ==> #[trigger] data@[i + j] == data@[i + j - cd])),
            i0 <= i <= n, n == data.len(), n < 0x1000_0000,
            toks@.len() <= 32768, level_ok(lv), tabs_wf(tabs),
            toks_ok(data@, toks@, pos), pos[0] == i0, pos[toks@.len() as int] == i,
            toks@.len() == 0 ==> i == i0, toks@.len() > 0 ==> i > i0,
        decreases n - i,
    {
        let mut tok = Tok { len: 0, lit: data[i], dist: 0, ls: 0, le: 0, lx: 0, ds: 0, de: 0, dx: 0 };
        if n - i < 3 {
            cached = false;
        }
        if n - i >= 3 {
            let h = hkey(data, i, lv.h4);
            let first = ch.head[h] as usize;
            let mut c3: usize = 0;
            if lv.h4 {
                let g = hash3(data, i);
                c3 = ch.head3[g] as usize;
                ch.head3[g] = (i + 1) as u32;
            }
            let pi = i & 0x7fff;
            assert(pi < 32768) by (bit_vector) requires pi == i & 0x7fff;
            let hv = ch.head[h];
            ch.prev[pi] = hv;
            ch.head[h] = (i + 1) as u32;
            let (m, d) = if cached { (cm, cd) } else { best_match(data, i, first, &ch.prev, lv.chain, 0, lv.nice, c3) };
            cached = false;
            // lazy matching: a literal here if the next position has a longer match
            let mut lazy = false;
            if m >= 3 && m < lv.lazy && n - (i + 1) >= 3 {
                let h1 = hkey(data, i + 1, lv.h4);
                let c31 = if lv.h4 { ch.head3[hash3(data, i + 1)] as usize } else { 0 };
                let (m1, d1) = best_match(data, i + 1, ch.head[h1] as usize, &ch.prev, if m >= lv.good { lv.chain / 4 } else { lv.chain }, m, lv.nice, c31);
                lazy = m1 > m;
                if lazy {
                    cached = true;
                    cm = m1;
                    cd = d1;
                }
            }
            if m >= 3 && !lazy {
                match (len_code_t(tabs, m as u64), dist_code_t(tabs, d as u64)) {
                    (Some((ls, le, lx)), Some((ds, de, dx))) => {
                        tok = Tok { len: m as u16, lit: 0, dist: d as u16, ls: ls as u16, le: le as u16,
                                    lx: lx as u8, ds: ds as u8, de: de as u16, dx: dx as u8 };
                        proof { reveal_with_fuel(p2, 14); }
                    }
                    _ => {}
                }
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
        // the positions inside a match go into the chains too
        let mut j: usize = 1;
        let lim = if step <= lv.ins { step } else { 1 };
        while j < lim
            invariant 1 <= j <= lim, lim <= step, i + step <= n, n == data.len(),
                n < 0x1000_0000,
                cached ==> (cm == 0 || (3 <= cm <= 258 && 1 <= cd <= i + step && cd <= 32768 && i + step + cm <= n
                    && forall|k: int| 0 <= k < cm ==> #[trigger] data@[i + step + k] == data@[i + step + k - cd])),
            decreases lim - j,
        {
            if n - (i + j) >= 3 {
                let h = hkey(data, i + j, lv.h4);
                if lv.h4 {
                    let g = hash3(data, i + j);
                    ch.head3[g] = (i + j + 1) as u32;
                }
                let ij = i + j;
                let pj = ij & 0x7fff;
                assert(pj < 32768) by (bit_vector) requires pj == ij & 0x7fff;
                let hv = ch.head[h];
                ch.prev[pj] = hv;
                ch.head[h] = (i + j + 1) as u32;
            }
            j = j + 1;
        }
        i = i + step;
    }
    (toks, i, Ghost(pos))
}

// ------------------------------------------------ writing a block's symbols

/// Every stream that starts with the bits written decodes the block's
/// symbols from `q0`, with the output before the block, to where the
/// writing is, with the output so far.
pub open spec fn blk_inv(w: Seq<bool>, ll: Seq<u8>, dl: Seq<u8>, q0: int, data: Seq<u8>, i0: int, i: int) -> bool {
    forall|b: Seq<bool>| #[trigger] is_prefix(w, b) ==>
        inflate_syms(ll, dl, b, q0, data.take(i0)) == inflate_syms(ll, dl, b, w.len() as int, data.take(i))
}

/// The symbols a token needs have codes.
pub open spec fn tok_coded(ll: Seq<u8>, dl: Seq<u8>, t: Tok) -> bool {
    if t.len == 0 { 1 <= ll[t.lit as int] } else { 1 <= ll[t.ls as int] && 1 <= dl[t.ds as int] }
}

/// Write a token.
pub fn emit_tok(w: &mut BitW, lc: &EncCode, dc: &EncCode, Ghost(ll): Ghost<Seq<u8>>, Ghost(dl): Ghost<Seq<u8>>,
                Ghost(data): Ghost<Seq<u8>>, Ghost(i): Ghost<int>, t: Tok, Ghost(q0): Ghost<int>, Ghost(i0): Ghost<int>)
    // (the bits written only grow)
    requires
        old(w).wf(), old(w).buf@.len() + 8 < 0x1000_0000_0000_0000 - 64,
        enc_ok(lc, ll), enc_ok(dc, dl), ll.len() >= 286, dl.len() >= 30,
        tok_ok(data, i, t), tok_coded(ll, dl, t),
        blk_inv(old(w).bits(), ll, dl, q0, data, i0, i),
    ensures
        final(w).pre == old(w).pre,
        final(w).wf(), final(w).buf@.len() <= old(w).buf@.len() + 20,
        final(w).bits().len() >= old(w).bits().len(), is_prefix(old(w).bits(), final(w).bits()),
        blk_inv(final(w).bits(), ll, dl, q0, data, i0, i + tok_len(t)),
{
    let ghost w0 = w.bits();
    let ghost p = w0.len() as int;
    if t.len == 0 {
        let x = t.lit as usize;
        let l = lc.lens[x] as u64;
        proof { assert(ll[x as int] <= 15); }
        put(w, lc.rc[x], l);
        proof {
            let wf = w.bits();
            assert forall|b: Seq<bool>| #[trigger] is_prefix(wf, b) implies
                inflate_syms(ll, dl, b, q0, data.take(i0)) == inflate_syms(ll, dl, b, wf.len() as int, data.take(i + 1)) by {
                lemma_prefix_of_append(w0, wbits(lc.rc@[x as int], l as nat), b);
                lemma_written_sym(ll, lc, x as int, w0, b);
                assert(sym_step(ll, dl, b, p) == Some(Step::Lit(x as u8, wf.len() as int)));
                lemma_syms_unfold(ll, dl, b, p, data.take(i));
                assert(data.take(i).push(x as u8) =~= data.take(i + 1));
            }
            assert(is_prefix(w0, wf)) by { lemma_prefix_of_append(w0, wbits(lc.rc@[x as int], l as nat), wf); }
        }
    } else {
        let ls = t.ls as usize;
        let ds = t.ds as usize;
        proof { assert(ll[ls as int] <= 15); assert(dl[ds as int] <= 15); }
        let l1 = lc.lens[ls] as u64;
        let l3 = dc.lens[ds] as u64;
        proof {
            assert(lc.rc@[ls as int] < p2(l1 as nat)) by { if l1 == 0 {} }
        }
        let ghost w1 = w0 + wbits(lc.rc@[ls as int], l1 as nat);
        put2(w, lc.rc[ls], l1, t.le as u64, t.lx as u64);
        let ghost w2 = w.bits();
        let ghost w3 = w2 + wbits(dc.rc@[ds as int], l3 as nat);
        put2(w, dc.rc[ds], l3, t.de as u64, t.dx as u64);
        proof {
            let wf = w.bits();
            let p1 = w1.len() as int;
            let p4 = wf.len() as int;
            assert forall|b: Seq<bool>| #[trigger] is_prefix(wf, b) implies
                inflate_syms(ll, dl, b, q0, data.take(i0)) == inflate_syms(ll, dl, b, p4, data.take(i + t.len)) by {
                lemma_prefix_of_append(w3, wbits(t.de as u64, t.dx as nat), b);
                lemma_prefix_of_append(w2, wbits(dc.rc@[ds as int], l3 as nat), b);
                lemma_prefix_of_append(w1, wbits(t.le as u64, t.lx as nat), b);
                lemma_prefix_of_append(w0, wbits(lc.rc@[ls as int], l1 as nat), b);
                lemma_written_sym(ll, lc, ls as int, w0, b);
                lemma_written_bits(t.le as u64, t.lx as nat, w1, b);
                lemma_written_sym(dl, dc, ds as int, w2, b);
                lemma_written_bits(t.de as u64, t.dx as nat, w3, b);
                assert(len_dist(dl, b, p1, ls as nat) == Some((t.len as nat, t.dist as nat, p4)));
                assert(sym_step(ll, dl, b, p) == Some(Step::Copy(t.len as nat, t.dist as nat, p4)));
                lemma_syms_unfold(ll, dl, b, p, data.take(i));
                lemma_lz_match(data, i, t.dist as nat, t.len as nat);
            }
            lemma_prefix_of_append(w3, wbits(t.de as u64, t.dx as nat), wf);
            lemma_prefix_of_append(w2, wbits(dc.rc@[ds as int], l3 as nat), w3);
            lemma_prefix_of_append(w1, wbits(t.le as u64, t.lx as nat), w2);
            lemma_prefix_of_append(w0, wbits(lc.rc@[ls as int], l1 as nat), w1);
            lemma_prefix_trans_b(w0, w1, w2);
            lemma_prefix_trans_b(w0, w2, w3);
            lemma_prefix_trans_b(w0, w3, wf);
        }
    }
}

// ------------------------------------------------------ the dynamic header

/// Where code length code length `k` comes in the header.
pub open spec fn cl_inv(k: nat) -> nat {
    if k == 16 { 0 } else if k == 17 { 1 } else if k == 18 { 2 } else if k == 0 { 3 }
    else if k >= 8 { (2 * (k - 8) + 4) as nat } else { (2 * (7 - k) + 5) as nat }
}

proof fn lemma_cl_inv(k: nat)
    requires k < 19,
    ensures cl_inv(k) < 19, cl_order(cl_inv(k)) == k,
{
}

proof fn lemma_cl_inv2(i: nat)
    requires i < 19,
    ensures cl_order(i) < 19, cl_inv(cl_order(i)) == i,
{
}

/// The code length code lengths after the first `i` have been read.
pub open spec fn cl_acc(cl: Seq<u8>, i: nat) -> Seq<u8> {
    Seq::new(19, |k: int| if cl_inv(k as nat) < i { cl[k] } else { 0u8 })
}

/// The code length code lengths, written 3 bits each in `cl_order`, read back.
proof fn lemma_read_cl_written(b: Seq<bool>, p0: int, cl: Seq<u8>, i: nat)
    requires
        cl.len() == 19, i <= 19, 0 <= p0,
        forall|j: nat| i <= j < 19 ==> #[trigger] getbits(b, p0 + 3 * j, 3) == Some(cl[cl_order(j) as int] as nat),
        forall|k: int| 0 <= k < 19 ==> #[trigger] cl[k] < 8,
    ensures read_cl(b, p0 + 3 * i, 19, i, cl_acc(cl, i)) == Some((cl, p0 + 57)),
    decreases 19 - i,
{
    if i < 19 {
        lemma_cl_inv2(i);
        let k = cl_order(i);
        let v = cl[k as int];
        assert(getbits(b, p0 + 3 * i, 3) == Some(v as nat));
        assert(cl_acc(cl, i).update(k as int, v as nat as u8) =~= cl_acc(cl, i + 1)) by {
            assert forall|m: int| 0 <= m < 19 implies #[trigger] cl_acc(cl, i).update(k as int, v as nat as u8)[m] == cl_acc(cl, i + 1)[m] by {
                lemma_cl_inv(m as nat);
                if m != k as int {
                    if cl_inv(m as nat) == i { assert(cl_order(cl_inv(m as nat)) == m); }
                }
            }
        }
        assert(p0 + 3 * i + 3 == p0 + 3 * (i + 1));
        lemma_read_cl_written(b, p0, cl, i + 1);
    } else {
        assert(cl_acc(cl, 19) =~= cl) by {
            assert forall|m: int| 0 <= m < 19 implies #[trigger] cl_acc(cl, 19)[m] == cl[m] by { lemma_cl_inv(m as nat); }
        }
    }
}

/// Code length op `s` (with extra bits `ex`) at `j` writes `rep` lengths
/// that are the next of `lens`: a length, a repeat of the one before (16),
/// or a run of zeros (17, 18).
pub open spec fn op_ok(lens: Seq<u8>, j: int, s: u8, ex: u8, rep: int) -> bool {
    &&& 0 <= j && 1 <= rep && j + rep <= lens.len() && s <= 18
    &&& if s < 16 {
            rep == 1 && lens[j] == s && ex == 0
        } else if s == 16 {
            j >= 1 && 3 <= rep <= 6 && ex == rep - 3 && forall|k: int| 0 <= k < rep ==> #[trigger] lens[j + k] == lens[j - 1]
        } else if s == 17 {
            3 <= rep <= 10 && ex == rep - 3 && forall|k: int| 0 <= k < rep ==> #[trigger] lens[j + k] == 0
        } else {
            11 <= rep <= 138 && ex == rep - 11 && forall|k: int| 0 <= k < rep ==> #[trigger] lens[j + k] == 0
        }
}

pub open spec fn op_nb(s: u8) -> nat { if s == 16 { 2 } else if s == 17 { 3 } else if s == 18 { 7 } else { 0 } }

/// The next code length op at `j`, zlib's way: runs of zeros as 17 or 18,
/// a length repeated 3 or more times after itself as 16.
pub fn next_op(all: &Vec<u8>, j: usize) -> (r: (u8, u8, usize))
    requires j < all@.len(), all@.len() <= 320, lens_ok(all@),
    ensures op_ok(all@, j as int, r.0, r.1, r.2 as int),
{
    let n = all.len();
    let v = all[j];
    let mut r: usize = 1;
    while j + r < n && r < 138 && all[j + r] == v
        invariant 1 <= r <= 138, j + r <= n, n == all@.len(), v == all@[j as int],
            forall|k: int| 0 <= k < r ==> #[trigger] all@[j + k] == v,
        decreases 138 - r,
    {
        r = r + 1;
    }
    proof { assert(all@[j as int] <= 15); }
    if v == 0 && r >= 11 {
        (18, (r - 11) as u8, r)
    } else if v == 0 && r >= 3 {
        (17, (r - 3) as u8, r)
    } else if j > 0 && v != 0 && all[j - 1] == v && r >= 3 {
        let rep = if r > 6 { 6 } else { r };
        (16, (rep - 3) as u8, rep)
    } else {
        (v, 0, 1)
    }
}

/// Every stream that starts with the bits written reads, from `q0`, the
/// lengths written so far and then what follows `w`.
pub open spec fn hdr_inv(w: Seq<bool>, cl: Seq<u8>, q0: int, lens: Seq<u8>, j: int) -> bool {
    forall|b: Seq<bool>| #[trigger] is_prefix(w, b) ==>
        read_lens(cl, b, q0, lens.len() as nat, Seq::empty()) == read_lens(cl, b, w.len() as int, lens.len() as nat, lens.take(j))
}

/// Write one code length op.
fn emit_op(w: &mut BitW, clc: &EncCode, Ghost(cl): Ghost<Seq<u8>>, Ghost(lens): Ghost<Seq<u8>>, Ghost(q0): Ghost<int>,
           j: usize, s: u8, ex: u8, rep: usize)
    requires
        old(w).wf(), old(w).buf@.len() + 16 < 0x1000_0000_0000_0000 - 64,
        enc_ok(clc, cl), cl.len() == 19, forall|k: int| 0 <= k < 19 ==> 1 <= #[trigger] cl[k] <= 7,
        op_ok(lens, j as int, s, ex, rep as int), hdr_inv(old(w).bits(), cl, q0, lens, j as int),
    ensures
        final(w).pre == old(w).pre,
        final(w).wf(), final(w).buf@.len() <= old(w).buf@.len() + 10,
        is_prefix(old(w).bits(), final(w).bits()),
        hdr_inv(final(w).bits(), cl, q0, lens, j + rep),
{
    let ghost w0 = w.bits();
    let x = s as usize;
    let l = clc.lens[x] as u64;
    proof { assert(cl[x as int] <= 7); }
    put(w, clc.rc[x], l);
    let ghost w1 = w.bits();
    let nb: u64 = if s == 16 { 2 } else if s == 17 { 3 } else if s == 18 { 7 } else { 0 };
    proof { reveal_with_fuel(p2, 8); }
    put(w, ex as u64, nb);
    proof {
        let wf = w.bits();
        let total = lens.len() as nat;
        assert(is_prefix(w0, w1)) by { lemma_prefix_of_append(w0, wbits(clc.rc@[x as int], l as nat), w1); }
        assert(is_prefix(w1, wf)) by { lemma_prefix_of_append(w1, wbits(ex as u64, nb as nat), wf); }
        lemma_prefix_trans_b(w0, w1, wf);
        assert forall|b: Seq<bool>| #[trigger] is_prefix(wf, b) implies
            read_lens(cl, b, q0, total, Seq::empty()) == read_lens(cl, b, wf.len() as int, total, lens.take(j + rep)) by {
            lemma_prefix_trans_b(w1, wf, b);
            lemma_prefix_trans_b(w0, w1, b);
            lemma_prefix_of_append(w0, wbits(clc.rc@[x as int], l as nat), b);
            lemma_prefix_of_append(w1, wbits(ex as u64, nb as nat), b);
            lemma_written_sym(cl, clc, x as int, w0, b);
            let acc = lens.take(j as int);
            assert(acc.len() == j);
            if s < 16 {
                assert(wf.len() == w1.len());
                assert(acc.push(s as nat as u8) =~= lens.take(j + 1));
            } else {
                lemma_written_bits(ex as u64, nb as nat, w1, b);
                let base: nat = if s == 16 { 3 } else if s == 17 { 3 } else { 11 };
                let v: u8 = if s == 16 { acc.last() } else { 0u8 };
                assert(base + ex as nat == rep);
                assert(acc + Seq::new(rep as nat, |_i: int| v) =~= lens.take(j + rep)) by {
                    assert forall|k: int| j <= k < j + rep implies #[trigger] lens.take(j + rep)[k] == v by {
                        assert(lens[j + (k - j)] == if s == 16 { lens[j - 1] } else { 0u8 });
                    }
                }
            }
        }
    }
}

/// Whether zlib accepts a dynamic header with these codes.
pub open spec fn hdr_strict(cl: Seq<u8>, lit: Seq<u8>, dist: Seq<u8>) -> bool {
    zlib_ok(cl, true) && zlib_ok(lit, false) && zlib_ok(dist, false)
}

/// What a dynamic header's lengths must satisfy for the spec to accept them.
pub open spec fn hdr_lens_ok(lit: Seq<u8>, dist: Seq<u8>) -> bool {
    &&& lit.len() == 286 && dist.len() == 30 && lens_ok(lit) && lens_ok(dist)
    &&& lit[256] != 0 && not_oversub(lit) && not_oversub(dist)
}

/// What the code length code must be: a length of 1 to 7 for all 19
/// symbols, not over-subscribed.
pub open spec fn cl_good(cl: Seq<u8>) -> bool {
    cl.len() == 19 && not_oversub(cl) && forall|k: int| 0 <= k < 19 ==> 1 <= #[trigger] cl[k] <= 7
}

/// Write a dynamic block's header (after its 3 header bits): every stream
/// that starts with the bits written has it. `all` is the lengths, lit/length
/// then distance.
pub fn write_hdr(w: &mut BitW, clv: &Vec<u8>, clc: &EncCode, lit: &Vec<u8>, dist: &Vec<u8>, all: &Vec<u8>)
    requires
        old(w).wf(), old(w).buf@.len() + 4000 < 0x1000_0000_0000_0000 - 64,
        cl_good(clv@), enc_ok(clc, clv@), hdr_lens_ok(lit@, dist@), all@ == lit@ + dist@,
    ensures
        final(w).pre == old(w).pre,
        final(w).wf(), final(w).buf@.len() <= old(w).buf@.len() + 3300,
        final(w).bits().len() > old(w).bits().len(), is_prefix(old(w).bits(), final(w).bits()),
        forall|b: Seq<bool>| #[trigger] is_prefix(final(w).bits(), b) ==>
            (dyn_header(b, old(w).bits().len() as int) matches Some((l2, d2, q, st))
                && l2 == lit@ && d2 == dist@ && q == final(w).bits().len() && st == hdr_strict(clv@, lit@, dist@)),
{
    let ghost w0 = w.bits();
    let ghost p0 = w0.len() as int;
    proof { reveal_with_fuel(p2, 6); }
    put(w, 29, 5);
    let ghost w1 = w.bits();
    put(w, 29, 5);
    let ghost w2 = w.bits();
    put(w, 15, 4);
    let ghost w3 = w.bits();
    let ghost clq = clv@;
    // the code length code lengths, in their order
    let mut i: usize = 0;
    while i < 19
        invariant
            i <= 19, w.wf(), w.pre == old(w).pre, clv@ == clq, cl_good(clq), w3.len() == p0 + 14,
            w.buf@.len() <= old(w).buf@.len() + 15 + 5 * i,
            old(w).buf@.len() + 4000 < 0x1000_0000_0000_0000 - 64,
            w.bits().len() == w3.len() + 3 * i, is_prefix(w3, w.bits()),
            forall|b: Seq<bool>| #[trigger] is_prefix(w.bits(), b) ==>
                forall|j: nat| j < i ==> #[trigger] getbits(b, w3.len() as int + 3 * j, 3) == Some(clq[cl_order(j) as int] as nat),
        decreases 19 - i,
    {
        let k = cl_order_x(i as u64);
        let v = clv[k] as u64;
        proof { reveal_with_fuel(p2, 4); lemma_cl_inv2(i as nat); assert(v < 8); }
        let ghost wb = w.bits();
        put(w, v, 3);
        proof {
            assert forall|b: Seq<bool>| #[trigger] is_prefix(w.bits(), b) implies
                forall|j: nat| j < i + 1 ==> #[trigger] getbits(b, w3.len() as int + 3 * j, 3) == Some(clq[cl_order(j) as int] as nat) by {
                lemma_prefix_of_append(wb, wbits(v, 3), b);
                lemma_written_bits(v, 3, wb, b);
            }
            assert(is_prefix(w3, w.bits())) by { lemma_prefix_of_append(wb, wbits(v, 3), w.bits()); lemma_prefix_trans_b(w3, wb, w.bits()); }
        }
        i = i + 1;
    }
    let ghost w4 = w.bits();
    let ghost q4 = w4.len() as int;
    let ghost lens = lit@ + dist@;
    // the code lengths, as code length ops
    let mut j: usize = 0;
    proof {
        assert(lens.take(0) =~= Seq::<u8>::empty());
        assert(lens_ok(lens)) by {
            assert forall|m: int| 0 <= m < lens.len() implies #[trigger] lens[m] <= 15 by {
                if m < 286 { assert(lit@[m] <= 15); } else { assert(dist@[m - 286] <= 15); }
            }
        }
    }
    while j < 316
        invariant
            j <= 316, w.wf(), w.pre == old(w).pre, lens == lit@ + dist@, all@ == lens, lens.len() == 316, lens_ok(lens),
            clv@ == clq, cl_good(clq), enc_ok(clc, clq),
            w.buf@.len() <= old(w).buf@.len() + 110 + 10 * j,
            old(w).buf@.len() + 4000 < 0x1000_0000_0000_0000 - 64,
            is_prefix(w4, w.bits()), hdr_inv(w.bits(), clq, q4, lens, j as int),
        decreases 316 - j,
    {
        let (s, ex, rep) = next_op(all, j);
        let ghost wb = w.bits();
        emit_op(w, clc, Ghost(clq), Ghost(lens), Ghost(q4), j, s, ex, rep);
        proof { lemma_prefix_trans_b(w4, wb, w.bits()); }
        j = j + rep;
    }
    proof {
        let wf = w.bits();
        lemma_prefix_trans_b(w3, w4, wf);
        lemma_prefix_of_append(w2, wbits(15, 4), w3);
        lemma_prefix_of_append(w1, wbits(29, 5), w2);
        lemma_prefix_of_append(w0, wbits(29, 5), w1);
        lemma_prefix_trans_b(w0, w1, w2);
        lemma_prefix_trans_b(w0, w2, w3);
        lemma_prefix_trans_b(w0, w3, wf);
        assert(lens.take(316) =~= lens);
        assert forall|b: Seq<bool>| #[trigger] is_prefix(wf, b) implies
            (dyn_header(b, p0) matches Some((l2, d2, q, st)) && l2 == lit@ && d2 == dist@ && q == wf.len()
                && st == hdr_strict(clq, lit@, dist@)) by {
            lemma_prefix_trans_b(w4, wf, b);
            lemma_prefix_trans_b(w3, w4, b);
            lemma_prefix_trans_b(w3, wf, b);
            lemma_prefix_of_append(w2, wbits(15, 4), b);
            lemma_prefix_of_append(w1, wbits(29, 5), b);
            lemma_prefix_of_append(w0, wbits(29, 5), b);
            lemma_written_bits(29, 5, w0, b);
            lemma_written_bits(29, 5, w1, b);
            lemma_written_bits(15, 4, w2, b);
            assert(forall|jj: nat| jj < 19 ==> #[trigger] getbits(b, w3.len() as int + 3 * jj, 3) == Some(clq[cl_order(jj) as int] as nat));
            assert forall|k: int| 0 <= k < 19 implies #[trigger] clq[k] < 8 by {}
            assert(Seq::new(19, |_i: int| 0u8) =~= cl_acc(clq, 0));
            lemma_read_cl_written(b, w3.len() as int, clq, 0);
            assert(read_lens(clq, b, wf.len() as int, 316, lens) == Some((lens, wf.len() as int)));
            assert(lens.subrange(0, 286) =~= lit@);
            assert(lens.subrange(286, 316) =~= dist@);
            assert(w4.len() == w3.len() + 57);
        }
    }
}

pub proof fn lemma_prefix_trans_b(a: Seq<bool>, b: Seq<bool>, c: Seq<bool>)
    requires is_prefix(a, b), is_prefix(b, c),
    ensures is_prefix(a, c),
{
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i] == c[i] by {
        assert(a[i] == b[i]);
        assert(b[i] == c[i]);
    }
}

// ------------------------------------------------------------ blocks

/// Every stream that starts with the bits written decodes, from where the
/// writing is, the rest of the input after the input so far.
pub open spec fn str_inv(w: Seq<bool>, data: Seq<u8>, i: int, st: bool) -> bool {
    forall|b: Seq<bool>| #[trigger] is_prefix(w, b) ==>
        inflate_blocks(b, 0, Seq::empty(), true) == inflate_blocks(b, w.len() as int, data.take(i), st)
}

/// What follows the block written: the end, or the rest of the stream.
pub open spec fn str_after(w: Seq<bool>, data: Seq<u8>, i: int, st: bool, last: bool) -> bool {
    if last {
        forall|b: Seq<bool>| #[trigger] is_prefix(w, b) ==>
            inflate_blocks(b, 0, Seq::empty(), true) == Some((data.take(i), w.len() as int, st))
    } else {
        str_inv(w, data, i, st)
    }
}

/// A block's tokens and its end-of-block code.
fn write_syms(w: &mut BitW, lc: &EncCode, dc: &EncCode, Ghost(ll): Ghost<Seq<u8>>, Ghost(dl): Ghost<Seq<u8>>,
              Ghost(data): Ghost<Seq<u8>>, toks: &Vec<Tok>, Ghost(pos): Ghost<Seq<int>>, Ghost(i0): Ghost<int>)
    requires
        old(w).wf(), old(w).buf@.len() + 20 * toks@.len() + 40 < 0x1000_0000_0000_0000 - 64,
        enc_ok(lc, ll), enc_ok(dc, dl), ll.len() >= 286, dl.len() >= 30, 1 <= ll[256],
        toks_ok(data, toks@, pos), pos[0] == i0, i0 <= data.len(),
        forall|k: int| 0 <= k < toks@.len() ==> tok_coded(ll, dl, #[trigger] toks@[k]),
    ensures
        final(w).pre == old(w).pre,
        final(w).wf(), final(w).buf@.len() <= old(w).buf@.len() + 20 * toks@.len() + 20,
        final(w).bits().len() > old(w).bits().len(), is_prefix(old(w).bits(), final(w).bits()),
        forall|b: Seq<bool>| #[trigger] is_prefix(final(w).bits(), b) ==>
            inflate_syms(ll, dl, b, old(w).bits().len() as int, data.take(i0))
                == Some((data.take(pos[toks@.len() as int]), final(w).bits().len() as int)),
{
    let ghost q0 = w.bits().len() as int;
    let mut k: usize = 0;
    let ghost mut ip: int = i0;
    while k < toks.len()
        invariant
            k <= toks@.len(), w.wf(), w.pre == old(w).pre, enc_ok(lc, ll), enc_ok(dc, dl), ll.len() >= 286, dl.len() >= 30,
            toks_ok(data, toks@, pos),
            forall|k: int| 0 <= k < toks@.len() ==> tok_coded(ll, dl, #[trigger] toks@[k]),
            w.buf@.len() <= old(w).buf@.len() + 20 * k,
            old(w).buf@.len() + 20 * toks@.len() + 40 < 0x1000_0000_0000_0000 - 64,
            ip == pos[k as int], ip <= data.len(), w.bits().len() >= q0,
            is_prefix(old(w).bits(), w.bits()), old(w).bits().len() == q0,
            blk_inv(w.bits(), ll, dl, q0, data, i0, ip),
        decreases toks@.len() - k,
    {
        let t = toks[k];
        proof { assert(tok_ok(data, pos[k as int], toks@[k as int])); }
        let ghost wk = w.bits();
        emit_tok(w, lc, dc, Ghost(ll), Ghost(dl), Ghost(data), Ghost(ip), t, Ghost(q0), Ghost(i0));
        proof { lemma_prefix_trans_b(old(w).bits(), wk, w.bits()); }
        proof { ip = ip + if t.len == 0 { 1 } else { t.len as int }; }
        k = k + 1;
    }
    let ghost w0 = w.bits();
    proof { assert(ll[256] <= 15); }
    let l = lc.lens[256] as u64;
    put(w, lc.rc[256], l);
    proof {
        let wf = w.bits();
        let p = w0.len() as int;
        assert forall|b: Seq<bool>| #[trigger] is_prefix(wf, b) implies
            inflate_syms(ll, dl, b, q0, data.take(i0))
                == Some((data.take(pos[toks@.len() as int]), wf.len() as int)) by {
            lemma_prefix_of_append(w0, wbits(lc.rc@[256], l as nat), b);
            lemma_written_sym(ll, lc, 256, w0, b);
            assert(sym_step(ll, dl, b, p) == Some(Step::End(wf.len() as int)));
            lemma_syms_unfold(ll, dl, b, p, data.take(ip));
        }
        lemma_prefix_of_append(w0, wbits(lc.rc@[256], l as nat), wf);
        lemma_prefix_trans_b(old(w).bits(), w0, wf);
    }
}

/// A dynamic block: its header bits, header, tokens and end.
#[verifier::spinoff_prover]
fn write_block_dyn(w: &mut BitW, clv: &Vec<u8>, clc: &EncCode, lc: &EncCode, dc: &EncCode, lit: &Vec<u8>, dist: &Vec<u8>,
                   all: &Vec<u8>, Ghost(data): Ghost<Seq<u8>>, toks: &Vec<Tok>, Ghost(pos): Ghost<Seq<int>>, Ghost(i0): Ghost<int>, last: bool,
                   Ghost(st): Ghost<bool>) -> (st2: Ghost<bool>)
    requires
        old(w).wf(), old(w).buf@.len() + 20 * toks@.len() + 4500 < 0x1000_0000_0000_0000 - 64,
        cl_good(clv@), enc_ok(clc, clv@), all@ == lit@ + dist@,
        hdr_lens_ok(lit@, dist@), enc_ok(lc, lit@), enc_ok(dc, dist@),
        toks_ok(data, toks@, pos), pos[0] == i0, i0 <= data.len(),
        forall|k: int| 0 <= k < toks@.len() ==> tok_coded(lit@, dist@, #[trigger] toks@[k]),
        str_inv(old(w).bits(), data, i0, st),
    ensures
        final(w).pre == old(w).pre,
        final(w).wf(), final(w).buf@.len() <= old(w).buf@.len() + 20 * toks@.len() + 3400,
        str_after(final(w).bits(), data, pos[toks@.len() as int], st2@, last),
        st2@ == (st && hdr_strict(clv@, lit@, dist@)),
{
    let ghost w0 = w.bits();
    let ghost p = w0.len() as int;
    let bf: u64 = if last { 1 } else { 0 };
    proof { reveal_with_fuel(p2, 3); }
    put(w, bf, 1);
    let ghost w1 = w.bits();
    put(w, 2, 2);
    let ghost w2 = w.bits();
    write_hdr(w, clv, clc, lit, dist, all);
    let ghost w3 = w.bits();
    write_syms(w, lc, dc, Ghost(lit@), Ghost(dist@), Ghost(data), toks, Ghost(pos), Ghost(i0));
    let ghost st2 = st && hdr_strict(clv@, lit@, dist@);
    proof {
        let wf = w.bits();
        let i1 = pos[toks@.len() as int];
        lemma_prefix_of_append(w1, wbits(2, 2), w2);
        lemma_prefix_of_append(w0, wbits(bf, 1), w1);
        lemma_prefix_trans_b(w0, w1, w2);
        lemma_prefix_trans_b(w2, w3, wf);
        lemma_prefix_trans_b(w0, w2, wf);
        assert forall|b: Seq<bool>| #[trigger] is_prefix(wf, b) implies
            inflate_blocks(b, 0, Seq::empty(), true) == after_blk(b, p, data.take(i1), wf.len() as int, last, st2) by {
            lemma_prefix_trans_b(w0, wf, b);
            lemma_prefix_trans_b(w2, wf, b);
            lemma_prefix_trans_b(w3, wf, b);
            lemma_prefix_trans_b(w1, w2, b);
            lemma_prefix_of_append(w1, wbits(2, 2), b);
            lemma_prefix_of_append(w0, wbits(bf, 1), b);
            lemma_written_bits(bf, 1, w0, b);
            lemma_written_bits(2, 2, w1, b);
            assert(is_prefix(w3, b));
            crate::stream::lemma_hdr(b, p, data.take(i0), st, bf as nat, 2);
        }
    }
    proof { lemma_after_blk(w.bits(), data, pos[toks@.len() as int], st2, last, p); }
    Ghost(st2)
}

/// A fixed-code block.
fn write_block_fixed(w: &mut BitW, fl: &EncCode, fd: &EncCode, Ghost(data): Ghost<Seq<u8>>, toks: &Vec<Tok>,
                     Ghost(pos): Ghost<Seq<int>>, Ghost(i0): Ghost<int>, last: bool, Ghost(st): Ghost<bool>) -> (st2: Ghost<bool>)
    requires
        old(w).wf(), old(w).buf@.len() + 20 * toks@.len() + 2500 < 0x1000_0000_0000_0000 - 64,
        enc_ok(fl, fixed_lit()), enc_ok(fd, fixed_dist()),
        toks_ok(data, toks@, pos), pos[0] == i0, i0 <= data.len(),
        str_inv(old(w).bits(), data, i0, st),
    ensures
        final(w).pre == old(w).pre,
        final(w).wf(), final(w).buf@.len() <= old(w).buf@.len() + 20 * toks@.len() + 30,
        str_after(final(w).bits(), data, pos[toks@.len() as int], st2@, last), st2@ == st,
{
    let ghost w0 = w.bits();
    let ghost p = w0.len() as int;
    let bf: u64 = if last { 1 } else { 0 };
    proof {
        reveal_with_fuel(p2, 3);
        assert forall|k: int| 0 <= k < toks@.len() implies tok_coded(fixed_lit(), fixed_dist(), #[trigger] toks@[k]) by {
            assert(tok_ok(data, pos[k], toks@[k]));
        }
    }
    put(w, bf, 1);
    let ghost w1 = w.bits();
    put(w, 1, 2);
    let ghost w2 = w.bits();
    write_syms(w, fl, fd, Ghost(fixed_lit()), Ghost(fixed_dist()), Ghost(data), toks, Ghost(pos), Ghost(i0));
    let ghost st2 = st && true;
    proof {
        let wf = w.bits();
        let i1 = pos[toks@.len() as int];
        lemma_prefix_of_append(w1, wbits(1, 2), w2);
        lemma_prefix_of_append(w0, wbits(bf, 1), w1);
        lemma_prefix_trans_b(w0, w1, w2);
        lemma_prefix_trans_b(w0, w2, wf);
        assert forall|b: Seq<bool>| #[trigger] is_prefix(wf, b) implies
            inflate_blocks(b, 0, Seq::empty(), true) == after_blk(b, p, data.take(i1), wf.len() as int, last, st2) by {
            lemma_prefix_trans_b(w0, wf, b);
            lemma_prefix_trans_b(w2, wf, b);
            lemma_prefix_trans_b(w1, w2, b);
            lemma_prefix_of_append(w1, wbits(1, 2), b);
            lemma_prefix_of_append(w0, wbits(bf, 1), b);
            lemma_written_bits(bf, 1, w0, b);
            lemma_written_bits(1, 2, w1, b);
            crate::stream::lemma_hdr(b, p, data.take(i0), st, bf as nat, 1);
        }
    }
    proof { lemma_after_blk(w.bits(), data, pos[toks@.len() as int], st2, last, p); }
    Ghost(st2)
}

fn put16(w: &mut BitW, v: u64)
    requires old(w).wf(), v < 65536, old(w).buf@.len() + 8 < 0x1000_0000_0000_0000,
    ensures final(w).wf(), final(w).bits() == old(w).bits() + wbits(v, 16),
        final(w).buf@.len() <= old(w).buf@.len() + 5, final(w).pre == old(w).pre,
{
    proof { reveal_with_fuel(p2, 17); }
    put(w, v, 16);
}

proof fn lemma_align8(m: nat, na: nat)
    requires na < 8,
    ensures align8((8 * m + na) as int) == 8 * m + na + (8 - na) % 8,
{
    assert((8 * m + na) % 8 == na) by (nonlinear_arith) requires na < 8;
}

proof fn lemma_head_bits(w0: Seq<bool>, w1: Seq<bool>, w2: Seq<bool>, w3: Seq<bool>, w4: Seq<bool>, wf: Seq<bool>,
                         b: Seq<bool>, bf: u64, k: u64, n: u64)
    requires
        w1 == w0 + wbits(bf, 1), w2 == w1 + wbits(0, 2), w3 == w2 + wbits(0, k as nat), w4 == w3 + wbits(n, 16),
        wf == w4 + wbits((65535 - n) as u64, 16), is_prefix(wf, b), bf < 2, k <= 7, n < 65536,
    ensures
        getbits(b, w0.len() as int, 1) == Some(bf as nat), getbits(b, w1.len() as int, 2) == Some(0nat),
        getbits(b, w3.len() as int, 16) == Some(n as nat), getbits(b, w4.len() as int, 16) == Some((65535 - n) as nat),
{
    reveal_with_fuel(p2, 17);
    lemma_prefix_of_append(w4, wbits((65535 - n) as u64, 16), b);
    lemma_prefix_of_append(w3, wbits(n, 16), w4);
    lemma_prefix_trans_b(w4, wf, b);
    lemma_prefix_trans_b(w3, w4, b);
    lemma_prefix_of_append(w3, wbits(n, 16), b);
    lemma_prefix_of_append(w2, wbits(0, k as nat), w3);
    lemma_prefix_trans_b(w2, w3, b);
    lemma_prefix_of_append(w1, wbits(0, 2), w2);
    lemma_prefix_trans_b(w1, w2, b);
    lemma_prefix_of_append(w1, wbits(0, 2), b);
    lemma_prefix_of_append(w0, wbits(bf, 1), w1);
    lemma_prefix_trans_b(w0, w1, b);
    lemma_prefix_of_append(w0, wbits(bf, 1), b);
    lemma_written_bits(bf, 1, w0, b);
    lemma_written_bits(0, 2, w1, b);
    lemma_written_bits(n, 16, w3, b);
    lemma_written_bits((65535 - n) as u64, 16, w4, b);
}

/// A stored block's header: BFINAL, BTYPE 0, zeros to the next byte, LEN
/// and NLEN.
#[verifier::spinoff_prover]
fn stored_head(w: &mut BitW, n: u64, last: bool)
    requires old(w).wf(), old(w).buf@.len() + 50 < 0x1000_0000_0000_0000 - 64, n <= 65535,
    ensures
        final(w).pre == old(w).pre, final(w).wf(), final(w).buf@.len() <= old(w).buf@.len() + 25,
        is_prefix(old(w).bits(), final(w).bits()),
        final(w).bits().len() == align8(old(w).bits().len() as int + 3) + 32,
        forall|b: Seq<bool>| #[trigger] is_prefix(final(w).bits(), b) ==>
            getbits(b, old(w).bits().len() as int, 1) == Some(if last { 1nat } else { 0nat })
            && getbits(b, old(w).bits().len() as int + 1, 2) == Some(0nat)
            && getbits(b, align8(old(w).bits().len() as int + 3), 16) == Some(n as nat)
            && getbits(b, align8(old(w).bits().len() as int + 3) + 16, 16) == Some((65535 - n) as nat),
{
    let ghost w0 = w.bits();
    let ghost p = w0.len() as int;
    let bf: u64 = if last { 1 } else { 0 };
    proof { reveal_with_fuel(p2, 4); }
    put(w, bf, 1);
    let ghost w1 = w.bits();
    put(w, 0, 2);
    let ghost w2 = w.bits();
    let na = w.nacc;
    let k: u64 = (8 - na) % 8;
    proof {
        let m = (w.pre@ + w.buf@).len();
        assert(w2.len() == 8 * m + na);
        lemma_align8(m, na as nat);
        assert(p2(k as nat) >= 1) by { reveal_with_fuel(p2, 9); }
    }
    put(w, 0, k);
    let ghost w3 = w.bits();
    put16(w, n);
    let ghost w4 = w.bits();
    put16(w, 65535 - n);
    proof {
        let wf = w.bits();
        assert(is_prefix(w0, wf)) by {
            assert forall|i: int| 0 <= i < w0.len() implies #[trigger] w0[i] == wf[i] by {
                assert(wf == w0 + wbits(bf, 1) + wbits(0, 2) + wbits(0, k as nat) + wbits(n, 16) + wbits((65535 - n) as u64, 16));
            }
        }
        assert forall|b: Seq<bool>| #[trigger] is_prefix(wf, b) implies
            getbits(b, p, 1) == Some(if last { 1nat } else { 0nat }) && getbits(b, p + 1, 2) == Some(0nat)
            && getbits(b, align8(p + 3), 16) == Some(n as nat)
            && getbits(b, align8(p + 3) + 16, 16) == Some((65535 - n) as nat) by {
            lemma_head_bits(w0, w1, w2, w3, w4, wf, b, bf, k, n);
        }
    }
}

/// The bytes of `src`, eight bits each.
fn put_bytes(w: &mut BitW, src: &[u8])
    requires old(w).wf(), old(w).buf@.len() + 5 * src@.len() + 50 < 0x1000_0000_0000_0000 - 64,
    ensures
        final(w).pre == old(w).pre, final(w).wf(), final(w).buf@.len() <= old(w).buf@.len() + 5 * src@.len(),
        is_prefix(old(w).bits(), final(w).bits()), final(w).bits().len() == old(w).bits().len() + 8 * src@.len(),
        forall|b: Seq<bool>| #[trigger] is_prefix(final(w).bits(), b) ==>
            bytes_at(b, old(w).bits().len() as int, src@.len()) == src@,
{
    let ghost w5 = w.bits();
    let mut j: usize = 0;
    proof { reveal_with_fuel(p2, 9); }
    while j < src.len()
        invariant
            j <= src@.len(), w.wf(), w.pre == old(w).pre, p2(8) == 256,
            w.buf@.len() <= old(w).buf@.len() + 5 * j,
            old(w).buf@.len() + 5 * src@.len() + 50 < 0x1000_0000_0000_0000 - 64,
            w.bits().len() == w5.len() + 8 * j, is_prefix(w5, w.bits()), w5 == old(w).bits(),
            forall|b: Seq<bool>| #[trigger] is_prefix(w.bits(), b) ==>
                forall|m: nat| m < j ==> #[trigger] getbits(b, w5.len() as int + 8 * m, 8) == Some(src@[m as int] as nat),
        decreases src@.len() - j,
    {
        let x = src[j] as u64;
        let ghost wb = w.bits();
        put(w, x, 8);
        proof {
            assert forall|b: Seq<bool>| #[trigger] is_prefix(w.bits(), b) implies
                forall|m: nat| m < j + 1 ==> #[trigger] getbits(b, w5.len() as int + 8 * m, 8) == Some(src@[m as int] as nat) by {
                lemma_prefix_of_append(wb, wbits(x, 8), b);
                lemma_written_bits(x, 8, wb, b);
            }
            assert(is_prefix(w5, w.bits())) by { lemma_prefix_of_append(wb, wbits(x, 8), w.bits()); lemma_prefix_trans_b(w5, wb, w.bits()); }
        }
        j = j + 1;
    }
    proof {
        assert forall|b: Seq<bool>| #[trigger] is_prefix(w.bits(), b) implies bytes_at(b, w5.len() as int, src@.len()) == src@ by {
            assert forall|m: int| 0 <= m < src@.len() implies #[trigger] bytes_at(b, w5.len() as int, src@.len())[m] == src@[m] by {
                assert(getbits(b, w5.len() as int + 8 * (m as nat), 8) == Some(src@[m] as nat));
            }
            assert(bytes_at(b, w5.len() as int, src@.len()) =~= src@);
        }
    }
}

proof fn lemma_stored_block(b: Seq<bool>, p: int, last: bool, n: nat, src: Seq<u8>, g: Seq<u8>, st: bool)
    requires
        0 <= p, getbits(b, p, 1) == Some(if last { 1nat } else { 0nat }), getbits(b, p + 1, 2) == Some(0nat),
        getbits(b, align8(p + 3), 16) == Some(n), getbits(b, align8(p + 3) + 16, 16) == Some((65535 - n) as nat), n <= 65535,
        src.len() == n, align8(p + 3) + 32 + 8 * n <= b.len(), bytes_at(b, align8(p + 3) + 32, n) == src,
    ensures inflate_blocks(b, p, g, st) == crate::stream::after_block(b, p, g + src, align8(p + 3) + 32 + 8 * n, last, st),
{
    crate::stream::lemma_hdr(b, p, g, st, if last { 1nat } else { 0nat }, 0);
    lemma_stored_unfold(b, p + 3);
    assert(stored_hdr(b, p + 3) == Some((n, align8(p + 3) + 32)));
}

/// A stored block of the bytes `src` (at most 65535), the input from `i0`.
#[verifier::spinoff_prover]
fn write_block_stored(w: &mut BitW, src: &[u8], Ghost(data): Ghost<Seq<u8>>, Ghost(i0): Ghost<int>, last: bool,
                      Ghost(st): Ghost<bool>) -> (st2: Ghost<bool>)
    requires
        old(w).wf(), old(w).buf@.len() + 5 * src@.len() + 100 < 0x1000_0000_0000_0000 - 64, src@.len() <= 65535,
        0 <= i0, i0 + src@.len() <= data.len(), src@ == data.subrange(i0, i0 + src@.len()),
        str_inv(old(w).bits(), data, i0, st),
    ensures
        final(w).pre == old(w).pre,
        final(w).wf(), final(w).buf@.len() <= old(w).buf@.len() + 5 * src@.len() + 50,
        str_after(final(w).bits(), data, i0 + src@.len(), st2@, last), st2@ == st,
{
    let ghost w0 = w.bits();
    let ghost p = w0.len() as int;
    let n = src.len() as u64;
    stored_head(w, n, last);
    let ghost w5 = w.bits();
    put_bytes(w, src);
    let ghost i1 = i0 + src@.len();
    let ghost st2 = st && true;
    proof {
        let wf = w.bits();
        lemma_prefix_trans_b(w0, w5, wf);
        assert forall|b: Seq<bool>| #[trigger] is_prefix(wf, b) implies
            inflate_blocks(b, 0, Seq::empty(), true) == after_blk(b, p, data.take(i1), wf.len() as int, last, st2) by {
            lemma_prefix_trans_b(w0, wf, b);
            lemma_prefix_trans_b(w5, wf, b);
            lemma_stored_block(b, p, last, n as nat, src@, data.take(i0), st);
            assert(data.take(i0) + src@ =~= data.take(i1));
        }
    }
    proof { lemma_after_blk(w.bits(), data, i1, st2, last, p); }
    Ghost(st2)
}

/// What follows a block that ended at `q`, as `after_block` puts it.
pub open spec fn after_blk(b: Seq<bool>, p: int, o: Seq<u8>, q: int, last: bool, s: bool) -> Option<(Seq<u8>, int, bool)> {
    crate::stream::after_block(b, p, o, q, last, s)
}

proof fn lemma_after_blk(w: Seq<bool>, data: Seq<u8>, i1: int, st2: bool, last: bool, p: int)
    requires
        p < w.len(),
        forall|b: Seq<bool>| #[trigger] is_prefix(w, b) ==>
            inflate_blocks(b, 0, Seq::empty(), true) == after_blk(b, p, data.take(i1), w.len() as int, last, st2),
    ensures str_after(w, data, i1, st2, last),
{
    assert forall|b: Seq<bool>| #[trigger] is_prefix(w, b) implies
        (if last { inflate_blocks(b, 0, Seq::empty(), true) == Some((data.take(i1), w.len() as int, st2)) }
         else { inflate_blocks(b, 0, Seq::empty(), true) == inflate_blocks(b, w.len() as int, data.take(i1), st2) }) by {
        assert(b.len() >= w.len());
    }
}

// ------------------------------------------------------- code lengths

/// Code lengths for these frequencies: Shannon lengths, capped at 15 and
/// lengthened until the Kraft sum fits, then shortened, most frequent
/// first, while it allows. Nothing here is relied on: the lengths are
/// checked before they are used.
/// Huffman code lengths for `freq` (depths in the Huffman tree, built by
/// merging the two lightest nodes, O(n^2) for n <= 320), clamped to 1..15
/// for the symbols that occur; `heur_lens` repairs the Kraft sum after.
fn huff_depths(freq: &Vec<u32>, maxl: u8) -> (lens: Vec<u8>)
    requires freq@.len() <= 320, 1 <= maxl <= 15,
    ensures lens@.len() == freq@.len(), forall|t: int| 0 <= t < lens@.len() ==> #[trigger] lens@[t] <= maxl,
{
    let n = freq.len();
    let m = 2 * n;
    let mut w: Vec<u64> = vec![0u64; m];
    let mut par: Vec<usize> = vec![m; m];
    let mut live: Vec<bool> = vec![false; m];
    let mut s: usize = 0;
    while s < n
        invariant s <= n, n == freq@.len(), n <= 320, m == 2 * n, w@.len() == m, live@.len() == m,
            forall|t: int| 0 <= t < m ==> #[trigger] w@[t] <= 640 * 0x1_0000_0000,
        decreases n - s,
    {
        if freq[s] > 0 {
            w.set(s, freq[s] as u64);
            live.set(s, true);
        }
        s = s + 1;
    }
    let mut nn = n;
    while nn < m
        invariant n <= nn <= m, m == 2 * n, n <= 320, w@.len() == m, par@.len() == m, live@.len() == m,
            forall|t: int| 0 <= t < m ==> #[trigger] w@[t] <= 640 * 0x1_0000_0000,
        decreases m - nn,
    {
        // the two lightest live nodes
        let mut a: usize = m;
        let mut b: usize = m;
        let mut t: usize = 0;
        while t < nn
            invariant t <= nn, nn <= m, w@.len() == m, live@.len() == m, a <= m, b <= m, a < m ==> a < t, b < m ==> b < t, b < m ==> a < m,
            decreases nn - t,
        {
            if live[t] {
                if a == m || w[t] < w[a] {
                    b = a;
                    a = t;
                } else if b == m || w[t] < w[b] {
                    b = t;
                }
            }
            t = t + 1;
        }
        if b == m {
            break;
        }
        live.set(a, false);
        live.set(b, false);
        let wa = w[a];
        let wb = w[b];
        let s2 = if wa + wb > 640 * 0x1_0000_0000 { 640 * 0x1_0000_0000 } else { wa + wb };
        w.set(nn, s2);
        live.set(nn, true);
        par.set(a, nn);
        par.set(b, nn);
        nn = nn + 1;
    }
    let mut lens: Vec<u8> = Vec::with_capacity(n);
    let mut s: usize = 0;
    while s < n
        invariant s <= n, n == freq@.len(), m == 2 * n, par@.len() == m, lens@.len() == s,
            forall|t: int| 0 <= t < s ==> #[trigger] lens@[t] <= maxl, 1 <= maxl <= 15,
        decreases n - s,
    {
        let mut l: u8 = 0;
        if freq[s] > 0 {
            let mut x = s;
            let mut d: usize = 0;
            while par[x] < m && d < m
                invariant x < m, par@.len() == m, d <= m,
                decreases m - d,
            {
                x = par[x];
                d = d + 1;
            }
            l = if d == 0 { 1 } else if d > maxl as usize { maxl } else { d as u8 };
        }
        lens.push(l);
        s = s + 1;
    }
    lens
}

pub fn heur_lens(freq: &Vec<u32>, maxl: u8) -> (lens: Vec<u8>)
    requires freq@.len() <= 320, 1 <= maxl <= 15,
    ensures lens@.len() == freq@.len(), lens_ok(lens@), forall|t: int| 0 <= t < lens@.len() ==> #[trigger] lens@[t] <= maxl,
{
    let n = freq.len();
    let mut total: u64 = 0;
    let mut s: usize = 0;
    while s < n
        invariant s <= n, n == freq@.len(), n <= 320, total <= s * 0x1_0000_0000,
        decreases n - s,
    {
        total = total + freq[s] as u64;
        s = s + 1;
    }
    let mut lens = huff_depths(freq, maxl);
    // lengthen the rarest until the lengths are not over-subscribed
    let mut guard: usize = 0;
    while guard < 5000 && kraft_sum(&lens) > 32768
        invariant lens@.len() == n, n == freq@.len(), n <= 320, forall|t: int| 0 <= t < n ==> #[trigger] lens@[t] <= maxl, 1 <= maxl <= 15,
        decreases 5000 - guard,
    {
        let mut best: usize = n;
        let mut s: usize = 0;
        while s < n
            invariant s <= n, lens@.len() == n, n == freq@.len(), best <= n,
            decreases n - s,
        {
            if lens[s] >= 1 && lens[s] < maxl && (best == n || freq[s] < freq[best]) {
                best = s;
            }
            s = s + 1;
        }
        if best == n {
            break;
        }
        let v = lens[best];
        if v < maxl {
            lens.set(best, v + 1);
        }
        guard = guard + 1;
    }
    // shorten the most frequent while the Kraft sum allows
    let mut done: Vec<bool> = vec![false; n];
    let mut round: usize = 0;
    while round < n
        invariant lens@.len() == n, done@.len() == n, n == freq@.len(), round <= n, n <= 320,
            forall|t: int| 0 <= t < n ==> #[trigger] lens@[t] <= maxl, 1 <= maxl <= 15,
        decreases n - round,
    {
        let mut best: usize = n;
        let mut s: usize = 0;
        while s < n
            invariant s <= n, lens@.len() == n, done@.len() == n, n == freq@.len(), best <= n,
            decreases n - s,
        {
            if !done[s] && lens[s] >= 1 && (best == n || freq[s] > freq[best]) {
                best = s;
            }
            s = s + 1;
        }
        if best == n {
            break;
        }
        done.set(best, true);
        let mut k = kraft_sum(&lens);
        let mut g: usize = 0;
        while g < 15 && lens[best] > 1
            invariant lens@.len() == n, n == freq@.len(), best < n, g <= 15, k <= 320 * 32768, n <= 320,
                forall|t: int| 0 <= t < n ==> #[trigger] lens@[t] <= maxl, 1 <= maxl <= 15,
            decreases 15 - g,
        {
            let v = lens[best];
            let e: u64 = 15 - v as u64;
            assert((1u64 << e) <= 16384) by (bit_vector) requires e <= 13;
            if k + (1u64 << e) > 32768 {
                break;
            }
            k = k + (1u64 << e);
            lens.set(best, v - 1);
            g = g + 1;
        }
        round = round + 1;
    }
    // fill what is left of the Kraft sum, so that the code is complete (as
    // zlib wants): shortening a longest code adds the least, and the slack
    // is a multiple of that
    let mut guard: usize = 0;
    while guard < 5000
        invariant lens@.len() == n, n == freq@.len(), n <= 320,
            forall|t: int| 0 <= t < n ==> #[trigger] lens@[t] <= maxl, 1 <= maxl <= 15,
        decreases 5000 - guard,
    {
        let k = kraft_sum(&lens);
        if k >= 32768 {
            break;
        }
        let mut best: usize = n;
        let mut s: usize = 0;
        while s < n
            invariant s <= n, lens@.len() == n, n == freq@.len(), best <= n,
                best < n ==> lens@[best as int] >= 2,
            decreases n - s,
        {
            if lens[s] >= 2 && (best == n || lens[s] > lens[best]) {
                best = s;
            }
            s = s + 1;
        }
        if best == n {
            break;
        }
        let v = lens[best];
        let e: u64 = 15 - v as u64;
        assert((1u64 << e) <= 16384) by (bit_vector) requires e <= 13;
        if k + (1u64 << e) > 32768 {
            break;
        }
        lens.set(best, v - 1);
        guard = guard + 1;
    }
    lens
}

/// The Kraft sum of lengths, in units of 2^-15 (for `heur_lens`).
fn kraft_sum(lens: &Vec<u8>) -> (k: u64)
    requires lens@.len() <= 320, forall|t: int| 0 <= t < lens@.len() ==> #[trigger] lens@[t] <= 15,
    ensures k <= 320 * 32768,
{
    let mut k: u64 = 0;
    let mut s: usize = 0;
    while s < lens.len()
        invariant s <= lens@.len(), lens@.len() <= 320, k <= s * 32768,
            forall|t: int| 0 <= t < lens@.len() ==> #[trigger] lens@[t] <= 15,
        decreases lens@.len() - s,
    {
        let l = lens[s] as u64;
        if l >= 1 {
            let e: u64 = 15 - l;
            assert((1u64 << e) <= 16384) by (bit_vector) requires e <= 14;
            k = k + (1u64 << e);
        }
        s = s + 1;
    }
    k
}

/// The block's lengths are usable: the spec accepts them, and they code
/// every symbol the block uses.
fn lens_usable(lit: &Vec<u8>, dist: &Vec<u8>, toks: &Vec<Tok>, Ghost(data): Ghost<Seq<u8>>, Ghost(pos): Ghost<Seq<int>>) -> (ok: bool)
    requires lit@.len() == 286, dist@.len() == 30, lens_ok(lit@), lens_ok(dist@), toks_ok(data, toks@, pos),
    ensures ok ==> hdr_lens_ok(lit@, dist@) && forall|k: int| 0 <= k < toks@.len() ==> tok_coded(lit@, dist@, #[trigger] toks@[k]),
{
    if lit[256] == 0 || kraft_x(lit.as_slice()) > 32768 || kraft_x(dist.as_slice()) > 32768 {
        return false;
    }
    proof { reveal_with_fuel(p2, 16); }
    let mut k: usize = 0;
    while k < toks.len()
        invariant k <= toks@.len(), lit@.len() == 286, dist@.len() == 30, toks_ok(data, toks@, pos),
            forall|j: int| 0 <= j < k ==> tok_coded(lit@, dist@, #[trigger] toks@[j]),
        decreases toks@.len() - k,
    {
        let t = toks[k];
        proof { assert(tok_ok(data, pos[k as int], toks@[k as int])); }
        if t.len == 0 {
            if lit[t.lit as usize] == 0 { return false; }
        } else {
            if lit[t.ls as usize] == 0 || dist[t.ds as usize] == 0 { return false; }
        }
        k = k + 1;
    }
    true
}

// ------------------------------------------------------------- deflate

/// `o` is a DEFLATE stream of `data` that ends in its last byte: every
/// stream that starts with it decodes to `data`, in `q` bits, and zlib
/// accepts it (the spec's flag is on).
pub open spec fn deflate_ok(data: Seq<u8>, o: Seq<u8>) -> bool {
    exists|q: nat| #![trigger inflate_q(o, q, true)] inflate_q(o, q, true) && (q + 7) / 8 == o.len()
        && forall|b: Seq<bool>| #[trigger] is_prefix(lbits(o), b) ==> inflate(b) == Some((data, q, true))
}

pub open spec fn inflate_q(o: Seq<u8>, q: nat, st: bool) -> bool { true }

/// In particular it decodes to `data` itself.
pub proof fn lemma_deflate_ok(data: Seq<u8>, o: Seq<u8>)
    requires deflate_ok(data, o),
    ensures inflate(lbits(o)) matches Some((d, _, _)) && d == data,
{
    let q = choose|q: nat| #![trigger inflate_q(o, q, true)] inflate_q(o, q, true) && (q + 7) / 8 == o.len()
        && forall|b: Seq<bool>| #[trigger] is_prefix(lbits(o), b) ==> inflate(b) == Some((data, q, true));
    assert(is_prefix(lbits(o), lbits(o)));
}

/// Compress `data`: blocks of up to 32768 tokens, each with its own codes
/// (or the fixed ones, where its own would not do). The result is what the
/// spec decodes to `data` (`None` only if a fixed code did not fit its
/// lengths, which they do).
/// Lit/length then distance lengths.
fn concat_lens(lit: &Vec<u8>, dist: &Vec<u8>) -> (v: Vec<u8>)
    ensures v@ == lit@ + dist@,
{
    let mut v = lit.clone();
    let mut k: usize = 0;
    while k < dist.len()
        invariant k <= dist@.len(), v@ == lit@ + dist@.take(k as int),
        decreases dist@.len() - k,
    {
        v.push(dist[k]);
        k = k + 1;
        proof { assert(v@ =~= lit@ + dist@.take(k as int)); }
    }
    proof { assert(dist@.take(dist@.len() as int) =~= dist@); }
    v
}

/// The code length code for writing `all` (from the ops' counts, every
/// symbol given at least a count of 1, lengths up to 7), and the header's
/// size in bits with it.
fn cl_plan(all: &Vec<u8>) -> (r: (Vec<u8>, u64))
    requires all@.len() <= 320, lens_ok(all@),
    ensures r.0@.len() == 19, lens_ok(r.0@), forall|k: int| 0 <= k < 19 ==> #[trigger] r.0@[k] <= 7, r.1 <= 50000,
{
    let n = all.len();
    let mut f: Vec<u32> = vec![0u32; 19];
    let mut xb: u64 = 0;
    let mut j: usize = 0;
    while j < n
        invariant j <= n, n == all@.len(), n <= 320, lens_ok(all@), f@.len() == 19, xb <= 7 * j,
            forall|k: int| 0 <= k < 19 ==> #[trigger] f@[k] <= j,
        decreases n - j,
    {
        let (s, _ex, rep) = next_op(all, j);
        let x = s as usize;
        f.set(x, f[x] + 1);
        xb = xb + if s == 16 { 2 } else if s == 17 { 3 } else if s == 18 { 7 } else { 0 };
        j = j + rep;
    }
    let mut g: Vec<u32> = f.clone();
    let mut k: usize = 0;
    while k < 19
        invariant k <= 19, g@.len() == 19,
        decreases 19 - k,
    {
        if g[k] == 0 { g.set(k, 1); }
        k = k + 1;
    }
    let clv = heur_lens(&g, 7);
    let mut hb: u64 = 14 + 57 + xb;
    let mut k: usize = 0;
    assert(hb <= 71 + 2240);
    while k < 19
        invariant k <= 19, clv@.len() == 19, f@.len() == 19, hb <= 2311 + 2240 * k,
            forall|t: int| 0 <= t < 19 ==> #[trigger] clv@[t] <= 7,
            forall|t: int| 0 <= t < 19 ==> #[trigger] f@[t] <= 320,
        decreases 19 - k,
    {
        let a = f[k] as u64;
        let b = clv[k] as u64;
        assert(a * b <= 320 * 7) by (nonlinear_arith) requires a <= 320, b <= 7;
        hb = hb + a * b;
        k = k + 1;
    }
    assert(hb <= 2311 + 2240 * 19);
    (clv, hb)
}

/// `cl_good`, checked.
fn cl_good_x(clv: &Vec<u8>) -> (ok: bool)
    requires clv@.len() == 19, lens_ok(clv@),
    ensures ok ==> cl_good(clv@),
{
    let mut k: usize = 0;
    while k < 19
        invariant k <= 19, clv@.len() == 19, forall|t: int| 0 <= t < k ==> 1 <= #[trigger] clv@[t] <= 7,
        decreases 19 - k,
    {
        if clv[k] < 1 || clv[k] > 7 { return false; }
        k = k + 1;
    }
    proof { reveal_with_fuel(p2, 16); }
    kraft_x(clv.as_slice()) <= 32768
}

/// The bits of the block's symbols with these lengths and the header
/// (`hbits` bits), and with the fixed codes, besides the extra bits (the same
/// either way); the dynamic header bits take fewer bits than with the fixed codes (the extra bits are the
/// same either way).
fn block_bits(lf: &Vec<u32>, df: &Vec<u32>, lit: &Vec<u8>, dist: &Vec<u8>, hbits: u64) -> (r: (u64, u64))
    requires lf@.len() == 286, df@.len() == 30, lit@.len() == 286, dist@.len() == 30,
        forall|s: int| 0 <= s < 286 ==> #[trigger] lf@[s] <= 32769,
        forall|s: int| 0 <= s < 30 ==> #[trigger] df@[s] <= 32769,
        lens_ok(lit@), lens_ok(dist@), hbits <= 50000,
    ensures r.0 <= 50000 + 316 * 32769 * 15, r.1 <= 316 * 32769 * 9,
{
    let mut db: u64 = hbits;
    let mut fb: u64 = 0;
    let mut s: usize = 0;
    while s < 286
        invariant s <= 286, lf@.len() == 286, lit@.len() == 286, lens_ok(lit@),
            forall|t: int| 0 <= t < 286 ==> #[trigger] lf@[t] <= 32769,
            db <= 50000 + s * 32769 * 15, fb <= s * 32769 * 9,
        decreases 286 - s,
    {
        let f = lf[s] as u64;
        let l = lit[s] as u64;
        let fl: u64 = if s < 144 { 8 } else if s < 256 { 9 } else if s < 280 { 7 } else { 8 };
        proof { assert(lit@[s as int] <= 15); }
        assert(f * l <= 32769 * 15) by (nonlinear_arith) requires f <= 32769, l <= 15;
        assert(f * fl <= 32769 * 9) by (nonlinear_arith) requires f <= 32769, fl <= 9;
        db = db + f * l;
        fb = fb + f * fl;
        s = s + 1;
    }
    let mut s: usize = 0;
    while s < 30
        invariant s <= 30, df@.len() == 30, dist@.len() == 30, lens_ok(dist@),
            forall|t: int| 0 <= t < 30 ==> #[trigger] df@[t] <= 32769,
            db <= 50000 + 286 * 32769 * 15 + s * 32769 * 15, fb <= 286 * 32769 * 9 + s * 32769 * 5,
        decreases 30 - s,
    {
        let f = df[s] as u64;
        let l = dist[s] as u64;
        proof { assert(dist@[s as int] <= 15); }
        assert(f * l <= 32769 * 15) by (nonlinear_arith) requires f <= 32769, l <= 15;
        db = db + f * l;
        fb = fb + f * 5;
        s = s + 1;
    }
    (db, fb)
}

pub fn deflate(data: &[u8]) -> (r: Option<Vec<u8>>)
    requires data.len() < 0x1000_0000,
    ensures r matches Some(o) ==> deflate_ok(data@, o@),
{
    deflate_level(data, level(6))
}

/// zlib's rule for a code (`zlib_ok`), checked.
fn zlib_ok_x(lens: &Vec<u8>, cl_code: bool) -> (r: bool)
    requires lens@.len() <= 320, lens_ok(lens@),
    ensures r ==> zlib_ok(lens@, cl_code),
{
    let n = lens.len();
    let mut any = false;
    let mut ones: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant i <= n, n == lens@.len(), ones == count_len(lens@, 1, i as int), ones <= i,
            !any ==> forall|j: int| 0 <= j < i ==> #[trigger] lens@[j] == 0,
        decreases n - i,
    {
        if lens[i] != 0 { any = true; }
        if lens[i] == 1 { ones = ones + 1; }
        i = i + 1;
    }
    if !any {
        proof { assert(!nonempty(lens@)); }
        return true;
    }
    let k = kraft_x(lens.as_slice());
    proof { reveal_with_fuel(p2, 16); }
    k == 32768 || (!cl_code && ones == 1 && k == 16384)
}

/// Write a block of `toks` (dynamic codes, or fixed ones when those are
/// smaller or the lengths fail their checks), after the input up to `i0`.
pub fn put_block(w: &mut BitW, fl: &EncCode, fd: &EncCode, toks: &Vec<Tok>, Ghost(pos): Ghost<Seq<int>>, src: &[u8],
             Ghost(data): Ghost<Seq<u8>>, Ghost(i0): Ghost<int>, last: bool, Ghost(st): Ghost<bool>) -> (g: Ghost<bool>)
    requires
        old(w).wf(), old(w).buf@.len() < 0x1000_0000_0000, toks@.len() <= 32768, src@.len() < 0x1000_0000,
        src@ == data.subrange(i0, pos[toks@.len() as int]),
        enc_ok(fl, fixed_lit()), enc_ok(fd, fixed_dist()),
        toks_ok(data, toks@, pos), pos[0] == i0, 0 <= i0 <= data.len(),
        str_inv(old(w).bits(), data, i0, st),
    ensures
        final(w).pre == old(w).pre, final(w).wf(),
        final(w).buf@.len() <= old(w).buf@.len() + 20 * toks@.len() + 5 * src@.len() + 3400,
        str_after(final(w).bits(), data, pos[toks@.len() as int], g@, last), g@ == st,
{
    let ghost mut st2 = st;
    proof {
        lemma_toks_len(data, toks@, pos, toks@.len() as int);
        let n = toks@.len() as int;
        if n > 0 { assert(tok_ok(data, pos[n - 1], toks@[n - 1])); }
        assert(pos[n] <= data.len());
        assert(src@.len() == pos[n] - i0);
    }
        // the block's frequencies
        let mut lf: Vec<u32> = vec![0u32; 286];
        let mut df: Vec<u32> = vec![0u32; 30];
        lf.set(256, 1);
        let mut ext: u64 = 0;
        let mut k: usize = 0;
        while k < toks.len()
            invariant k <= toks@.len(), toks@.len() <= 32768, lf@.len() == 286, df@.len() == 30,
                toks_ok(data, toks@, pos), ext <= 18 * k,
                forall|s: int| 0 <= s < 286 ==> #[trigger] lf@[s] <= k + 1,
                forall|s: int| 0 <= s < 30 ==> #[trigger] df@[s] <= k,
            decreases toks@.len() - k,
        {
            let t = toks[k];
            proof { assert(tok_ok(data, pos[k as int], toks@[k as int])); }
            if t.len == 0 {
                let x = t.lit as usize;
                lf.set(x, lf[x] + 1);
            } else {
                let x = t.ls as usize;
                lf.set(x, lf[x] + 1);
                let y = t.ds as usize;
                df.set(y, df[y] + 1);
                ext = ext + t.lx as u64 + t.dx as u64;
            }
            k = k + 1;
        }
        let lit = heur_lens(&lf, 15);
        let dist = heur_lens(&df, 15);
        let ghost wb = w.bits();
        let usable = lens_usable(&lit, &dist, &toks, Ghost(data), Ghost(pos));
        let mut wrote = false;
        let all = concat_lens(&lit, &dist);
        let (clv, hbits) = cl_plan(&all);
        let (db, fb) = block_bits(&lf, &df, &lit, &dist, hbits);
        let dyn_ok = usable && cl_good_x(&clv) && zlib_ok_x(&lit, false) && zlib_ok_x(&dist, false) && zlib_ok_x(&clv, true);
        let huff = (if dyn_ok && db < fb { db } else { fb }) + ext;
        let sb = 42 + 8 * src.len() as u64;
        if src.len() <= 65535 && sb < huff {
            proof { assert(pos[toks@.len() as int] == i0 + src@.len()); }
            let g = write_block_stored(w, src, Ghost(data), Ghost(i0), last, Ghost(st));
            proof { st2 = g@; }
            return Ghost(st2);
        }
        if dyn_ok && db < fb {
            let lc = enc_code(lit.clone());
            let dc = enc_code(dist.clone());
            proof { reveal_with_fuel(p2, 16); }
            let clc = enc_code(clv.clone());
            match (lc, dc, clc) {
                (Some(lc), Some(dc), Some(clc)) => {
                    let g = write_block_dyn(w, &clv, &clc, &lc, &dc, &lit, &dist, &all, Ghost(data), &toks, Ghost(pos), Ghost(i0), last, Ghost(st));
                    proof { st2 = g@; }
                    wrote = true;
                }
                _ => {}
            }
        }
        if !wrote {
            let g = write_block_fixed(w, fl, fd, Ghost(data), &toks, Ghost(pos), Ghost(i0), last, Ghost(st));
            proof { st2 = g@; }
        }
    Ghost(st2)
}

/// `deflate` with matches found as hard as `lv` says.
pub fn deflate_level(data: &[u8], lv: Level) -> (r: Option<Vec<u8>>)
    requires data.len() < 0x1000_0000, level_ok(lv),
    ensures r matches Some(o) ==> deflate_ok(data@, o@),
{
    let fl = match enc_code(fixed_lit_x()) { None => return None, Some(c) => c };
    let fd = match enc_code(fixed_dist_x()) { None => return None, Some(c) => c };
    proof {
        assert(lens_ok(fixed_lit())) by { assert forall|i: int| 0 <= i < fixed_lit().len() implies #[trigger] fixed_lit()[i] <= 15 by {} }
    }
    let n = data.len();
    let mut w = bw_new();
    let ghost mut st = true;
    proof {
        assert forall|b: Seq<bool>| #[trigger] is_prefix(w.bits(), b) implies
            inflate_blocks(b, 0, Seq::empty(), true) == inflate_blocks(b, w.bits().len() as int, data@.take(0), true) by {
            assert(data@.take(0) =~= Seq::<u8>::empty());
        }
    }
    if n == 0 {
        let toks: Vec<Tok> = Vec::new();
        let ghost pos0: Seq<int> = seq![0int];
        let g = write_block_fixed(&mut w, &fl, &fd, Ghost(data@), &toks, Ghost(pos0), Ghost(0), true, Ghost(st));
        let ghost wf0 = w.bits();
        let out = finish(w);
        proof {
            assert(data@.take(0) =~= data@);
            let q = wf0.len();
            assert forall|b: Seq<bool>| #[trigger] is_prefix(lbits(out@), b) implies inflate(b) == Some((data@, q, g@)) by {
                lemma_prefix_trans_b(wf0, lbits(out@), b);
                assert(inflate_blocks(b, 0, Seq::empty(), true) == Some((data@.take(0), wf0.len() as int, g@)));
            }
            assert(inflate_q(out@, q, g@));
        }
        return Some(out);
    }
    let mut ch = chains_new();
    let tabs = sym_tabs();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n, n == data.len(), n < 0x1000_0000, w.wf(), st, w.pre@.len() == 0, level_ok(lv), tabs_wf(&tabs),
            w.buf@.len() <= 3500 * i,
            enc_ok(&fl, fixed_lit()), enc_ok(&fd, fixed_dist()),
            i < n ==> str_inv(w.bits(), data@, i as int, st),
            i == n ==> str_after(w.bits(), data@, n as int, st, true),
        decreases n - i,
    {
        let (toks, i1, Ghost(pos)) = tokenize(data, i, n, &mut ch, lv, &tabs);
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
