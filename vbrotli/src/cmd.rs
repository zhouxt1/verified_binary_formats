//! Commands (RFC 7932 4, 5, 6, 7, 9.3): block switches, literals in their
//! context, distances, copies and dictionary words, and the command loop
//! of a meta-block, each proved to compute its spec function.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
use vbits::lsb::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::{getbits, lz_copy};
use crate::spec::*;
use crate::code::*;
use crate::hdr::*;
use crate::dict::*;
use crate::tables::*;
use crate::br::*;

verus! {

// ---------------------------------------------------------------- blocks

/// A category's current block.
#[derive(Clone, Copy)]
pub struct XBlk {
    pub t: u64,
    pub prev: u64,
    pub left: u64,
}

pub open spec fn blk(x: XBlk) -> Blk { Blk { t: x.t as nat, prev: x.prev as nat, left: x.left as nat } }

pub open spec fn blk_ok(x: XBlk, c: &XCat) -> bool {
    x.t < c.n && (c.n >= 2 ==> x.prev < c.n) && x.left < 0x200_0000
}

pub fn blk0_x(c: &XCat, Ghost(cat): Ghost<Cat>) -> (r: XBlk)
    requires xcat_wf(c, cat),
    ensures blk(r) == blk0(cat), blk_ok(r, c),
{
    XBlk { t: 0, prev: 1, left: c.first }
}

/// Take the next element of a category, switching blocks first if its
/// block is used up: `next_blk`.
#[inline(always)]
#[verifier::spinoff_prover]
pub fn next_blk_x(c: &XCat, Ghost(cat): Ghost<Cat>, k: &mut XBlk, buf: &[u8], x: &mut Br) -> (ok: bool)
    requires xcat_wf(c, cat), blk_ok(*old(k), c), br_wf(buf@, *old(x)),
    ensures
        br_wf(buf@, *final(x)), old(x).p <= final(x).p,
        ok ==> next_blk(cat, blk(*old(k)), lbits(buf@), old(x).p as int) == Some((blk(*final(k)), final(x).p as int))
            && blk_ok(*final(k), c),
        !ok ==> next_blk(cat, blk(*old(k)), lbits(buf@), old(x).p as int) is None,
{
    if k.left > 0 {
        k.left = k.left - 1;
        return true;
    }
    if c.n < 2 {
        return false;
    }
    proof { lemma_bc(); reveal(codes_ok); }
    let ghost b = lbits(buf@);
    let ghost p0 = x.p;
    let (tc, cc) = match &c.codes { Some(v) => (&v.0, &v.1), None => return false };
    let s = match sym(tc, buf, x) { None => return false, Some(s) => s as u64 };
    let ghost q = x.p;
    let s2 = match sym(cc, buf, x) { None => return false, Some(s) => s as u64 };
    if s2 >= 26 {
        return false;
    }
    let nb = BC_EXTRA[s2 as usize] as u64;
    let e = match take(buf, x, nb) { None => return false, Some(e) => e };
    proof {
        vbits::prim_read::lemma_p2_mono(nb as nat, 24);
        assert(p2(24) == 0x100_0000) by { reveal_with_fuel(p2, 25); }
        assert(read_count(cc.lens@, b, q as int) == Some(((BC_BASE@[s2 as int] as u64 + e) as nat, x.p as int)));
    }
    let t: u64 = if s == 0 { k.prev } else if s == 1 { (k.t + 1) % c.n } else { s - 2 };
    let cnt = BC_BASE[s2 as usize] as u64 + e;
    *k = XBlk { t, prev: k.t, left: cnt - 1 };
    true
}

// -------------------------------------------------------------- literals

pub proof fn lemma_luts()
    ensures
        LUT0@ == lut0(), LUT1@ == lut1(), LUT2@ == lut2(),
        forall|i: int| 0 <= i < 256 ==> (#[trigger] lut0()[i]) < 64 && lut1()[i] < 4 && lut2()[i] < 8,
{
    lemma_lut0();
    lemma_lut1();
    lemma_lut2();
    assert(forall|i: int| 0 <= i < 256 ==> (#[trigger] lut0()[i]) < 64 && lut1()[i] < 4 && lut2()[i] < 8)
        by (compute);
}

#[inline(always)]
pub fn lit_ctx_x(mode: u8, x1: u8, x2: u8) -> (r: u64)
    requires mode < 4,
    ensures r as nat == lit_ctx(mode as nat, x1, x2), r < 64,
{
    proof { lemma_luts(); }
    if mode == 0 {
        (x1 % 64) as u64
    } else if mode == 1 {
        (x1 / 4) as u64
    } else if mode == 2 {
        let a = LUT0[x1 as usize];
        let b = LUT1[x2 as usize];
        assert(a | b < 64) by (bit_vector) requires a < 64, b < 4;
        (a | b) as u64
    } else {
        (8 * LUT2[x1 as usize] + LUT2[x2 as usize]) as u64
    }
}

/// The output is `pre + out@.take(n)`: `pre` is output already dropped
/// from the buffer `out` (ghost; `base` long), and the rest of `out` is
/// room to write into.
pub open spec fn ov(pre: Seq<u8>, out: Seq<u8>, n: int) -> Seq<u8> { pre + out.take(n) }

/// The buffer holds the last two bytes of the output, or all of it.
pub open spec fn two_ok(pre: Seq<u8>, n: int) -> bool { n >= 2 || pre.len() == 0 }

pub proof fn lemma_ov_push(pre: Seq<u8>, o: Seq<u8>, n: int, x: u8)
    requires 0 <= n < o.len(),
    ensures ov(pre, o.update(n, x), n + 1) == ov(pre, o, n).push(x),
{
    assert(ov(pre, o.update(n, x), n + 1) =~= ov(pre, o, n).push(x));
}

/// Copying after a prefix copies within what follows it.
pub proof fn lemma_lz_copy_pre(pre: Seq<u8>, s: Seq<u8>, d: nat, len: nat)
    requires 1 <= d <= s.len(),
    ensures lz_copy(pre + s, d, len) == pre + lz_copy(s, d, len),
    decreases len,
{
    if len > 0 {
        let t = pre + s;
        assert(t[t.len() - d] == s[s.len() - d]);
        assert(t.push(t[t.len() - d]) =~= pre + s.push(s[s.len() - d]));
        lemma_lz_copy_pre(pre, s.push(s[s.len() - d]), d, (len - 1) as nat);
    }
}

#[inline(always)]
fn last1(out: &Vec<u8>, n: usize, Ghost(pre): Ghost<Seq<u8>>) -> (r: u8)
    requires n <= out@.len(), two_ok(pre, n as int),
    ensures r == p1(ov(pre, out@, n as int)),
{
    if n >= 1 { out[n - 1] } else { 0 }
}

#[inline(always)]
fn last2(out: &Vec<u8>, n: usize, Ghost(pre): Ghost<Seq<u8>>) -> (r: u8)
    requires n <= out@.len(), two_ok(pre, n as int),
    ensures r == p2b(ov(pre, out@, n as int)),
{
    if n >= 2 { out[n - 2] } else { 0 }
}

pub proof fn lemma_lit_ctx_bound(mode: nat, x1: u8, x2: u8)
    requires mode < 4,
    ensures lit_ctx(mode, x1, x2) < 64,
{
    lemma_luts();
    let a = lut0()[x1 as int];
    let b = lut1()[x2 as int];
    assert(a | b < 64) by (bit_vector) requires a < 64, b < 4;
}

/// One literal in block type `t` after the bytes `b2, b1`: `tv` is the
/// block type's one code (below 256) or 256, `mode` its context mode.
#[inline(always)]
fn lit1(h: &XHdr, Ghost(sh): Ghost<Hdr>, t: u64, tv: u16, mode: u8, b1: u8, b2: u8, buf: &[u8], x: &mut Br)
    -> (r: Option<u8>)
    requires
        xhdr_wf(h, sh), t < h.cl.n, tv == h.triv@[t as int], mode == h.modes@[t as int],
        br_wf(buf@, *old(x)),
    ensures
        br_wf(buf@, *final(x)), old(x).p <= final(x).p,
        match r {
            Some(s) => dsym(sh.lit[sh.cmapl[64 * t + lit_ctx(sh.modes[t as int], b1, b2)] as int], lbits(buf@),
                            old(x).p as int) == Some((s as nat, final(x).p as int)),
            None => dsym(sh.lit[sh.cmapl[64 * t + lit_ctx(sh.modes[t as int], b1, b2)] as int], lbits(buf@),
                         old(x).p as int) is None,
        },
{
    let ghost ctx = lit_ctx(sh.modes[t as int], b1, b2);
    proof {
        assert(sh.modes[t as int] == h.modes@[t as int] as nat);
        assert(h.modes@[t as int] < 4);
        lemma_lit_ctx_bound(sh.modes[t as int], b1, b2);
        assert(sh.cmapl[64 * t + ctx] == h.cmapl@[64 * t + ctx] as nat);
    }
    let tree = if tv < 256 {
        proof { assert(h.cmapl@[64 * t + ctx] as u16 == tv); }
        tv as usize
    } else {
        h.cmapl[(64 * t + lit_ctx_x(mode, b1, b2)) as usize] as usize
    };
    proof {
        assert(h.cmapl@[64 * t + ctx] < h.lit@.len());
        assert(h.lit@[tree as int].lens@ == sh.lit[tree as int]);
    }
    match sym(&h.lit[tree], buf, x) {
        None => None,
        Some(s) => {
            proof { assert((s as int) < 256); }
            Some(s as u8)
        }
    }
}

/// The bytes after a push.
proof fn lemma_p12_push(o: Seq<u8>, s: u8)
    ensures p1(o.push(s)) == s, p2b(o.push(s)) == p1(o),
{
    assert(o.push(s)[o.len() as int] == s);
    if o.len() >= 1 { assert(o.push(s)[o.len() - 1] == o[o.len() - 1]); }
}

/// `cnt` literals written after the output `out@.take(n)`.
#[inline(always)]
pub fn lits_x(h: &XHdr, Ghost(sh): Ghost<Hdr>, buf: &[u8], x: &mut Br, cnt: u64, out: &mut Vec<u8>, n: usize,
              k: &mut XBlk, Ghost(pre): Ghost<Seq<u8>>) -> (ok: bool)
    requires xhdr_wf(h, sh), blk_ok(*old(k), &h.cl), br_wf(buf@, *old(x)), two_ok(pre, n as int),
        n + cnt <= old(out)@.len(), n + cnt < 0x1000_0000_0000_0000,
    ensures
        final(out)@.len() == old(out)@.len(), br_wf(buf@, *final(x)), old(x).p <= final(x).p,
        final(out)@.take(n as int) == old(out)@.take(n as int),
        ok ==> lits(sh, lbits(buf@), old(x).p as int, cnt as nat, ov(pre, old(out)@, n as int), blk(*old(k)))
                    == Some((ov(pre, final(out)@, n + cnt), blk(*final(k)), final(x).p as int))
                && blk_ok(*final(k), &h.cl),
        !ok ==> lits(sh, lbits(buf@), old(x).p as int, cnt as nat, ov(pre, old(out)@, n as int), blk(*old(k))) is None,
{
    let ghost b = lbits(buf@);
    let ghost target = lits(sh, b, x.p as int, cnt as nat, ov(pre, out@, n as int), blk(*k));
    let ghost len0 = out@.len();
    let ghost p0 = x.p;
    let mut i: usize = 0;
    let c = cnt as usize;
    if c == 0 {
        proof { assert(ov(pre, out@, n as int) == ov(pre, old(out)@, n as int)); }
        return true;
    }
    // the last two bytes of the output
    let mut b1 = last1(out, n, Ghost(pre));
    let mut b2 = last2(out, n, Ghost(pre));
    while i < c
        invariant
            xhdr_wf(h, sh), blk_ok(*k, &h.cl), br_wf(buf@, *x), p0 <= x.p, b == lbits(buf@),
            i <= c, c == cnt, n + c <= len0, out@.len() == len0, len0 == old(out)@.len(), n + c < 0x1000_0000_0000_0000,
            out@.take(n as int) == old(out)@.take(n as int),
            lits(sh, b, x.p as int, (c - i) as nat, ov(pre, out@, n + i), blk(*k)) == target,
            target == lits(sh, lbits(buf@), old(x).p as int, cnt as nat, ov(pre, old(out)@, n as int), blk(*old(k))),
            p0 == old(x).p, two_ok(pre, n as int),
            b1 == p1(ov(pre, out@, n + i)), b2 == p2b(ov(pre, out@, n + i)),
        decreases c - i,
    {
        if !next_blk_x(&h.cl, Ghost(sh.cl), k, buf, x) {
            return false;
        }
        // the block type, its one code if it has one, and its context mode
        let t = k.t;
        let tv = h.triv[t as usize];
        let mode = h.modes[t as usize];
        let s = match lit1(h, Ghost(sh), t, tv, mode, b1, b2, buf, x) { None => return false, Some(s) => s };
        let ghost o = out@;
        out.set(n + i, s);
        proof {
            lemma_ov_push(pre, o, n + i, s);
            lemma_p12_push(ov(pre, o, n + i), s);
            assert(out@.take(n as int) =~= o.take(n as int));
        }
        b2 = b1;
        b1 = s;
        i = i + 1;
        let ghost i1 = i;
        // the rest of this block's run: no block switch to read
        while i < c && k.left > 0
            invariant
                xhdr_wf(h, sh), blk_ok(*k, &h.cl), br_wf(buf@, *x), p0 <= x.p, b == lbits(buf@),
                i <= c, c == cnt, n + c <= len0, out@.len() == len0, len0 == old(out)@.len(), n + c < 0x1000_0000_0000_0000,
                out@.take(n as int) == old(out)@.take(n as int),
                lits(sh, b, x.p as int, (c - i) as nat, ov(pre, out@, n + i), blk(*k)) == target,
                target == lits(sh, lbits(buf@), old(x).p as int, cnt as nat, ov(pre, old(out)@, n as int), blk(*old(k))),
                p0 == old(x).p, i1 <= i, two_ok(pre, n as int),
                b1 == p1(ov(pre, out@, n + i)), b2 == p2b(ov(pre, out@, n + i)),
                t == k.t, tv == h.triv@[t as int], mode == h.modes@[t as int],
            decreases c - i,
        {
            k.left = k.left - 1;
            let s = match lit1(h, Ghost(sh), t, tv, mode, b1, b2, buf, x) { None => return false, Some(s) => s };
            let ghost o = out@;
            out.set(n + i, s);
            proof {
                lemma_ov_push(pre, o, n + i, s);
                lemma_p12_push(ov(pre, o, n + i), s);
                assert(out@.take(n as int) =~= o.take(n as int));
            }
            b2 = b1;
            b1 = s;
            i = i + 1;
        }
    }
    true
}

// ------------------------------------------------------------- distances

/// The last four distances, `r[0]` the last.
pub open spec fn rseq(r: [u64; 4]) -> Seq<int> { seq![r[0] as int, r[1] as int, r[2] as int, r[3] as int] }

pub open spec fn ring_ok(r: [u64; 4]) -> bool {
    forall|i: int| 0 <= i < 4 ==> 1 <= #[trigger] r[i] < 0x100_0000
}

#[inline(always)]
fn dist_ctx_x(clen: u64) -> (r: u64)
    requires clen >= 2,
    ensures r as nat == dist_ctx(clen as nat), r < 4,
{
    if clen > 4 { 3 } else { clen - 2 }
}

/// The distance of a command: the distance and whether it goes into the
/// ring (unless it is a dictionary reference).
#[inline(always)]
#[verifier::spinoff_prover]
fn read_dist_x(h: &XHdr, Ghost(sh): Ghost<Hdr>, ring: [u64; 4], c: u64, clen: u64, buf: &[u8], x: &mut Br,
               bd: &mut XBlk) -> (r: Option<(u64, bool)>)
    requires xhdr_wf(h, sh), blk_ok(*old(bd), &h.cd), ring_ok(ring), br_wf(buf@, *old(x)), clen >= 2,
    ensures
        br_wf(buf@, *final(x)), old(x).p <= final(x).p,
        match r {
            Some((d, e)) => read_dist(sh, rseq(ring), c as nat, clen as nat, lbits(buf@), old(x).p as int, blk(*old(bd)))
                    == Some((d as int, e, blk(*final(bd)), final(x).p as int))
                && blk_ok(*final(bd), &h.cd) && 1 <= d < 0x4000_0000,
            None => read_dist(sh, rseq(ring), c as nat, clen as nat, lbits(buf@), old(x).p as int, blk(*old(bd))) is None,
        },
{
    if c < 128 {
        return Some((ring[0], false));
    }
    if !next_blk_x(&h.cd, Ghost(sh.cd), bd, buf, x) {
        return None;
    }
    let ti = (4 * bd.t + dist_ctx_x(clen)) as usize;
    let tree = h.cmapd[ti] as usize;
    proof {
        assert(sh.cmapd[ti as int] == tree as nat);
        assert(h.dist@[tree as int].lens@ == sh.dist[tree as int]);
    }
    let dc = match sym(&h.dist[tree], buf, x) { None => return None, Some(s) => s as u64 };
    if dc < 16 {
        let base: u64 = if dc < 10 { ring[0] } else { ring[1] };
        let k: u64 = if dc < 4 { 0 } else if dc < 10 { dc - 4 } else { dc - 10 };
        let delta: u64 = k / 2 + 1;
        let d: u64 = if dc < 4 {
            if dc == 0 { ring[0] } else if dc == 1 { ring[1] } else if dc == 2 { ring[2] } else { ring[3] }
        } else if k % 2 == 0 {
            if base <= delta { return None; }
            base - delta
        } else {
            base + delta
        };
        proof {
            assert(rseq(ring).len() == 4);
            if dc < 4 { assert(rseq(ring)[dc as int] == ring[dc as int] as int); }
            assert(1 <= ring[0] < 0x100_0000 && 1 <= ring[1] < 0x100_0000);
            if dc < 4 { assert(1 <= ring[dc as int] < 0x100_0000); }
        }
        return Some((d, dc != 0));
    }
    proof {
        reveal(dtab_ok);
        assert(dtab_at(h.dtab@[dc as int], h.npostfix as nat, h.ndirect as nat, dc as nat));
    }
    let v = h.dtab[dc as usize];
    let nb = v / 0x1_0000_0000;
    let base = v % 0x1_0000_0000;
    let e = match take(buf, x, nb) { None => return None, Some(e) => e };
    let np = h.npostfix;
    proof {
        if dc >= 16 + h.ndirect {
            lemma_long_dist_e(np as nat, h.ndirect as nat, dc as nat, e as nat);
        } else {
            assert(p2(0) == 1) by { reveal_with_fuel(p2, 1); }
            assert(e == 0);
        }
        vbits::prim_read::lemma_p2_eq_pow2(np as nat);
        vbits::prim_read::lemma_p2_mono(np as nat, 3);
        vbits::prim_read::lemma_p2_mono(nb as nat, 24);
        reveal_with_fuel(p2, 25);
        assert(e * p2(np as nat) <= (p2(nb as nat) - 1) * p2(np as nat)) by (nonlinear_arith)
            requires e <= p2(nb as nat) - 1;
        vstd::bits::lemma_u64_shl_is_mul(e, np);
    }
    Some((base + (e << np), true))
}

// ------------------------------------------------------------------ copies

/// Copy `t[i] = out[i - d]` for `i` from `n + k0` to `n + len`, sixteen
/// bytes at a time: `d >= 16`, so each sixteen come from bytes already there.
#[inline(always)]
fn copy16s(out: &mut Vec<u8>, n: usize, d: usize, k0: usize, len: usize, Ghost(t): Ghost<Seq<u8>>)
    requires
        16 <= d <= n + k0, k0 <= len, n + len + 16 <= old(out)@.len(), len < 0x400_0000,
        t.len() == n + len,
        forall|i: int| 0 <= i < n + k0 ==> #[trigger] old(out)@[i] == t[i],
        forall|i: int| n + k0 <= i < n + len ==> #[trigger] t[i] == t[i - d],
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|i: int| 0 <= i < n + len ==> #[trigger] final(out)@[i] == t[i],
{
    let pl = out.len();
    let mut k: usize = k0;
    while k < len
        invariant
            16 <= d <= n + k0, k0 <= k, k <= len + 15, n + len + 16 <= pl, out@.len() == pl, len < 0x400_0000,
            t.len() == n + len,
            forall|i: int| n + k0 <= i < n + len ==> #[trigger] t[i] == t[i - d],
            forall|i: int| 0 <= i < n + k && i < n + len ==> #[trigger] out@[i] == t[i],
        decreases len + 16 - k,
    {
        let ghost old_out = out@;
        let src = n + k - d;
        out.as_mut_slice().copy_within(src..src + 16, n + k);
        proof {
            assert forall|i: int| 0 <= i < n + k + 16 && i < n + len implies #[trigger] out@[i] == t[i] by {
                if i >= n + k {
                    assert(out@[i] == old_out[src + (i - (n + k))]);
                    assert(src + (i - (n + k)) == i - d);
                    assert(old_out[i - d] == t[i - d]);
                }
            }
        }
        k = k + 16;
    }
}

/// Append a copy of `len` bytes from `d` back to the output `out@.take(n)`:
/// for `d >= 16`, sixteen bytes at a time, the first sixteen outside a loop.
#[inline(always)]
fn copy_x(out: &mut Vec<u8>, n: usize, d: usize, len: usize)
    requires 1 <= d <= n, n + len + 16 <= old(out)@.len(), len < 0x400_0000,
    ensures
        final(out)@.len() == old(out)@.len(),
        final(out)@.take((n + len) as int) == lz_copy(old(out)@.take(n as int), d as nat, len as nat),
{
    if d < 16 {
        vdeflate::inflate::copy_match(out, n, d, len);
        return;
    }
    let ghost o = out@.take(n as int);
    let ghost t = lz_copy(o, d as nat, len as nat);
    proof { vdeflate::inflate::lemma_lz_char(o, d as nat, len as nat); }
    let ghost old_out = out@;
    let src = n - d;
    out.as_mut_slice().copy_within(src..src + 16, n);
    proof {
        assert forall|i: int| 0 <= i < n + 16 && i < n + len implies #[trigger] out@[i] == t[i] by {
            if i >= n {
                assert(out@[i] == old_out[src + (i - n)]);
                assert(t[i] == t[i - d]);
            }
        }
    }
    if len > 16 {
        copy16s(out, n, d, 16, len, Ghost(t));
    }
    proof { assert(out@.take((n + len) as int) =~= t); }
}

/// Transform `id` of the word of length `len` and index `idx`, written
/// after `out@.take(n)` if it ends by `end`: the new length.
#[verifier::spinoff_prover]
fn put_word(dict: &[u8], out: &mut Vec<u8>, n: usize, len: usize, idx: usize, id: usize, end: usize) -> (r: Option<usize>)
    requires
        dict_ok(dict@), 4 <= len <= 24, idx < p2(ndbits()[len as int] as nat), id <= 120,
        n <= end, end <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        match r {
            Some(n2) => final(out)@.take(n2 as int)
                    == old(out)@.take(n as int) + transform(id as nat, dict_word(dict@, len as nat, idx as nat))
                && n <= n2 <= end,
            None => n + transform(id as nat, dict_word(dict@, len as nat, idx as nat)).len() > end
                && final(out)@ == old(out)@,
        },
{
    hide(transform);
    let ghost word = dict_word(dict@, len as nat, idx as nat);
    proof { lemma_word_in(len as nat, idx as nat); lemma_doff(); lemma_transform(id as int, word); }
    let o = DOFF[len] as usize + idx * len;
    let t = TR_TYPE[id];
    let (pa, pb) = (TR_PRE_OFF[id] as usize, TR_PRE_OFF[id + 1] as usize);
    let (sa, sb) = (TR_SUF_OFF[id] as usize, TR_SUF_OFF[id + 1] as usize);
    proof { assert(word =~= dict@.subrange(o as int, o + len)); }
    let k0 = elem_len(t, len);
    proof { assert(elem(t as nat, word).len() == k0); }
    if (pb - pa) + k0 + (sb - sa) > end - n {
        return None;
    }
    let ghost o0 = out@;
    put_x(out, n, &TR_PRE, pa, pb);
    let m1 = n + (pb - pa);
    let k = put_elem(out, m1, dict, o, len, t);
    let m2 = m1 + k;
    put_x(out, m2, &TR_SUF, sa, sb);
    let n2 = m2 + (sb - sa);
    proof { assert(out@.take(n2 as int) =~= o0.take(n as int) + transform(id as nat, word)); }
    Some(n2)
}

/// A dictionary reference: the word written after `out@.take(n)`; the
/// flag and the new length.
#[verifier::spinoff_prover]
fn dict_ref_x(dict: &[u8], maxd: u64, out: &mut Vec<u8>, n: usize, ring: [u64; 4], google: bool, d: u64, clen: u64,
              end: usize, Ghost(pre): Ghost<Seq<u8>>) -> (r: Option<(bool, usize)>)
    requires
        dict_ok(dict@), maxd < d < 0x4000_0000, 2 <= clen < 0x200_0000,
        n <= end, end <= old(out)@.len(), pre.len() + end < 0x4000_0000_0000_0000,
    ensures
        final(out)@.len() == old(out)@.len(),
        match r {
            Some((g2, n2)) => dict_ref(dict@, maxd as int, St { out: ov(pre, old(out)@, n as int), ring: rseq(ring), google },
                                       d as int, clen as nat, (pre.len() + end) as nat)
                    == Some(St { out: ov(pre, final(out)@, n2 as int), ring: rseq(ring), google: g2 })
                && n <= n2 <= end,
            None => dict_ref(dict@, maxd as int, St { out: ov(pre, old(out)@, n as int), ring: rseq(ring), google },
                             d as int, clen as nat, (pre.len() + end) as nat) is None,
        },
        r is None ==> final(out)@ == old(out)@,
{
    let wid = d - maxd - 1;
    if clen < 4 || clen > 24 {
        return None;
    }
    proof { lemma_doff(); lemma_ndbits(); lemma_tr(); }
    let nbits = NDBITS[clen as usize] as u64;
    proof {
        vbits::prim_read::lemma_p2_eq_pow2(nbits as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(nbits as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, nbits);
        vbits::bitspec::lemma_p2_pos(nbits as nat);
    }
    let nw: u64 = 1u64 << nbits;
    let tid = wid / nw;
    if tid > 120 {
        return None;
    }
    let len = clen as usize;
    let idx = (wid % nw) as usize;
    let ghost w = transform(tid as nat, dict_word(dict@, len as nat, idx as nat));
    let ghost o0 = out@;
    match put_word(dict, out, n, len, idx, tid as usize, end) {
        None => None,
        Some(n2) => {
            proof { assert(ov(pre, out@, n2 as int) =~= ov(pre, o0, n as int) + w); }
            Some((google && !(n2 == n && d <= 120), n2))
        }
    }
}

/// The copy part of a command: a copy, or a dictionary word. The ring, the
/// flag and the new length. The buffer holds at least a window of output,
/// or all of it, so a copy's bytes are in it.
#[inline(always)]
fn do_copy_x(dict: &[u8], window: u64, out: &mut Vec<u8>, n: usize, ring: [u64; 4], google: bool, d: u64,
             explicit: bool, clen: u64, end: usize, Ghost(pre): Ghost<Seq<u8>>, base: usize) -> (r: Option<([u64; 4], bool, usize)>)
    requires
        dict_ok(dict@), window < 0x100_0000, 1 <= d < 0x4000_0000, 2 <= clen < 0x200_0000, ring_ok(ring),
        n <= end, end + 16 <= old(out)@.len(), base + end < 0x4000_0000_0000_0000,
        base == pre.len(), n >= window || base == 0,
    ensures
        final(out)@.len() == old(out)@.len(),
        match r {
            Some((ring2, g2, n2)) => do_copy(dict@, window as nat, St { out: ov(pre, old(out)@, n as int), ring: rseq(ring), google },
                                             d as int, explicit, clen as nat, (base + end) as nat)
                    == Some(St { out: ov(pre, final(out)@, n2 as int), ring: rseq(ring2), google: g2 })
                && ring_ok(ring2) && n <= n2 <= end,
            None => do_copy(dict@, window as nat, St { out: ov(pre, old(out)@, n as int), ring: rseq(ring), google },
                            d as int, explicit, clen as nat, (base + end) as nat) is None,
        },
        r is None ==> final(out)@ == old(out)@,
{
    let tot = (base + n) as u64;
    let maxd: u64 = if tot < window { tot } else { window };
    if d > maxd {
        match dict_ref_x(dict, maxd, out, n, ring, google, d, clen, end, Ghost(pre)) {
            None => None,
            Some((g2, n2)) => Some((ring, g2, n2)),
        }
    } else {
        if clen > (end - n) as u64 {
            return None;
        }
        proof { assert(old(out)@.take(n as int).len() == n); }
        copy_x(out, n, d as usize, clen as usize);
        proof {
            vdeflate::inflate::lemma_lz_char(old(out)@.take(n as int), d as nat, clen as nat);
            lemma_lz_copy_pre(pre, old(out)@.take(n as int), d as nat, clen as nat);
        }
        if explicit {
            let r2 = [d, ring[0], ring[1], ring[2]];
            proof { assert(rseq(r2) =~= seq![d as int] + rseq(ring).take(3)); }
            Some((r2, google, n + clen as usize))
        } else {
            Some((ring, google, n + clen as usize))
        }
    }
}

// ----------------------------------------------------------- the commands

/// The insert and copy length codes' bases and extra bits (5), by row: an
/// insert code by `c / 8` (its cell and the middle three bits), a copy code
/// by `8 * (c / 64) + c % 8` (its cell and the low three bits). Padded to
/// 128 so that a masked index needs no bounds check.
pub const INS_BASE_J: [u16; 128] = [
    0, 1, 2, 3, 4, 5, 6, 8, 0, 1, 2, 3, 4, 5, 6, 8, 0, 1, 2, 3, 4, 5, 6, 8, 0, 1, 2, 3, 4, 5, 6, 8, 10, 14, 18,
    26, 34, 50, 66, 98, 10, 14, 18, 26, 34, 50, 66, 98, 0, 1, 2, 3, 4, 5, 6, 8, 130, 194, 322, 578, 1090, 2114,
    6210, 22594, 10, 14, 18, 26, 34, 50, 66, 98, 130, 194, 322, 578, 1090, 2114, 6210, 22594, 130, 194, 322, 578,
    1090, 2114, 6210, 22594, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
];
pub const INS_EXTRA_J: [u8; 128] = [
    0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4,
    4, 5, 5, 2, 2, 3, 3, 4, 4, 5, 5, 0, 0, 0, 0, 0, 0, 1, 1, 6, 7, 8, 9, 10, 12, 14, 24, 2, 2, 3, 3, 4, 4, 5, 5,
    6, 7, 8, 9, 10, 12, 14, 24, 6, 7, 8, 9, 10, 12, 14, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
];
pub const COPY_BASE_J: [u16; 128] = [
    2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 18, 22, 30, 38, 54, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 18, 22, 30, 38,
    54, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 18, 22, 30, 38, 54, 70, 102, 134, 198, 326, 582, 1094, 2118, 2, 3, 4,
    5, 6, 7, 8, 9, 70, 102, 134, 198, 326, 582, 1094, 2118, 10, 12, 14, 18, 22, 30, 38, 54, 70, 102, 134, 198,
    326, 582, 1094, 2118, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2
];
pub const COPY_EXTRA_J: [u8; 128] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 8, 9, 10, 24, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 6, 7, 8, 9, 10, 24,
    1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 8, 9, 10, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
];

pub open spec fn ins_row(j: nat) -> nat { cell_ins()[(j / 8) as int] + j % 8 }
pub open spec fn copy_row(j: nat) -> nat { cell_copy()[(j / 8) as int] + j % 8 }

pub proof fn lemma_cmd_tables_j()
    ensures
        forall|j: int| 0 <= j < 88 ==> (#[trigger] INS_BASE_J@[j]) as nat == ins_base()[ins_row(j as nat) as int]
            && INS_EXTRA_J@[j] as nat == ins_extra()[ins_row(j as nat) as int]
            && INS_BASE_J@[j] <= 22594 && INS_EXTRA_J@[j] <= 24,
        forall|j: int| 0 <= j < 88 ==> (#[trigger] COPY_BASE_J@[j]) as nat == copy_base()[copy_row(j as nat) as int]
            && COPY_EXTRA_J@[j] as nat == copy_extra()[copy_row(j as nat) as int]
            && 2 <= COPY_BASE_J@[j] <= 2118 && COPY_EXTRA_J@[j] <= 24,
{
    assert(forall|j: int| 0 <= j < 88 ==> (#[trigger] INS_BASE_J@[j]) as nat == ins_base()[ins_row(j as nat) as int]
            && INS_EXTRA_J@[j] as nat == ins_extra()[ins_row(j as nat) as int]
            && INS_BASE_J@[j] <= 22594 && INS_EXTRA_J@[j] <= 24) by (compute);
    assert(forall|j: int| 0 <= j < 88 ==> (#[trigger] COPY_BASE_J@[j]) as nat == copy_base()[copy_row(j as nat) as int]
            && COPY_EXTRA_J@[j] as nat == copy_extra()[copy_row(j as nat) as int]
            && 2 <= COPY_BASE_J@[j] <= 2118 && COPY_EXTRA_J@[j] <= 24) by (compute);
}

/// A command symbol's insert base, copy base, insert and copy extra bits.
#[inline(always)]
fn cmd_lens(c: u64) -> (r: (u64, u64, u64, u64))
    requires c < 704,
    ensures
        r.0 as nat == ins_base()[ins_code(c as nat) as int] && r.0 <= 22594,
        r.1 as nat == copy_base()[copy_code(c as nat) as int] && 2 <= r.1 <= 2118,
        r.2 as nat == ins_extra()[ins_code(c as nat) as int] && r.2 <= 24,
        r.3 as nat == copy_extra()[copy_code(c as nat) as int] && r.3 <= 24,
{
    proof { lemma_cmd_tables_j(); }
    let ji = (c >> 3) & 127;
    let jc = ((c >> 3) & 120) | (c & 7);
    assert(ji == c / 8 && jc == 8 * (c / 64) + c % 8 && jc < 88) by (bit_vector)
        requires ji == (c >> 3) & 127, jc == ((c >> 3) & 120) | (c & 7), c < 704;
    proof {
        assert(ins_row(ji as nat) == ins_code(c as nat)) by {
            assert((ji as nat) / 8 == (c as nat) / 64 && (ji as nat) % 8 == ((c as nat) / 8) % 8);
        }
        assert(copy_row(jc as nat) == copy_code(c as nat)) by {
            assert((jc as nat) / 8 == (c as nat) / 64 && (jc as nat) % 8 == (c as nat) % 8);
        }
    }
    (INS_BASE_J[ji as usize] as u64, COPY_BASE_J[jc as usize] as u64, INS_EXTRA_J[ji as usize] as u64,
     COPY_EXTRA_J[jc as usize] as u64)
}

/// The start of a command: its symbol, insert and copy lengths.
#[inline(always)]
#[verifier::spinoff_prover]
pub fn cmd_head_x(h: &XHdr, Ghost(sh): Ghost<Hdr>, buf: &[u8], x: &mut Br, bi: &mut XBlk) -> (r: Option<(u64, u64, u64)>)
    requires xhdr_wf(h, sh), br_wf(buf@, *old(x)), blk_ok(*old(bi), &h.ci),
    ensures
        br_wf(buf@, *final(x)), old(x).p <= final(x).p,
        match r {
            Some((c, ilen, clen)) => cmd_head(sh, lbits(buf@), old(x).p as int, blk(*old(bi)))
                    == Some((blk(*final(bi)), c as nat, ilen as nat, clen as nat, final(x).p as int))
                && blk_ok(*final(bi), &h.ci) && c < 704 && ilen < 0x200_0000 && 2 <= clen < 0x200_0000,
            None => cmd_head(sh, lbits(buf@), old(x).p as int, blk(*old(bi))) is None,
        },
{
    if !next_blk_x(&h.ci, Ghost(sh.ci), bi, buf, x) {
        return None;
    }
    proof { assert(h.cmd@[bi.t as int].lens@ == sh.cmd[bi.t as int]); }
    let c = match sym(&h.cmd[bi.t as usize], buf, x) { None => return None, Some(s) => s as u64 };
    let (ib, cb, ie, ce) = cmd_lens(c);
    let e1 = match take(buf, x, ie) { None => return None, Some(e) => e };
    let e2 = match take(buf, x, ce) { None => return None, Some(e) => e };
    proof {
        vbits::prim_read::lemma_p2_mono(ie as nat, 24);
        vbits::prim_read::lemma_p2_mono(ce as nat, 24);
        assert(p2(24) == 0x100_0000) by { reveal_with_fuel(p2, 25); }
    }
    Some((c, ib + e1, cb + e2))
}

/// The end of a command: its distance and its copy or dictionary word:
/// the ring, the flag and the output's length.
#[inline(always)]
#[verifier::spinoff_prover]
pub fn cmd_tail_x(dict: &[u8], window: u64, h: &XHdr, Ghost(sh): Ghost<Hdr>, buf: &[u8], x: &mut Br, end: usize,
              out: &mut Vec<u8>, n: usize, ring: [u64; 4], google: bool, c: u64, clen: u64, bd: &mut XBlk,
              Ghost(pre): Ghost<Seq<u8>>, base: usize)
    -> (r: Option<([u64; 4], bool, usize)>)
    requires
        dict_ok(dict@), window < 0x100_0000, xhdr_wf(h, sh), br_wf(buf@, *old(x)),
        blk_ok(*old(bd), &h.cd), ring_ok(ring), 2 <= clen < 0x200_0000,
        n <= end, end + 16 <= old(out)@.len(), base + end < 0x1000_0000_0000_0000,
        base == pre.len(), n >= window || base == 0,
    ensures
        final(out)@.len() == old(out)@.len(), br_wf(buf@, *final(x)), old(x).p <= final(x).p,
        match r {
            Some((ring2, g2, n2)) => cmd_tail(dict@, window as nat, sh, lbits(buf@), old(x).p as int, (base + end) as nat,
                                              St { out: ov(pre, old(out)@, n as int), ring: rseq(ring), google },
                                              c as nat, clen as nat, blk(*old(bd)))
                    == Some((St { out: ov(pre, final(out)@, n2 as int), ring: rseq(ring2), google: g2 }, blk(*final(bd)),
                             final(x).p as int))
                && ring_ok(ring2) && n <= n2 <= end && blk_ok(*final(bd), &h.cd),
            None => cmd_tail(dict@, window as nat, sh, lbits(buf@), old(x).p as int, (base + end) as nat,
                             St { out: ov(pre, old(out)@, n as int), ring: rseq(ring), google },
                             c as nat, clen as nat, blk(*old(bd))) is None,
        },
        r is None ==> final(out)@ == old(out)@,
{
    let (d, explicit) = match read_dist_x(h, Ghost(sh), ring, c, clen, buf, x, bd) {
        None => return None,
        Some(v) => v,
    };
    do_copy_x(dict, window, out, n, ring, google, d, explicit, clen, end, Ghost(pre), base)
}

/// The command loop's state: the bit window, the output's length, the
/// ring, the flag, and the three blocks.
pub struct CState {
    pub x: Br,
    pub n: usize,
    pub ring: [u64; 4],
    pub google: bool,
    pub bl: XBlk,
    pub bi: XBlk,
    pub bd: XBlk,
}

pub open spec fn cs_wf(c: &CState, h: &XHdr, buf: Seq<u8>, end: nat) -> bool {
    &&& br_wf(buf, c.x) && c.n <= end && ring_ok(c.ring)
    &&& blk_ok(c.bl, &h.cl) && blk_ok(c.bi, &h.ci) && blk_ok(c.bd, &h.cd)
}

/// The spec's state for a command loop state over the buffer `out`, after
/// the dropped output `pre`.
pub open spec fn cs_st(c: &CState, pre: Seq<u8>, out: Seq<u8>) -> St {
    St { out: ov(pre, out, c.n as int), ring: rseq(c.ring), google: c.google }
}

/// One command: `Some(true)` if it ends the meta-block, `Some(false)` if
/// another follows, `None` if the spec has no result.
#[inline(always)]
#[verifier::spinoff_prover]
pub fn command_x(dict: &[u8], window: u64, h: &XHdr, Ghost(sh): Ghost<Hdr>, buf: &[u8], end: usize,
             out: &mut Vec<u8>, cs: &mut CState, Ghost(pre): Ghost<Seq<u8>>, base: usize) -> (r: Option<bool>)
    requires
        dict_ok(dict@), window < 0x100_0000, xhdr_wf(h, sh),
        cs_wf(old(cs), h, buf@, end as nat), old(cs).n < end,
        end + 16 <= old(out)@.len(), base + end < 0x1000_0000_0000_0000,
        base == pre.len(), old(cs).n >= window || base == 0, two_ok(pre, old(cs).n as int),
    ensures
        final(out)@.len() == old(out)@.len(),
        match r {
            Some(done) => cmd_step(dict@, window as nat, sh, lbits(buf@), old(cs).x.p as int, (base + end) as nat,
                                   cs_st(old(cs), pre, old(out)@), blk(old(cs).bl), blk(old(cs).bi), blk(old(cs).bd))
                    == (if done { Some(Step::Done(cs_st(final(cs), pre, final(out)@), final(cs).x.p as int)) }
                        else { Some(Step::Next(cs_st(final(cs), pre, final(out)@), blk(final(cs).bl), blk(final(cs).bi),
                                                blk(final(cs).bd), final(cs).x.p as int)) })
                && cs_wf(final(cs), h, buf@, end as nat)
                && (done ==> final(cs).n == end) && (!done ==> final(cs).n < end),
            None => cmd_step(dict@, window as nat, sh, lbits(buf@), old(cs).x.p as int, (base + end) as nat,
                             cs_st(old(cs), pre, old(out)@), blk(old(cs).bl), blk(old(cs).bi), blk(old(cs).bd)) is None,
        },
        r is None ==> final(out)@.take(old(cs).n as int) == old(out)@.take(old(cs).n as int),
        r is Some ==> old(cs).x.p <= final(cs).x.p,
{
    hide(lits);
    hide(cmd_tail);
    let n = cs.n;
    let (c, ilen, clen) = match cmd_head_x(h, Ghost(sh), buf, &mut cs.x, &mut cs.bi) { None => return None, Some(v) => v };
    if ilen > (end - n) as u64 {
        return None;
    }
    if !lits_x(h, Ghost(sh), buf, &mut cs.x, ilen, out, n, &mut cs.bl, Ghost(pre)) {
        return None;
    }
    let n1 = n + ilen as usize;
    if n1 >= end {
        cs.n = end;
        return Some(true);
    }
    let (ring2, g2, n2) = match cmd_tail_x(dict, window, h, Ghost(sh), buf, &mut cs.x, end, out, n1, cs.ring,
                                           cs.google, c, clen, &mut cs.bd, Ghost(pre), base) {
        None => return None,
        Some(v) => v,
    };
    cs.n = n2;
    cs.ring = ring2;
    cs.google = g2;
    Some(n2 >= end)
}

/// The commands of a meta-block until the output `out@.take(n)` reaches
/// `end`: the position after them, the ring, the flag. The output then
/// ends at `end`.
#[verifier::spinoff_prover]
pub fn commands_x(dict: &[u8], window: u64, h: &XHdr, Ghost(sh): Ghost<Hdr>, buf: &[u8], pos: usize, end: usize,
                  out: &mut Vec<u8>, n0: usize, ring0: [u64; 4], google0: bool, bl0: XBlk, bi0: XBlk, bd0: XBlk,
                  Ghost(pre): Ghost<Seq<u8>>, base: usize)
    -> (r: Option<(usize, [u64; 4], bool)>)
    requires
        dict_ok(dict@), window < 0x100_0000, xhdr_wf(h, sh), buf_ok(buf@), pos <= 8 * buf.len(),
        blk_ok(bl0, &h.cl), blk_ok(bi0, &h.ci), blk_ok(bd0, &h.cd), ring_ok(ring0),
        n0 < end, end + 16 <= old(out)@.len(), base + end < 0x1000_0000_0000_0000,
        base == pre.len(), n0 >= window || base == 0, two_ok(pre, n0 as int),
    ensures
        final(out)@.len() == old(out)@.len(),
        match r {
            Some((q, ring2, g2)) => commands(dict@, window as nat, sh, lbits(buf@), pos as int, (base + end) as nat,
                                             St { out: ov(pre, old(out)@, n0 as int), ring: rseq(ring0), google: google0 },
                                             blk(bl0), blk(bi0), blk(bd0))
                    == Some((St { out: ov(pre, final(out)@, end as int), ring: rseq(ring2), google: g2 }, q as int))
                && ring_ok(ring2) && q <= 8 * buf.len(),
            None => commands(dict@, window as nat, sh, lbits(buf@), pos as int, (base + end) as nat,
                             St { out: ov(pre, old(out)@, n0 as int), ring: rseq(ring0), google: google0 },
                             blk(bl0), blk(bi0), blk(bd0)) is None,
        },
{
    hide(cmd_step);
    let ghost b = lbits(buf@);
    let ghost target = commands(dict@, window as nat, sh, b, pos as int, (base + end) as nat,
                                St { out: ov(pre, out@, n0 as int), ring: rseq(ring0), google: google0 },
                                blk(bl0), blk(bi0), blk(bd0));
    let ghost len0 = out@.len();
    let mut cs = CState { x: br_at(buf, pos), n: n0, ring: ring0, google: google0, bl: bl0, bi: bi0, bd: bd0 };
    loop
        invariant
            dict_ok(dict@), window < 0x100_0000, xhdr_wf(h, sh), buf_ok(buf@), b == lbits(buf@),
            cs_wf(&cs, h, buf@, end as nat), cs.n < end,
            end + 16 <= len0, out@.len() == len0, len0 == old(out)@.len(), base + end < 0x1000_0000_0000_0000,
            base == pre.len(), cs.n >= window || base == 0, two_ok(pre, cs.n as int),
            commands(dict@, window as nat, sh, b, cs.x.p as int, (base + end) as nat, cs_st(&cs, pre, out@),
                     blk(cs.bl), blk(cs.bi), blk(cs.bd)) == target,
            target == commands(dict@, window as nat, sh, lbits(buf@), pos as int, (base + end) as nat,
                               St { out: ov(pre, old(out)@, n0 as int), ring: rseq(ring0), google: google0 },
                               blk(bl0), blk(bi0), blk(bd0)),
        decreases end - cs.n, 8 * buf.len() - cs.x.p, cs.bi.left,
    {
        let (p, n, left) = (cs.x.p, cs.n, cs.bi.left);
        match command_x(dict, window, h, Ghost(sh), buf, end, out, &mut cs, Ghost(pre), base) {
            None => return None,
            Some(true) => {
                proof { assert(cs_st(&cs, pre, out@).out == ov(pre, out@, end as int)); }
                return Some((cs.x.p, cs.ring, cs.google));
            }
            Some(false) => {
                if !((cs.n > n) || (cs.n == n && p < cs.x.p && cs.x.p <= 8 * buf.len())
                     || (cs.n == n && cs.x.p == p && cs.bi.left < left)) {
                    return None;
                }
            }
        }
    }
}

} // verus!
