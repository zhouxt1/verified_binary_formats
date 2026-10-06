//! The decoder: blocks, their headers and their symbols, each proved to
//! compute its spec function (`spec.rs`) on `lbits(input)`.
//!
//! A decode ends in one of three ways. `Ok` is exactly the spec's result.
//! `Err(Bad)` means the spec has no result: the input is not a DEFLATE
//! stream. `Err(TooBig)` means the output would pass the caller's limit: the
//! spec either has no result or one longer than the limit.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
use vbits::lsb::*;
use crate::spec::*;
use crate::huff::*;
use crate::step::*;

verus! {

#[cfg(verus_keep_ghost)] // proof-only: erased from a plain build
use vstd::bits::{lemma_u64_shl_is_mul, lemma_u64_pow2_no_overflow};
#[cfg(verus_keep_ghost)] // proof-only: erased from a plain build
use vbits::prim_read::lemma_p2_eq_pow2;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Error {
    /// Not a DEFLATE stream.
    Bad,
    /// The output would be longer than the limit.
    TooBig,
}

/// What a decode that stops with `r` says about the spec's result `sp`.
pub open spec fn outcome(r: Result<usize, Error>, sp: Option<(Seq<u8>, int)>, max_out: nat,
                         got: Seq<u8>) -> bool {
    match r {
        Ok(q) => sp == Some((got, q as int)),
        Err(Error::Bad) => sp is None,
        Err(Error::TooBig) => sp matches Some((o, _)) ==> o.len() > max_out,
    }
}

// ------------------------------------------------------------ bit fields

/// `n` bits at `pos` (n <= 16), LSB first.
pub fn getbits_x(buf: &[u8], pos: usize, n: u64) -> (r: Option<u64>)
    requires buf.len() < max_input(), pos <= 8 * buf.len(), n <= 16,
    ensures
        match r {
            Some(v) => getbits(lbits(buf@), pos as int, n as nat) == Some(v as nat)
                && pos + n <= 8 * buf.len(),
            None => getbits(lbits(buf@), pos as int, n as nat) is None,
        },
{
    if n as usize > 8 * buf.len() - pos {
        return None;
    }
    if n == 0 {
        proof {
            assert(lbits(buf@).subrange(pos as int, pos as int) =~= Seq::<bool>::empty());
        }
        return Some(0);
    }
    let v = peek_lsb(buf, pos, n);
    proof { lemma_lview_inside(buf@, pos as int, pos as int + n); }
    Some(v)
}

pub proof fn lemma_getbits_bound(b: Seq<bool>, p: int, n: nat)
    requires getbits(b, p, n) is Some,
    ensures getbits(b, p, n).unwrap() < p2(n),
{
    lemma_lval_bound(b.subrange(p, p + n));
}

// ------------------------------------------------------ the fixed tables

pub fn len_base_x(s: u64) -> (r: u64)
    requires 257 <= s <= 285,
    ensures r as nat == len_base(s as nat), r <= 258,
{
    if s <= 264 { s - 254 }
    else if s <= 268 { 11 + 2 * (s - 265) }
    else if s <= 272 { 19 + 4 * (s - 269) }
    else if s <= 276 { 35 + 8 * (s - 273) }
    else if s <= 280 { 67 + 16 * (s - 277) }
    else if s <= 284 { 131 + 32 * (s - 281) }
    else { 258 }
}

pub fn len_extra_x(s: u64) -> (r: u64)
    requires 257 <= s <= 285,
    ensures r as nat == len_extra(s as nat), r <= 5,
{
    if s <= 264 || s == 285 { 0 } else { (s - 261) / 4 }
}

pub fn dist_extra_x(d: u64) -> (r: u64)
    requires d <= 29,
    ensures r as nat == dist_extra(d as nat), r <= 13,
{
    if d < 4 { 0 } else { d / 2 - 1 }
}

pub fn dist_base_x(d: u64) -> (r: u64)
    requires d <= 29,
    ensures r as nat == dist_base(d as nat), 1 <= r <= 24577,
{
    if d < 4 {
        d + 1
    } else {
        let e = d / 2 - 1;
        proof {
            lemma_p2_eq_pow2(e as nat);
            lemma_u64_pow2_no_overflow(e as nat);
            lemma_u64_shl_is_mul(1u64, e);
            vbits::prim_read::lemma_p2_mono(e as nat, 13);
            reveal_with_fuel(p2, 14);
            assert(p2(13) == 8192);
        }
        let v: u64 = 1u64 << e;
        let m: u64 = 2 + d % 2;
        assert(v * m <= 8192 * 3) by (nonlinear_arith) requires v <= 8192, m <= 3;
        v * m + 1
    }
}

// ------------------------------------------------------- LZ77 copies

pub proof fn lemma_lz_copy(out: Seq<u8>, d: nat, len: nat)
    ensures
        lz_copy(out, d, len).len() == out.len() + len,
        lz_copy(out, d, len).take(out.len() as int) =~= out,
    decreases len,
{
    if len > 0 {
        let o1 = out.push(out[out.len() - d]);
        lemma_lz_copy(o1, d, (len - 1) as nat);
        assert(lz_copy(o1, d, (len - 1) as nat).take(out.len() as int)
               =~= lz_copy(o1, d, (len - 1) as nat).take(o1.len() as int).take(out.len() as int));
    }
}

/// A block's symbols only add to the output.
pub proof fn lemma_syms_grow(lit: Seq<u8>, dist: Seq<u8>, b: Seq<bool>, p: int, out: Seq<u8>)
    ensures inflate_syms(lit, dist, b, p, out) matches Some((o, q)) ==> o.len() >= out.len(),
    decreases b.len() - p,
{
    match decode_sym(lit, b, p) {
        None => {}
        Some((s, p1)) => {
            if p1 <= p || p1 > b.len() {
            } else if s < 256 {
                lemma_syms_grow(lit, dist, b, p1, out.push(s as u8));
            } else if s == 256 || s > 285 {
            } else {
                match getbits(b, p1, len_extra(s)) {
                    None => {}
                    Some(e) => {
                        let len = len_base(s) + e;
                        let q2 = p1 + len_extra(s);
                        match decode_sym(dist, b, q2) {
                            None => {}
                            Some((ds, p3)) => {
                                if ds <= 29 {
                                    match getbits(b, p3, dist_extra(ds)) {
                                        None => {}
                                        Some(e2) => {
                                            let d = dist_base(ds) + e2;
                                            let p4 = p3 + dist_extra(ds);
                                            if !(d > out.len() || p4 <= p || p4 > b.len()) {
                                                lemma_lz_copy(out, d, len);
                                                lemma_syms_grow(lit, dist, b, p4, lz_copy(out, d, len));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// The output buffer: the output so far is `out@.take(n)`; the rest of
/// `out` is scratch, so that literals and copies are stores, not pushes, and
/// a copy may write a few bytes past its end.
pub open spec fn max_len() -> nat { 0x1000_0000_0000_0000 }

/// Make `out` at least `need` long, keeping the output so far.
#[inline]
pub fn grow(out: &mut Vec<u8>, n: usize, need: usize)
    requires n <= old(out)@.len(), need <= 2 * max_len(),
    ensures
        final(out)@.len() >= need, final(out)@.len() >= old(out)@.len(),
        final(out)@.take(n as int) == old(out)@.take(n as int),
{
    if out.len() < need {
        let cur = out.len();
        let new = if cur > need - cur { 2 * cur } else { need };
        let ghost o = out@;
        out.resize(new, 0);
        proof { assert(out@.take(n as int) =~= o.take(n as int)); }
    }
}

/// A copy's bytes: the old output, then each byte the one `d` before it.
pub proof fn lemma_lz_char(o: Seq<u8>, d: nat, len: nat)
    requires 1 <= d <= o.len(),
    ensures
        lz_copy(o, d, len).len() == o.len() + len,
        forall|i: int| 0 <= i < o.len() ==> #[trigger] lz_copy(o, d, len)[i] == o[i],
        forall|i: int| o.len() <= i < o.len() + len ==>
            #[trigger] lz_copy(o, d, len)[i] == lz_copy(o, d, len)[i - d],
    decreases len,
{
    if len > 0 {
        let o1 = o.push(o[o.len() - d]);
        lemma_lz_char(o1, d, (len - 1) as nat);
        let t = lz_copy(o, d, len);
        assert(t == lz_copy(o1, d, (len - 1) as nat));
        assert forall|i: int| o.len() <= i < o.len() + len implies #[trigger] t[i] == t[i - d] by {
            if i == o.len() {
                assert(t[i] == o1[i]);
                assert(t[i - d] == o1[i - d]);
            }
        }
    }
}

/// Past its first `(m - 1) * d` bytes, a copy's bytes are also the ones
/// `m * d` back.
pub proof fn lemma_lz_mult(o: Seq<u8>, d: nat, len: nat, m: nat)
    requires 1 <= d <= o.len(), 1 <= m,
    ensures
        forall|i: int| o.len() + (m - 1) * d <= i < o.len() + len ==>
            #[trigger] lz_copy(o, d, len)[i] == lz_copy(o, d, len)[i - m * d],
    decreases m,
{
    lemma_lz_char(o, d, len);
    let t = lz_copy(o, d, len);
    if m > 1 {
        lemma_lz_mult(o, d, len, (m - 1) as nat);
        assert forall|i: int| o.len() + (m - 1) * d <= i < o.len() + len implies
            #[trigger] t[i] == t[i - m * d] by {
            assert(i >= o.len());
            assert(t[i] == t[i - d]);
            assert(o.len() + (m - 2) * d <= i - d) by (nonlinear_arith)
                requires o.len() + (m - 1) * d <= i, m >= 2;
            assert(i - d < o.len() + len);
            assert(t[i - d] == t[(i - d) - (m - 1) * d]);
            assert((i - d) - (m - 1) * d == i - m * d) by (nonlinear_arith);
        }
    } else {
        assert forall|i: int| o.len() + (m - 1) * d <= i < o.len() + len implies
            #[trigger] t[i] == t[i - m * d] by {
            assert(m * d == d) by (nonlinear_arith) requires m == 1;
        }
    }
}

/// Copy `t[i] = out[i - dd]` for `i` from `n + k0` to `n + len`, eight
/// bytes at a time: `dd >= 8`, so each eight come from bytes already there.
#[inline(always)]
pub fn copy_words(out: &mut Vec<u8>, n: usize, dd: usize, k0: usize, len: usize,
              Ghost(t): Ghost<Seq<u8>>)
    requires
        8 <= dd <= n + k0, k0 <= len, n + len + 8 <= old(out)@.len(), len < 0x400_0000,
        t.len() == n + len,
        forall|i: int| 0 <= i < n + k0 ==> #[trigger] old(out)@[i] == t[i],
        forall|i: int| n + k0 <= i < n + len ==> #[trigger] t[i] == t[i - dd],
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|i: int| 0 <= i < n + len ==> #[trigger] final(out)@[i] == t[i],
{
    let pl = out.len();
    let mut k: usize = k0;
    while k < len
        invariant
            8 <= dd <= n + k0, k0 <= k, k <= len + 7, n + len + 8 <= pl, out@.len() == pl, len < 0x400_0000,
            t.len() == n + len,
            forall|i: int| n + k0 <= i < n + len ==> #[trigger] t[i] == t[i - dd],
            forall|i: int| 0 <= i < n + k && i < n + len ==> #[trigger] out@[i] == t[i],
        decreases len + 8 - k,
    {
        let ghost old_out = out@;
        let src = n + k - dd;
        out.as_mut_slice().copy_within(src..src + 8, n + k);
        proof {
            assert forall|i: int| 0 <= i < n + k + 8 && i < n + len implies #[trigger] out@[i] == t[i] by {
                if i >= n + k {
                    assert(out@[i] == old_out[src + (i - (n + k))]);
                    assert(src + (i - (n + k)) == i - dd);
                    assert(old_out[i - dd] == t[i - dd]);
                }
            }
        }
        k = k + 8;
    }
}

/// One step of `copy_words`: `t[i] = out[i - dd]` for the eight `i` from
/// `n + k`.
#[inline(always)]
pub fn copy8(out: &mut Vec<u8>, n: usize, dd: usize, k: usize, len: usize, Ghost(t): Ghost<Seq<u8>>)
    requires
        8 <= dd <= n, k < len, n + k + 8 <= old(out)@.len(), len < 0x400_0000,
        t.len() == n + len,
        forall|i: int| 0 <= i < n + k ==> #[trigger] old(out)@[i] == t[i],
        forall|i: int| n <= i < n + len ==> #[trigger] t[i] == t[i - dd],
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|i: int| 0 <= i < n + k + 8 && i < n + len ==> #[trigger] final(out)@[i] == t[i],
{
    let ghost old_out = out@;
    let ol = out.len();
    assert(n + k + 8 <= ol);
    let src = (n - dd) + k;
    out.as_mut_slice().copy_within(src..src + 8, n + k);
    proof {
        assert forall|i: int| 0 <= i < n + k + 8 && i < n + len implies #[trigger] out@[i] == t[i] by {
            if i >= n + k {
                assert(out@[i] == old_out[src + (i - (n + k))]);
                assert(src + (i - (n + k)) == i - dd);
                assert(old_out[i - dd] == t[i - dd]);
            }
        }
    }
}

/// Append a copy of `len` bytes from `d` back to the output `out@.take(n)`.
#[inline]
pub fn copy_match(out: &mut Vec<u8>, n: usize, d: usize, len: usize)
    requires 1 <= d <= n, n + len + 8 <= old(out)@.len(), len < 0x400_0000,
    ensures
        final(out)@.len() == old(out)@.len(),
        final(out)@.take((n + len) as int) == lz_copy(old(out)@.take(n as int), d as nat, len as nat),
{
    let ghost o = out@.take(n as int);
    let ghost t = lz_copy(o, d as nat, len as nat);
    proof { lemma_lz_char(o, d as nat, len as nat); }
    if d >= len && len > 16 {
        // one copy: it reads only bytes from before the output grew
        let ghost old_out = out@;
        out.as_mut_slice().copy_within(n - d..n - d + len, n);
        proof {
            assert forall|i: int| 0 <= i < n + len implies #[trigger] out@[i] == t[i] by {
                if i >= n {
                    assert(out@[i] == old_out[(n - d) + (i - n)]);
                    assert(t[i] == t[i - d]);
                    assert(t[i - d] == o[i - d]);
                }
            }
        }
    } else if d >= 8 {
        copy_words(out, n, d, 0, len, Ghost(t));
    } else {
        // the first dd - d bytes one at a time, dd the least multiple of d
        // that is at least 8; the rest are the bytes dd back
        let m: usize = if d == 1 { 8 } else if d == 2 { 4 } else if d == 3 { 3 } else { 2 };
        // dd = m * d, case by case (so that no product is left to the solver)
        let dd: usize = if d == 1 { 8 } else if d == 2 { 8 } else if d == 3 { 9 } else { d + d };
        assert(dd == m * d && 8 <= dd < 16) by {
            if d == 1 { assert(m == 8); } else if d == 2 { assert(m == 4); } else if d == 3 { assert(m == 3); }
            else { assert(m == 2); }
        }
        let pre = if dd - d < len { dd - d } else { len };
        let pl = out.len();
        let mut k: usize = 0;
        while k < pre
            invariant
                1 <= d <= n, n + len + 8 <= pl, out@.len() == pl, len < 0x400_0000, k <= pre, pre <= len,
                t == lz_copy(o, d as nat, len as nat), o.len() == n, t.len() == n + len,
                forall|i: int| 0 <= i < n + k ==> #[trigger] out@[i] == t[i],
            decreases pre - k,
        {
            let x = out[n + k - d];
            proof {
                assert(out@[n + k - d] == t[n + k - d]);
                lemma_lz_char(o, d as nat, len as nat);
                assert(t[(n + k) as int] == t[(n + k) - d]);
            }
            out.set(n + k, x);
            k = k + 1;
        }
        proof {
            lemma_lz_mult(o, d as nat, len as nat, m as nat);
            assert(m * d == dd);
            assert((m - 1) * d == dd - d) by (nonlinear_arith) requires m * d == dd;
            assert(dd <= n + pre || pre == len);
        }
        if pre < len {
            copy_words(out, n, dd, pre, len, Ghost(t));
        }
    }
    proof { assert(out@.take((n + len) as int) =~= t); }
}

/// `t[i] = out[i - dd]` for the eight bytes from `n + k`, as one load and
/// one store: the first `dd` of them (all eight when `dd >= 8`) come from
/// bytes already in place; the rest, up to the copy's end, are left for
/// later steps. Writes up to eight bytes past the copy's end.
#[inline(always)]
fn chunk8(out: &mut Vec<u8>, n: usize, dd: usize, k: usize, len: usize, Ghost(t): Ghost<Seq<u8>>)
    requires
        1 <= dd <= n + k, n + k + 8 <= old(out)@.len(), t.len() == n + len,
        forall|i: int| 0 <= i < n + k && i < n + len ==> #[trigger] old(out)@[i] == t[i],
        forall|i: int| n + k <= i < n + len ==> #[trigger] t[i] == t[i - dd],
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|i: int| 0 <= i < n + k + 8 && i < n + k + dd && i < n + len ==> #[trigger] final(out)@[i] == t[i],
{
    let ghost old_out = out@;
    let ol = out.len();
    assert(n + k + 8 <= ol);
    let src = (n + k) - dd;
    vsimd::mem::copy8(out, src, n + k);
    proof {
        assert forall|i: int| 0 <= i < n + k + 8 && i < n + k + dd && i < n + len implies #[trigger] out@[i] == t[i] by {
            if i >= n + k {
                assert(out@[i] == old_out[src + i - (n + k)]);
                assert(old_out[i - dd] == t[i - dd]);
            }
        }
    }
}

/// `chunk8` for sixteen bytes.
#[inline(always)]
fn chunk16(out: &mut Vec<u8>, n: usize, dd: usize, k: usize, len: usize, Ghost(t): Ghost<Seq<u8>>)
    requires
        16 <= dd <= n + k, n + k + 16 <= old(out)@.len(), t.len() == n + len,
        forall|i: int| 0 <= i < n + k && i < n + len ==> #[trigger] old(out)@[i] == t[i],
        forall|i: int| n + k <= i < n + len ==> #[trigger] t[i] == t[i - dd],
    ensures
        final(out)@.len() == old(out)@.len(),
        forall|i: int| 0 <= i < n + k + 16 && i < n + len ==> #[trigger] final(out)@[i] == t[i],
{
    let ghost old_out = out@;
    let ol = out.len();
    assert(n + k + 16 <= ol);
    let src = (n + k) - dd;
    vsimd::mem::copy16(out, src, n + k);
    proof {
        assert forall|i: int| 0 <= i < n + k + 16 && i < n + len implies #[trigger] out@[i] == t[i] by {
            if i >= n + k {
                assert(out@[i] == old_out[src + i - (n + k)]);
                assert(old_out[i - dd] == t[i - dd]);
            }
        }
    }
}

/// A copy of `len` bytes from `d` back, appended to the output
/// `out@.take(n)`, for the fast loop, which leaves room for 16 bytes past
/// a longest copy: whole 16-byte (`d >= 16`) or 8-byte moves, the first 32
/// bytes without a test of the length (most copies are no longer). Below 8
/// back, the first moves step by `d` until `dd - d` bytes are in place, `dd`
/// the least multiple of `d` from 8 (for `d = 1`, one store of the byte
/// eight times), and the rest come from `dd` back.
#[inline(always)]
fn fast_copy(out: &mut Vec<u8>, n: usize, d: usize, len: usize)
    requires 1 <= d <= n, 3 <= len <= 258, n + 272 <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        final(out)@.take((n + len) as int) == lz_copy(old(out)@.take(n as int), d as nat, len as nat),
{
    let ghost o = out@.take(n as int);
    let ghost t = lz_copy(o, d as nat, len as nat);
    let ghost ol = out@.len();
    proof { lemma_lz_char(o, d as nat, len as nat); }
    if d >= 16 {
        chunk16(out, n, d, 0, len, Ghost(t));
        chunk16(out, n, d, 16, len, Ghost(t));
        let mut k: usize = 32;
        while k < len
            invariant
                16 <= d <= n, 3 <= len <= 258, n + 272 <= ol, out@.len() == ol, 32 <= k, k == 32 || k <= len + 15, k % 16 == 0,
                t.len() == n + len,
                forall|i: int| n <= i < n + len ==> #[trigger] t[i] == t[i - d],
                forall|i: int| 0 <= i < n + k && i < n + len ==> #[trigger] out@[i] == t[i],
            decreases len + 16 - k,
        {
            chunk16(out, n, d, k, len, Ghost(t));
            k = k + 16;
        }
    } else if d >= 8 {
        chunk8(out, n, d, 0, len, Ghost(t));
        chunk8(out, n, d, 8, len, Ghost(t));
        chunk8(out, n, d, 16, len, Ghost(t));
        chunk8(out, n, d, 24, len, Ghost(t));
        let mut k: usize = 32;
        while k < len
            invariant
                8 <= d <= n, 3 <= len <= 258, n + 272 <= ol, out@.len() == ol, 32 <= k, k == 32 || k <= len + 7,
                t.len() == n + len,
                forall|i: int| n <= i < n + len ==> #[trigger] t[i] == t[i - d],
                forall|i: int| 0 <= i < n + k && i < n + len ==> #[trigger] out@[i] == t[i],
            decreases len + 8 - k,
        {
            chunk8(out, n, d, k, len, Ghost(t));
            k = k + 8;
        }
    } else {
        let m: usize = if d == 1 { 8 } else if d == 2 { 4 } else if d == 3 { 3 } else { 2 };
        // dd = m * d, case by case (so that no product is left to the solver)
        let dd: usize = if d == 1 { 8 } else if d == 2 { 8 } else if d == 3 { 9 } else { d + d };
        assert(dd == m * d && 8 <= dd < 16) by {
            if d == 1 { assert(m == 8); } else if d == 2 { assert(m == 4); } else if d == 3 { assert(m == 3); }
            else { assert(m == 2); }
        }
        let mut k: usize;
        if d == 1 {
            let ghost old_out = out@;
            let x = vsimd::mem::get(out.as_slice(), n - 1);
            let xx = x as u64;
            let v = xx * 0x0101_0101_0101_0101u64;
            vsimd::mem::store_u64le(out, n, v);
            proof {
                assert forall|i: int| 0 <= i < n + 8 && i < n + len implies #[trigger] out@[i] == t[i] by {
                    if i >= n {
                        let jj = (i - n) as u64;
                        assert(((v >> (8 * jj)) & 0xff) == xx) by (bit_vector)
                            requires v == xx * 0x0101_0101_0101_0101u64, xx < 256, jj < 8;
                        assert(out@[i] == ((v >> (8 * (i - n)) as u64) & 0xff) as u8);
                        lemma_lz_mult(o, 1, len as nat, (i - n + 1) as nat);
                        assert(t[i] == t[i - (i - n + 1) * 1]);
                        assert(i - (i - n + 1) * 1 == n - 1);
                        assert(t[n - 1] == o[n - 1]);
                    }
                }
            }
            k = 8;
        } else {
            chunk8(out, n, d, 0, len, Ghost(t));
            k = d;
            if d == 2 {
                chunk8(out, n, d, 2, len, Ghost(t));
                chunk8(out, n, d, 4, len, Ghost(t));
                k = 6;
            } else if d == 3 {
                chunk8(out, n, d, 3, len, Ghost(t));
                k = 6;
            }
        }
        proof {
            lemma_lz_mult(o, d as nat, len as nat, m as nat);
            assert(m * d == dd);
            assert((m - 1) * d == dd - d) by (nonlinear_arith) requires m * d == dd;
            assert(dd - d <= k);
        }
        while k < len
            invariant
                1 <= d <= n, 8 <= dd < 16, dd - d <= k, 3 <= len <= 258, n + 272 <= ol, out@.len() == ol, k <= len + 7,
                t.len() == n + len,
                forall|i: int| n + (dd - d) <= i < n + len ==> #[trigger] t[i] == t[i - dd],
                forall|i: int| 0 <= i < n + k && i < n + len ==> #[trigger] out@[i] == t[i],
            decreases len + 8 - k,
        {
            chunk8(out, n, dd, k, len, Ghost(t));
            k = k + 8;
        }
    }
    proof { assert(out@.take((n + len) as int) =~= t); }
}

pub open spec fn outcome_n(r: Result<(usize, usize), Error>, sp: Option<(Seq<u8>, int)>, max_out: nat,
                           out: Seq<u8>) -> bool {
    match r {
        Ok((q, n)) => n <= out.len() && sp == Some((out.take(n as int), q as int)),
        Err(Error::Bad) => sp is None,
        Err(Error::TooBig) => sp matches Some((o, _)) ==> o.len() > max_out,
    }
}

/// The low `n` bits of `w`.
#[inline(always)]
fn low_bits(w: u64, n: u64) -> (v: u64)
    requires n <= 32,
    ensures v as nat == (w as nat) % p2(n as nat),
{
    proof {
        lemma_p2_eq_pow2(n as nat);
        lemma_u64_pow2_no_overflow(n as nat);
        lemma_u64_shl_is_mul(1u64, n);
    }
    let m: u64 = 1u64 << n;
    assert(m >= 1) by (bit_vector) requires m == 1u64 << n, n <= 32;
    let mm: u64 = m - 1;
    assert(w & mm == w % m) by (bit_vector) requires m == 1u64 << n, mm == m - 1, n <= 32;
    w & mm
}

/// What follows a length symbol `s` at `p1`: the length, the distance, and
/// the position after the distance's extra bits.
pub open spec fn len_dist(dist: Seq<u8>, b: Seq<bool>, p1: int, s: nat) -> Option<(nat, nat, int)> {
    match getbits(b, p1, len_extra(s)) {
        None => None,
        Some(e) => {
            let q2 = p1 + len_extra(s);
            match decode_sym(dist, b, q2) {
                None => None,
                Some((ds, p3)) =>
                    if ds > 29 {
                        None
                    } else {
                        match getbits(b, p3, dist_extra(ds)) {
                            None => None,
                            Some(e2) => Some((len_base(s) + e, dist_base(ds) + e2, p3 + dist_extra(ds))),
                        }
                    },
            }
        }
    }
}

/// The length and distance after length symbol `s`, from a window of at
/// least 33 bits at `p1` (5 extra, a distance code of at most 15 and at most
/// 13 extra).
#[inline(always)]
fn len_dist_x(dist: &Code, Ghost(dl): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>,
              p1: usize, avail: usize, w: u64, Ghost(k): Ghost<nat>, s: u64)
    -> (r: Result<(usize, usize, usize), Error>)
    requires
        code_wf(dist, dl), p1 + avail == b.len(), win_k(b, p1 as int, w, k), 33 <= k <= 64,
        257 <= s <= 285, b.len() <= 8 * max_input(),
    ensures
        match r {
            Ok((len, d, p4)) => len_dist(dl, b, p1 as int, s as nat) == Some((len as nat, d as nat, p4 as int))
                && p1 < p4 <= b.len() && 3 <= len <= 258 && 1 <= d && p4 <= p1 + 33,
            Err(_) => len_dist(dl, b, p1 as int, s as nat) is None,
        },
{
    let lx = len_extra_x(s);
    if lx as usize > avail {
        return Err(Error::Bad);
    }
    proof {
        lemma_win_getbits(b, p1 as int, w, k, lx as nat);
        reveal_with_fuel(p2, 6);
    }
    let e = low_bits(w, lx);
    let len: usize = (len_base_x(s) + e) as usize;
    let q2: usize = p1 + lx as usize;
    let w2 = w >> lx;
    proof { lemma_win_shift(b, p1 as int, w, k, lx); }
    let (ds, dln) = match decode_win(dist, Ghost(dl), Ghost(b), q2, avail - lx as usize, w2,
                                     Ghost((k - lx) as nat)) {
        None => return Err(Error::Bad),
        Some(x) => x,
    };
    proof { lemma_find_sym_adv(dl, b, q2 as int, 1); }
    if ds > 29 {
        return Err(Error::Bad);
    }
    let ds = ds as u64;
    let dx = dist_extra_x(ds);
    let p3: usize = q2 + dln as usize;
    if dx as usize > avail - (lx + dln) as usize {
        return Err(Error::Bad);
    }
    let w3 = w2 >> dln;
    proof {
        lemma_win_shift(b, q2 as int, w2, (k - lx) as nat, dln);
        lemma_win_getbits(b, p3 as int, w3, (k - lx - dln) as nat, dx as nat);
        reveal_with_fuel(p2, 14);
    }
    let e2 = low_bits(w3, dx);
    let d: usize = (dist_base_x(ds) + e2) as usize;
    Ok((len, d, p3 + dx as usize))
}

/// How a run of a block's symbols stopped.
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Run {
    /// At the end-of-block code.
    End,
    /// At a step that needs bits past the input's end, or might.
    Pause,
    /// At a step no continuation of the input has.
    Bad,
    /// At a step that would pass the output limit.
    TooBig,
}

/// A step that fails with 48 bits to spare fails for every continuation.
pub proof fn lemma_step_none_ext(ll: Seq<u8>, dl: Seq<u8>, b: Seq<bool>, f: Seq<bool>, p: int)
    requires is_prefix(b, f), sym_step(ll, dl, b, p) is None, 0 <= p, p + 48 <= b.len(),
    ensures sym_step(ll, dl, f, p) is None,
{
    if sym_step(ll, dl, f, p) is Some {
        lemma_sym_step_bound(ll, dl, f, p);
        let e = step_end(sym_step(ll, dl, f, p).unwrap());
        lemma_prefix_agree(b, f, p, e);
        lemma_sym_step_agree(ll, dl, b, f, p);
    }
}

/// A step decoded from the input is the step of every continuation of it.
pub proof fn lemma_step_ext(ll: Seq<u8>, dl: Seq<u8>, b: Seq<bool>, f: Seq<bool>, p: int, out: Seq<u8>)
    requires is_prefix(b, f), sym_step(ll, dl, b, p) is Some, 0 <= p,
    ensures
        sym_step(ll, dl, f, p) == sym_step(ll, dl, b, p),
        inflate_syms(ll, dl, f, p, out) == match sym_step(ll, dl, b, p) {
            None => None,
            Some(Step::Lit(x, p1)) => inflate_syms(ll, dl, f, p1, out.push(x)),
            Some(Step::End(p1)) => Some((out, p1)),
            Some(Step::Copy(len, d, p4)) =>
                if d > out.len() { None } else { inflate_syms(ll, dl, f, p4, lz_copy(out, d, len)) },
        },
{
    lemma_sym_step_bound(ll, dl, b, p);
    let e = step_end(sym_step(ll, dl, b, p).unwrap());
    lemma_prefix_agree(b, f, p, e);
    lemma_sym_step_agree(ll, dl, f, b, p);
    lemma_syms_unfold(ll, dl, f, p, out);
}

/// A block's symbols end after they start.
pub proof fn lemma_syms_pos(lit: Seq<u8>, dist: Seq<u8>, b: Seq<bool>, p: int, out: Seq<u8>)
    ensures inflate_syms(lit, dist, b, p, out) matches Some((o, q)) ==> p < q <= b.len(),
    decreases b.len() - p,
{
    lemma_syms_unfold(lit, dist, b, p, out);
    match sym_step(lit, dist, b, p) {
        None => {}
        Some(Step::Lit(x, p1)) => { lemma_syms_pos(lit, dist, b, p1, out.push(x)); }
        Some(Step::End(p1)) => {}
        Some(Step::Copy(len, d, p4)) => {
            if d <= out.len() { lemma_syms_pos(lit, dist, b, p4, lz_copy(out, d, len)); }
        }
    }
}

// ------------------------------------ length and distance tables (fast loop)

/// Base length and extra bits of lit/length symbol 257 + i, as
/// `base | extra << 16` (3.2.5); 0 past 28.
pub open spec fn len_tab() -> Seq<u32> {
    seq![3u32, 4, 5, 6, 7, 8, 9, 10, 65547, 65549, 65551, 65553, 131091, 131095, 131099, 131103, 196643, 196651, 196659, 196667, 262211, 262227, 262243, 262259, 327811, 327843, 327875, 327907, 258, 0, 0, 0]
}

pub const LEN_TAB: [u32; 32] = [3, 4, 5, 6, 7, 8, 9, 10, 65547, 65549, 65551, 65553, 131091, 131095, 131099, 131103, 196643, 196651, 196659, 196667, 262211, 262227, 262243, 262259, 327811, 327843, 327875, 327907, 258, 0, 0, 0];

/// Base distance and extra bits of distance symbol i, as
/// `base | extra << 16` (3.2.5); 0 past 29.
pub open spec fn dist_tab() -> Seq<u32> {
    seq![1u32, 2, 3, 4, 65541, 65543, 131081, 131085, 196625, 196633, 262177, 262193, 327745, 327777, 393345, 393409, 459009, 459137, 524801, 525057, 590849, 591361, 657409, 658433, 724993, 727041, 794625, 798721, 868353, 876545, 0, 0]
}

pub const DIST_TAB: [u32; 32] = [1, 2, 3, 4, 65541, 65543, 131081, 131085, 196625, 196633, 262177, 262193, 327745, 327777, 393345, 393409, 459009, 459137, 524801, 525057, 590849, 591361, 657409, 658433, 724993, 727041, 794625, 798721, 868353, 876545, 0, 0];

pub open spec fn len_tab_case(i: nat) -> bool {
    len_tab()[i as int] as nat == len_base(257 + i) + 65536 * len_extra(257 + i)
}

pub open spec fn len_tab_cases(n: nat) -> bool
    decreases n,
{
    if n == 0 { true } else { len_tab_case((n - 1) as nat) && len_tab_cases((n - 1) as nat) }
}

pub open spec fn dist_tab_case(i: nat) -> bool {
    dist_tab()[i as int] as nat == dist_base(i) + 65536 * dist_extra(i)
}

pub open spec fn dist_tab_cases(n: nat) -> bool
    decreases n,
{
    if n == 0 { true } else { dist_tab_case((n - 1) as nat) && dist_tab_cases((n - 1) as nat) }
}

proof fn lemma_len_tab_cases(n: nat, i: nat)
    requires len_tab_cases(n), i < n,
    ensures len_tab_case(i),
    decreases n,
{
    if i + 1 < n { lemma_len_tab_cases((n - 1) as nat, i); }
}

proof fn lemma_dist_tab_cases(n: nat, i: nat)
    requires dist_tab_cases(n), i < n,
    ensures dist_tab_case(i),
    decreases n,
{
    if i + 1 < n { lemma_dist_tab_cases((n - 1) as nat, i); }
}

/// The tables are the RFC's: LEN_TAB[s - 257] for s in 257..285,
/// DIST_TAB[d] for d in 0..29.
pub proof fn lemma_tabs()
    ensures
        LEN_TAB@ == len_tab(), DIST_TAB@ == dist_tab(),
        forall|i: nat| i < 29 ==> #[trigger] len_tab_case(i),
        forall|i: nat| i < 30 ==> #[trigger] dist_tab_case(i),
{
    assert(LEN_TAB@ =~= len_tab()) by (compute);
    assert(DIST_TAB@ =~= dist_tab()) by (compute);
    reveal_with_fuel(p2, 14);
    assert(len_tab_cases(29)) by (compute);
    assert(dist_tab_cases(30)) by (compute);
    assert forall|i: nat| i < 29 implies #[trigger] len_tab_case(i) by { lemma_len_tab_cases(29, i); }
    assert forall|i: nat| i < 30 implies #[trigger] dist_tab_case(i) by { lemma_dist_tab_cases(30, i); }
}

/// The length and distance after length symbol `s`, from a window of `k1`
/// bits at `p1` (at least 36, all inside the stream), with the tables:
/// also the number of bits they took and the window after them.
#[inline(always)]
fn len_dist_fast(dist: &Code, Ghost(dl): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>,
                 p1: usize, nbits: usize, w1: u64, k1: u64, s: u64)
    -> (r: Option<(usize, usize, u64, u64)>)
    requires
        code_wf(dist, dl), win_k(b, p1 as int, w1, k1 as nat), 36 <= k1 <= 64, p1 + k1 <= b.len(),
        b.len() == nbits, 257 <= s <= 285, b.len() <= 8 * max_input(),
    ensures
        match r {
            Some((len, d, used, w4)) => len_dist(dl, b, p1 as int, s as nat) == Some((len as nat, d as nat, p1 + used))
                && used <= 33 && used <= k1 && win_k(b, p1 + used, w4, (k1 - used) as nat)
                && 3 <= len <= 258 && 1 <= d,
            None => len_dist(dl, b, p1 as int, s as nat) is None,
        },
{
    proof { lemma_tabs(); }
    let s0: u64 = s - 257;
    let i = (s0 & 31) as usize;
    assert(s0 & 31 == s0) by (bit_vector) requires s0 <= 28;
    let le = LEN_TAB[i];
    let lx = (le >> 16) as u64;
    let base = (le & 0xffff) as u64;
    proof {
        assert(len_tab_case((s - 257) as nat));
        assert(le as nat == len_base(s as nat) + 65536 * len_extra(s as nat));
        assert(len_base(s as nat) <= 258 && len_extra(s as nat) <= 5);
        assert(le >> 16 == le / 65536 && le & 0xffff == le % 65536) by (bit_vector);
        assert(lx as nat == len_extra(s as nat) && base as nat == len_base(s as nat)) by (nonlinear_arith)
            requires le as nat == len_base(s as nat) + 65536 * len_extra(s as nat), len_base(s as nat) <= 258,
                lx as nat == le / 65536, base as nat == le % 65536;
        lemma_win_getbits(b, p1 as int, w1, k1 as nat, lx as nat);
        reveal_with_fuel(p2, 6);
    }
    let e = low_bits(w1, lx);
    let len: usize = (base + e) as usize;
    let q2: usize = p1 + lx as usize;
    let w2 = w1 >> lx;
    proof { lemma_win_shift(b, p1 as int, w1, k1 as nat, lx); }
    let (ds, dln) = match decode_win(dist, Ghost(dl), Ghost(b), q2, nbits - q2, w2, Ghost((k1 - lx) as nat)) {
        None => return None,
        Some(x) => x,
    };
    proof { lemma_find_sym_adv(dl, b, q2 as int, 1); }
    if ds > 29 {
        return None;
    }
    let di = (ds & 31) as usize;
    assert((ds & 31) == ds) by (bit_vector) requires ds <= 29;
    let de = DIST_TAB[di];
    let dx = (de >> 16) as u64;
    let dbase = (de & 0xffff) as u64;
    let p3: usize = q2 + dln as usize;
    let w3 = w2 >> dln;
    proof {
        assert(dist_tab_case(ds as nat));
        reveal_with_fuel(p2, 14);
        assert(dist_base(ds as nat) <= 24577 && dist_extra(ds as nat) <= 13);
        assert(de >> 16 == de / 65536 && de & 0xffff == de % 65536) by (bit_vector);
        assert(dx as nat == dist_extra(ds as nat) && dbase as nat == dist_base(ds as nat)) by (nonlinear_arith)
            requires de as nat == dist_base(ds as nat) + 65536 * dist_extra(ds as nat), dist_base(ds as nat) <= 24577,
                dx as nat == de / 65536, dbase as nat == de % 65536;
        lemma_win_shift(b, q2 as int, w2, (k1 - lx) as nat, dln);
        lemma_win_getbits(b, p3 as int, w3, (k1 - lx - dln) as nat, dx as nat);
    }
    let e2 = low_bits(w3, dx);
    let d: usize = (dbase + e2) as usize;
    let used = lx + dln + dx;
    proof { lemma_win_shift(b, p3 as int, w3, (k1 - lx - dln) as nat, dx); }
    Some((len, d, used, w3 >> dx))
}

// --------------------------------------------- packed tables (fast loop)

/// A lit/length table entry packed for the fast loop: a literal as
/// `2^31 + byte * 2^16 + code length`, end-of-block as `2^30 + code
/// length`, a length symbol as `base * 2^16 + code length * 2^8 + (code
/// length + extra bits)`, so that the bits a symbol takes are the entry's
/// low byte (the shift past them takes the entry as its count); `NO_LIT`
/// for no entry or a symbol past 285, so that one test (`>= 2^30`) finds
/// both it and end-of-block.
pub open spec fn pack_lit(e: u16) -> u32 {
    if e == 0 {
        NO_LIT
    } else {
        let s = (e % 1024) as nat;
        let l = (e / 1024) as nat;
        if s < 256 {
            (0x8000_0000 + s * 65536 + l) as u32
        } else if s == 256 {
            (0x4000_0000 + l) as u32
        } else if s <= 285 {
            (len_base(s) * 65536 + l * 256 + (l + len_extra(s))) as u32
        } else {
            NO_LIT
        }
    }
}

pub const NO_LIT: u32 = 0x4000_0100;

/// A distance table entry packed: `base * 2^16 + code length * 2^8 +
/// (code length + extra bits)`; 0 for no entry or a symbol past 29.
pub open spec fn pack_dist(e: u16) -> u32 {
    if e == 0 {
        0
    } else {
        let s = (e % 1024) as nat;
        let l = (e / 1024) as nat;
        if s <= 29 { (dist_base(s) * 65536 + l * 256 + (l + dist_extra(s))) as u32 } else { 0 }
    }
}

fn pack_lit_x(e: u16) -> (r: u32)
    ensures r == pack_lit(e),
{
    if e == 0 {
        return NO_LIT;
    }
    let s = (e % 1024) as u32;
    let l = (e / 1024) as u32;
    if s < 256 {
        0x8000_0000 + s * 65536 + l
    } else if s == 256 {
        0x4000_0000 + l
    } else if s <= 285 {
        proof { lemma_tabs(); assert(len_tab_case((s - 257) as nat)); }
        let le = LEN_TAB[(s - 257) as usize];
        let base = le % 65536;
        let lx = le / 65536;
        proof {
            assert(le as nat == len_base(s as nat) + 65536 * len_extra(s as nat));
            assert(len_base(s as nat) <= 258 && len_extra(s as nat) <= 5);
            assert(base as nat == len_base(s as nat) && lx as nat == len_extra(s as nat)) by (nonlinear_arith)
                requires le as nat == len_base(s as nat) + 65536 * len_extra(s as nat), len_base(s as nat) <= 258,
                    base == le % 65536, lx == le / 65536;
        }
        base * 65536 + l * 256 + (l + lx)
    } else {
        NO_LIT
    }
}

fn pack_dist_x(e: u16) -> (r: u32)
    ensures r == pack_dist(e),
{
    if e == 0 {
        return 0;
    }
    let s = (e % 1024) as u32;
    let l = (e / 1024) as u32;
    if s <= 29 {
        proof {
            lemma_tabs();
            assert(dist_tab_case(s as nat));
            reveal_with_fuel(p2, 14);
            assert(dist_base(s as nat) <= 24577 && dist_extra(s as nat) <= 13);
        }
        let de = DIST_TAB[s as usize];
        let base = de % 65536;
        let dx = de / 65536;
        proof {
            assert(base as nat == dist_base(s as nat) && dx as nat == dist_extra(s as nat)) by (nonlinear_arith)
                requires de as nat == dist_base(s as nat) + 65536 * dist_extra(s as nat), dist_base(s as nat) <= 24577,
                    base == de % 65536, dx == de / 65536;
        }
        base * 65536 + l * 256 + (l + dx)
    } else {
        0
    }
}

/// The packed table of a distance code (its entries repeat past its own
/// bits, so that the fast loop indexes it with the constant mask 1023).
fn pack_dist_tab(dist: &Code, Ghost(dl): Ghost<Seq<u8>>) -> (dt: [u32; 1024])
    requires code_wf(dist, dl),
    ensures forall|i: int| 0 <= i < 1024 ==> #[trigger] dt@[i] == pack_dist(dist.tbl@[(i as u64 & dist.mask) as int]),
{
    let mut dt = [0u32; 1024];
    let mut i: usize = 0;
    while i < 1024
        invariant
            i <= 1024, code_wf(dist, dl),
            forall|j: int| 0 <= j < i ==> #[trigger] dt@[j] == pack_dist(dist.tbl@[(j as u64 & dist.mask) as int]),
        decreases 1024 - i,
    {
        let dm = dist.mask;
        let di = i as u64 & dm;
        assert(di < 1024) by (bit_vector) requires di == i as u64 & dm, i < 1024;
        dt[i] = pack_dist_x(dist.tbl[di as usize]);
        i = i + 1;
    }
    dt
}

/// `load_le64_in` without its bounds checks: the fast loop's refill.
#[inline(always)]
fn load64(buf: &[u8], i: usize) -> (w: u64)
    requires i + 8 <= buf@.len(),
    ensures w as nat == lval(lview(buf@).subrange(8 * i as int, 8 * i as int + 64)),
{
    let w = vsimd::mem::load_u64le(buf, i);
    proof {
        let s = buf@;
        let j = i as int;
        vbits::lsb::lemma_le_window(s, j, s[j] as u64, s[j + 1] as u64, s[j + 2] as u64, s[j + 3] as u64,
                                    s[j + 4] as u64, s[j + 5] as u64, s[j + 6] as u64, s[j + 7] as u64, w);
    }
    w
}

/// All 64 bits of an 8-byte load at byte `i` are the stream's bits from
/// `8 * i`.
proof fn lemma_load_win(buf: Seq<u8>, i: int, x: u64)
    requires 0 <= i, i + 8 <= buf.len(), x as nat == lval(lview(buf).subrange(8 * i, 8 * i + 64)),
    ensures win_k(lbits(buf), 8 * i, x, 64),
{
    assert forall|j: int| 0 <= j < 64 && 8 * i + j < lbits(buf).len() implies
        #[trigger] lbits(buf)[8 * i + j] == ((x >> (j as u64)) & 1u64 == 1u64) by {
        let t = lview(buf).subrange(8 * i, 8 * i + 64);
        lemma_lval_bit(t, j);
        vbits::prim_read::lemma_p2_eq_pow2(j as nat);
        vstd::bits::lemma_u64_shr_is_div(x, j as u64);
        let y = x >> (j as u64);
        assert((y & 1u64 == 1u64) == (y % 2 == 1)) by (bit_vector);
        assert(t[j] == lview(buf)[8 * i + j]);
        assert(lview(buf)[8 * i + j] == lbits(buf)[8 * i + j]);
    }
}

/// The low `k` bits set.
pub open spec fn kmask(k: u64) -> u64 {
    ((1u64 << k) - 1) as u64
}

/// Refilling a window: its `k` bits, then 64 more from where they end.
proof fn lemma_refill(b: Seq<bool>, p: int, w: u64, k: u64, x: u64)
    requires win_k(b, p, w, k as nat), k < 64, win_k(b, p + k, x, 64),
    ensures win_k(b, p, (w & kmask(k)) | (x << k), 64),
{
    let m = kmask(k);
    assert(m == ((1u64 << k) - 1) as u64);
    let w2 = (w & m) | (x << k);
    assert forall|j: int| 0 <= j < 64 && p + j < b.len() implies
        #[trigger] b[p + j] == ((w2 >> (j as u64)) & 1u64 == 1u64) by {
        let jj = j as u64;
        if jj < k {
            assert((w2 >> jj) & 1u64 == (w >> jj) & 1u64) by (bit_vector)
                requires w2 == (w & m) | (x << k), m == ((1u64 << k) - 1) as u64, jj < k, k < 64;
        } else {
            let d = (jj - k) as u64;
            assert((w2 >> jj) & 1u64 == (x >> d) & 1u64) by (bit_vector)
                requires w2 == (w & m) | (x << k), m == ((1u64 << k) - 1) as u64, k <= jj, jj < 64, d == jj - k, k < 64;
            assert(b[(p + k) + (j - k)] == ((x >> ((j - k) as u64)) & 1u64 == 1u64));
        }
    }
}

/// Past its `k` bits a window holds only the stream's bits or zeros: each
/// set bit is the stream's, as far as the stream goes. A refill can then
/// OR the new bits in without clearing the old ones first.
pub open spec fn win_hi(b: Seq<bool>, p: int, w: u64) -> bool {
    forall|j: int| 0 <= j < 64 && p + j < b.len() && #[trigger] ((w >> (j as u64)) & 1u64) == 1u64 ==> b[p + j]
}

proof fn lemma_hi_shift(b: Seq<bool>, p: int, w: u64, m: u64)
    requires win_hi(b, p, w), m < 64,
    ensures win_hi(b, p + m, w >> m),
{
    assert forall|j: int| 0 <= j < 64 && p + m + j < b.len() && #[trigger] (((w >> m) >> (j as u64)) & 1u64) == 1u64
        implies b[p + m + j] by {
        let jj = j as u64;
        if m + jj < 64 {
            assert(((w >> m) >> jj) & 1u64 == (w >> ((m + jj) as u64)) & 1u64) by (bit_vector)
                requires m + jj < 64;
            assert(((w >> ((m + j) as u64)) & 1u64) == 1u64);
        } else {
            assert(((w >> m) >> jj) & 1u64 == 0) by (bit_vector)
                requires m + jj >= 64, m < 64, jj < 64;
        }
    }
}

proof fn lemma_full_hi(b: Seq<bool>, p: int, w: u64)
    requires win_k(b, p, w, 64),
    ensures win_hi(b, p, w),
{
    assert forall|j: int| 0 <= j < 64 && p + j < b.len() && #[trigger] ((w >> (j as u64)) & 1u64) == 1u64
        implies b[p + j] by {
        assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
    }
}

/// A window cut to its `k` bits.
proof fn lemma_mask_hi(b: Seq<bool>, p: int, w: u64, k: u64)
    requires win_k(b, p, w, k as nat), k < 64,
    ensures win_k(b, p, w & kmask(k), k as nat), win_hi(b, p, w & kmask(k)),
{
    let m = kmask(k);
    assert forall|j: int| 0 <= j < 64 implies
        #[trigger] (((w & m) >> (j as u64)) & 1u64) == if j < k { (w >> (j as u64)) & 1u64 } else { 0u64 } by {
        let jj = j as u64;
        assert(((w & m) >> jj) & 1u64 == if jj < k { (w >> jj) & 1u64 } else { 0u64 }) by (bit_vector)
            requires m == ((1u64 << k) - 1) as u64, k < 64, jj < 64;
    }
    assert forall|j: int| 0 <= j < k && p + j < b.len() implies
        #[trigger] b[p + j] == (((w & m) >> (j as u64)) & 1u64 == 1u64) by {
        assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
    }
}

/// Refilling a window whose bits past `k` are the stream's or zeros: OR in
/// 64 bits from where its `k` end.
proof fn lemma_refill_or(b: Seq<bool>, p: int, w: u64, k: u64, x: u64)
    requires win_k(b, p, w, k as nat), win_hi(b, p, w), k < 64, win_k(b, p + k, x, 64),
    ensures win_k(b, p, w | (x << k), 64), win_hi(b, p, w | (x << k)),
{
    let w2 = w | (x << k);
    assert forall|j: int| 0 <= j < 64 && p + j < b.len() implies
        #[trigger] b[p + j] == ((w2 >> (j as u64)) & 1u64 == 1u64) by {
        let jj = j as u64;
        if jj < k {
            assert((w2 >> jj) & 1u64 == (w >> jj) & 1u64) by (bit_vector)
                requires w2 == w | (x << k), jj < k, k < 64;
        } else {
            let d = (jj - k) as u64;
            assert((w2 >> jj) & 1u64 == ((w >> jj) & 1u64) | ((x >> d) & 1u64)) by (bit_vector)
                requires w2 == w | (x << k), k <= jj, jj < 64, d == jj - k, k < 64;
            assert(b[(p + k) + (j - k)] == ((x >> ((j - k) as u64)) & 1u64 == 1u64));
            let wb = (w >> jj) & 1u64;
            let xb = (x >> d) & 1u64;
            assert(wb <= 1u64 && xb <= 1u64) by (bit_vector) requires wb == (w >> jj) & 1u64, xb == (x >> d) & 1u64;
            assert(((wb | xb) == 1u64) == (wb == 1u64 || xb == 1u64)) by (bit_vector) requires wb <= 1u64, xb <= 1u64;
            if wb == 1u64 {
                assert(((w >> (j as u64)) & 1u64) == 1u64);
                assert(b[p + j]);
            }
        }
    }
    lemma_full_hi(b, p, w2);
}

/// The fast loop's state: output `o.take(n)` and position `p` decode, in
/// every continuation of `b`, as the block from `pos` after `g0` does.
pub open spec fn fast_inv(ll: Seq<u8>, dl: Seq<u8>, b: Seq<bool>, pos: int, g0: Seq<u8>, n0: nat,
                          p: int, n: nat, o: Seq<u8>) -> bool {
    &&& n0 <= n <= o.len() && o.take(n0 as int) == g0 && pos <= p
    &&& forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
            inflate_syms(ll, dl, f, p, o.take(n as int)) == inflate_syms(ll, dl, f, pos, g0)
}

/// One literal, if the next symbol is one: decoded from the window of `k`
/// bits ending at `q` (so starting at `q - k`), written to the output, and
/// the window's start moved past it.
#[inline(always)]
fn lit1(lit: &Code, Ghost(ll): Ghost<Seq<u8>>, Ghost(dl): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>,
        nbits: usize, q: usize, n: &mut usize, w: &mut u64, k: &mut u64, out: &mut Vec<u8>,
        Ghost(pos): Ghost<int>, Ghost(g0): Ghost<Seq<u8>>, Ghost(n0): Ghost<nat>) -> (ok: bool)
    requires
        code_wf(lit, ll), b.len() == nbits, q <= nbits,
        15 <= *old(k) <= 64, *old(k) <= q, win_k(b, q - *old(k), *old(w), *old(k) as nat),
        *old(n) < old(out)@.len(),
        fast_inv(ll, dl, b, pos, g0, n0, q - *old(k), *old(n) as nat, old(out)@),
    ensures
        final(out)@.len() == old(out)@.len(),
        *final(k) <= *old(k),
        win_k(b, q - *final(k), *final(w), *final(k) as nat),
        fast_inv(ll, dl, b, pos, g0, n0, q - *final(k), *final(n) as nat, final(out)@),
        ok ==> *final(n) == *old(n) + 1 && *final(k) < *old(k) && *final(k) + 15 >= *old(k),
        !ok ==> *final(n) == *old(n) && *final(k) == *old(k),
{
    let ghost p0 = q - *k;
    let (s, l) = match decode_fast(lit, Ghost(ll), Ghost(b), q, *k, nbits, *w) {
        None => return false,
        Some(x) => x,
    };
    if s >= 256 {
        return false;
    }
    let ghost lo = out@.take(*n as int);
    let ghost p1 = p0 + l;
    proof {
        lemma_find_sym_adv(ll, b, p0, 1);
        assert(sym_step(ll, dl, b, p0) == Some(Step::Lit(s as u8, p1)));
        lemma_win_shift(b, p0, *w, *k as nat, l);
    }
    let ghost n1 = *n;
    let ghost o1 = out@;
    let olen = out.len();
    assert(n1 < o1.len() && olen == o1.len());
    out.set(*n, s as u8);
    proof {
        assert(n0 <= n1);
        assert(out@.take(n1 + 1) =~= lo.push(s as u8));
        assert(out@.take(n0 as int) =~= lo.take(n0 as int));
        assert(lo.take(n0 as int) =~= o1.take(n0 as int));
        assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
            inflate_syms(ll, dl, f, p1, out@.take(n1 + 1)) == inflate_syms(ll, dl, f, pos, g0) by {
            lemma_step_ext(ll, dl, b, f, p0, lo);
        }
    }
    let nv = *n;
    assert(nv == n1 && n1 < olen);
    *n = nv + 1;
    *w = *w >> l;
    *k = *k - l;
    true
}

/// One symbol other than a literal, from a window of at least 56 bits
/// ending at `q`: 0 when a copy was made (the window's start moved past it;
/// its end stays at `q`), 1 at end-of-block (with the position after it),
/// 2 for anything the fast loop leaves to `syms_run` (nothing changed).
#[inline(never)]
fn other1(lit: &Code, dist: &Code, Ghost(ll): Ghost<Seq<u8>>, Ghost(dl): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>,
          nbits: usize, q: usize, n: &mut usize, w: &mut u64, k: &mut u64, out: &mut Vec<u8>,
          Ghost(pos): Ghost<int>, Ghost(g0): Ghost<Seq<u8>>, Ghost(n0): Ghost<nat>) -> (r: (u8, usize))
    requires
        code_wf(lit, ll), code_wf(dist, dl), b.len() == nbits, b.len() <= 8 * max_input(), q <= nbits,
        56 <= *old(k) <= 64, *old(k) <= q, win_k(b, q - *old(k), *old(w), *old(k) as nat),
        *old(n) + 272 <= old(out)@.len(),
        fast_inv(ll, dl, b, pos, g0, n0, q - *old(k), *old(n) as nat, old(out)@),
    ensures
        final(out)@.len() == old(out)@.len(),
        r.0 <= 2,
        r.0 == 0 ==> *final(k) < *old(k) && *final(k) <= q
            && win_k(b, q - *final(k), *final(w), *final(k) as nat) && *final(n) <= *old(n) + 258
            && fast_inv(ll, dl, b, pos, g0, n0, q - *final(k), *final(n) as nat, final(out)@),
        r.0 == 1 ==> r.1 <= nbits && q - *old(k) < r.1 && *final(n) == *old(n) && n0 <= *final(n) <= final(out)@.len()
            && final(out)@.take(n0 as int) == g0
            && forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                inflate_syms(ll, dl, f, pos, g0) == Some((final(out)@.take(*final(n) as int), r.1 as int)),
        r.0 == 2 ==> *final(k) == *old(k) && *final(n) == *old(n) && final(out)@ == old(out)@,
{
    let ghost p0 = q - *k;
    let ghost nn = *n;
    let ghost o0 = out@;
    let ghost lo = out@.take(*n as int);
    let olen = out.len();
    let (s, l) = match decode_fast(lit, Ghost(ll), Ghost(b), q, *k, nbits, *w) {
        None => return (2, 0),
        Some(x) => x,
    };
    proof {
        lemma_find_sym_adv(ll, b, p0, 1);
        lemma_win_shift(b, p0, *w, *k as nat, l);
    }
    if s == 256 {
        let p1 = q - *k as usize + l as usize;
        proof {
            assert(sym_step(ll, dl, b, p0) == Some(Step::End(p1 as int)));
            assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
                inflate_syms(ll, dl, f, pos, g0) == Some((lo, p1 as int)) by {
                lemma_step_ext(ll, dl, b, f, p0, lo);
            }
        }
        return (1, p1);
    }
    if s < 256 {
        // A literal whose code is longer than the table's bits.
        let ghost p1 = p0 + l;
        proof { assert(sym_step(ll, dl, b, p0) == Some(Step::Lit(s as u8, p1))); }
        let ghost n1 = *n;
        let ghost o1 = out@;
        out.set(*n, s as u8);
        proof {
            assert(n0 <= n1);
            assert(out@.take(n1 + 1) =~= lo.push(s as u8));
            assert(out@.take(n0 as int) =~= lo.take(n0 as int));
            assert(lo.take(n0 as int) =~= o1.take(n0 as int));
            assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
                inflate_syms(ll, dl, f, p1, out@.take(n1 + 1)) == inflate_syms(ll, dl, f, pos, g0) by {
                lemma_step_ext(ll, dl, b, f, p0, lo);
            }
        }
        let nv = *n;
        assert(nv == n1 && n1 + 272 <= olen);
        *n = nv + 1;
        *w = *w >> l;
        *k = *k - l;
        return (0, 0);
    }
    if s > 285 {
        return (2, 0);
    }
    let w1 = *w >> l;
    let k1 = *k - l;
    let p1 = q - k1 as usize;
    let (len, d, used, w4) = match len_dist_fast(dist, Ghost(dl), Ghost(b), p1, nbits, w1, k1, s as u64) {
        None => return (2, 0),
        Some(x) => x,
    };
    let ghost p4 = p1 + used;
    proof {
        assert(sym_step(ll, dl, b, p0) == Some(Step::Copy(len as nat, d as nat, p4)));
    }
    if d > *n {
        return (2, 0);
    }
    proof { lemma_lz_copy(lo, d as nat, len as nat); }
    if d >= 8 {
        // Short copies (most) without entering a loop.
        let ghost t = lz_copy(lo, d as nat, len as nat);
        proof { lemma_lz_char(lo, d as nat, len as nat); }
        copy8(out, *n, d, 0, len, Ghost(t));
        if len > 8 {
            copy8(out, *n, d, 8, len, Ghost(t));
            if len > 16 {
                copy_words(out, *n, d, 16, len, Ghost(t));
            }
        }
        proof { assert(out@.take((nn + len) as int) =~= t); }
    } else {
        copy_match(out, *n, d, len);
    }
    proof {
        assert(n0 <= nn);
        assert(out@.take(n0 as int) =~= out@.take((nn + len) as int).take(n0 as int));
        assert(lz_copy(lo, d as nat, len as nat).take(n0 as int) =~= lo.take(n0 as int)) by {
            assert(lz_copy(lo, d as nat, len as nat).take(n0 as int)
                =~= lz_copy(lo, d as nat, len as nat).take(lo.len() as int).take(n0 as int));
        }
        assert(lo.take(n0 as int) =~= o0.take(n0 as int));
        assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
            inflate_syms(ll, dl, f, p4, out@.take((nn + len) as int)) == inflate_syms(ll, dl, f, pos, g0) by {
            lemma_step_ext(ll, dl, b, f, p0, lo);
        }
    }
    let nv = *n;
    assert(nv == nn && nn + 272 <= olen && len <= 258);
    *n = nv + len;
    *w = w4;
    *k = k1 - used;
    (0, 0)
}

/// A table index by the constant mask 1023, then by the table's own.
proof fn lemma_mask1023(w: u64, tb: u64, mask: u64)
    requires tb_ok(tb), mask == (1u64 << tb) - 1,
    ensures (w & 1023) < 1024, ((w & 1023) & mask) == (w & mask), (w & mask) < 1024,
{
    assert((w & 1023) < 1024 && ((w & 1023) & mask) == (w & mask) && (w & mask) < 1024) by (bit_vector)
        requires mask == (1u64 << tb) - 1, 1 <= tb <= 10;
}

/// The fast loop's lit/length table: 12 bits, so that the codes of 11
/// and 12 bits most of a code's long ones are, are one lookup too. Its
/// ghost entries `et` say what each packed entry is: `et[i]` is 0, or the
/// code length times 1024 plus the symbol of the code the 12-bit window
/// `i` starts with.
pub open spec fn lt_ok(pt: &[u32; 4096], et: Seq<u16>, lens: Seq<u8>) -> bool {
    &&& et.len() == 4096
    &&& forall|i: int| 0 <= i < 4096 ==>
            #[trigger] pt@[i] == pack_lit(et[i]) && entry_ok(et[i], lens, wbits(i as u64, 12))
}

/// `lemma_tbl_sym` for the 12-bit table.
proof fn lemma_lt_sym(pt: &[u32; 4096], et: Seq<u16>, lens: Seq<u8>, b: Seq<bool>, p: int, w: u64, k: nat)
    requires lt_ok(pt, et, lens), win_k(b, p, w, k), 15 <= k <= 64, 0 <= p, p + 15 <= b.len(),
    ensures
        (w & 4095) < 4096,
        pt@[(w & 4095) as int] == pack_lit(et[(w & 4095) as int]),
        et[(w & 4095) as int] != 0 ==> ({
            let e = et[(w & 4095) as int];
            &&& 1 <= e / 1024 <= 15
            &&& find_sym(lens, b, p, 1) == Some(((e % 1024) as nat, p + (e / 1024) as int))
        }),
{
    let wi = w & 4095;
    assert(wi < 4096) by (bit_vector) requires wi == w & 4095;
    let ii = wi as int;
    assert(0 <= ii < 4096);
    assert(pt@[ii] == pack_lit(et[ii]) && entry_ok(et[ii], lens, wbits(ii as u64, 12)));
    assert(ii as u64 == wi);
    let e = et[wi as int];
    if e != 0 {
        let l = (e / 1024) as nat;
        let wb = wbits(wi, 12);
        let sy = (e % 1024) as nat;
        lemma_find_sym_adv(lens, wb, 0, 1);
        assert(l <= 12);
        assert forall|j: int| 0 <= j < l implies #[trigger] b[p + j] == wb[0 + j] by {
            let jj = j as u64;
            assert(((wi >> jj) & 1u64) == ((w >> jj) & 1u64)) by (bit_vector)
                requires wi == w & 4095, jj < 12;
            assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
        }
        lemma_find_sym_agree(lens, b, p, wb, 0, 1, sy, l);
    }
}

/// A table entry for a code of at most `tb` bits is one for every wider
/// window with the same low bits.
proof fn lemma_entry_lift(e: u16, lens: Seq<u8>, wi: u64, tb: nat, i: u64)
    requires e != 0, entry_ok(e, lens, wbits(wi, tb)), tb <= 12, wi == i & (((1u64 << (tb as u64)) - 1) as u64),
        1 <= tb <= 10,
    ensures entry_ok(e, lens, wbits(i, 12)),
{
    let l = (e / 1024) as nat;
    let sy = (e % 1024) as nat;
    let wb = wbits(wi, tb);
    let w12 = wbits(i, 12);
    lemma_find_sym_adv(lens, wb, 0, 1);
    assert(l <= tb);
    assert forall|j: int| 0 <= j < l implies #[trigger] w12[0 + j] == wb[0 + j] by {
        let jj = j as u64;
        let t = tb as u64;
        assert(((wi >> jj) & 1u64) == ((i >> jj) & 1u64)) by (bit_vector)
            requires wi == i & (((1u64 << t) - 1) as u64), jj < t, t <= 10;
    }
    lemma_find_sym_agree(lens, w12, 0, wb, 0, 1, sy, l);
}

/// `pack_lit12`'s loop invariants, past one more entry.
proof fn lemma_lt_step(pt0: Seq<u32>, et0: Seq<u16>, pt1: Seq<u32>, et1: Seq<u16>, ll: Seq<u8>, i: int,
                       tbl: Seq<u16>, mk: u64)
    requires
        0 <= i < 4096, pt0.len() == 4096, et0.len() == 4096,
        pt1 == pt0.update(i, pt1[i]), et1 == et0.update(i, et1[i]),
        pt1[i] == pack_lit(et1[i]), entry_ok(et1[i], ll, wbits(i as u64, 12)),
        tbl[(i as u64 & mk) as int] != 0 ==> et1[i] == tbl[(i as u64 & mk) as int],
        forall|j: int| 0 <= j < i ==> #[trigger] pt0[j] == pack_lit(et0[j]) && entry_ok(et0[j], ll, wbits(j as u64, 12)),
        forall|j: int| 0 <= j < i && #[trigger] tbl[(j as u64 & mk) as int] != 0 ==> et0[j] == tbl[(j as u64 & mk) as int],
    ensures
        et1.len() == 4096,
        forall|j: int| 0 <= j < i + 1 ==> #[trigger] pt1[j] == pack_lit(et1[j]) && entry_ok(et1[j], ll, wbits(j as u64, 12)),
        forall|j: int| 0 <= j < i + 1 && #[trigger] tbl[(j as u64 & mk) as int] != 0 ==> et1[j] == tbl[(j as u64 & mk) as int],
{
    assert forall|j: int| 0 <= j < i + 1 implies #[trigger] pt1[j] == pack_lit(et1[j]) && entry_ok(et1[j], ll, wbits(j as u64, 12)) by {
        if j < i { assert(pt1[j] == pt0[j] && et1[j] == et0[j]); assert(pt0[j] == pack_lit(et0[j])); }
    }
    assert forall|j: int| 0 <= j < i + 1 && #[trigger] tbl[(j as u64 & mk) as int] != 0 implies et1[j] == tbl[(j as u64 & mk) as int] by {
        if j < i { assert(et1[j] == et0[j]); }
    }
}

/// The 12-bit table: a window whose low `tb` bits have an entry takes it
/// (copied for the windows past 1024); one without is searched from
/// `tb + 1` bits within its 12 (`decode_resume`).
fn pack_lit12(lit: &Code, Ghost(ll): Ghost<Seq<u8>>) -> (r: ([u32; 4096], Ghost<Seq<u16>>))
    requires code_wf(lit, ll),
    ensures lt_ok(&r.0, r.1@, ll),
{
    let mut pt = [0u32; 4096];
    let ghost mut et: Seq<u16> = Seq::new(4096, |i: int| 0u16);
    let ghost tb = lit.tb;
    let ghost mk = lit.mask;
    let mut i: usize = 0;
    while i < 4096
        invariant
            i <= 4096, code_wf(lit, ll), et.len() == 4096, tb == lit.tb, mk == lit.mask,
            forall|j: int| 0 <= j < i ==>
                #[trigger] pt@[j] == pack_lit(et[j]) && entry_ok(et[j], ll, wbits(j as u64, 12)),
            forall|j: int| 0 <= j < i && #[trigger] lit.tbl@[(j as u64 & mk) as int] != 0 ==>
                et[j] == lit.tbl@[(j as u64 & mk) as int],
        decreases 4096 - i,
    {
        let wi = (i as u64) & lit.mask;
        proof {
            assert(wi < 1024 && wi < (1u64 << tb)) by (bit_vector)
                requires wi == (i as u64) & mk, mk == (1u64 << tb) - 1, 1 <= tb <= 10;
        }
        let e = lit.tbl[wi as usize];
        if e != 0 {
            proof {
                reveal(fast_wf);
                vbits::prim_read::lemma_p2_eq_pow2(tb as nat);
                vstd::bits::lemma_u64_pow2_no_overflow(tb as nat);
                vstd::bits::lemma_u64_shl_is_mul(1u64, tb);
                assert(entry_ok(e, ll, wbits(wi, tb as nat)));
                lemma_entry_lift(e, ll, wi, tb as nat, i as u64);
            }
            let v = if i >= 1024 {
                let lo = i - 1024 * (i / 1024);
                proof {
                    assert(lo < 1024 && (lo as u64 & mk) == wi) by (bit_vector)
                        requires lo == i - 1024 * (i / 1024), wi == (i as u64) & mk, mk == (1u64 << tb) - 1, 1 <= tb <= 10,
                            i < 4096;
                }
                pt[lo]
            } else {
                pack_lit_x(e)
            };
            let ghost pt0 = pt@;
            let ghost et0 = et;
            pt[i] = v;
            proof {
                et = et.update(i as int, e);
                lemma_lt_step(pt0, et0, pt@, et, ll, i as int, lit.tbl@, mk);
            }
        } else {
            let ghost wb = wbits(i as u64, 12);
            proof {
                assert forall|j: int| 0 <= j < 15 && 0 + j < wb.len() implies
                    #[trigger] wb[0 + j] == (((i as u64) >> (j as u64)) & 1u64 == 1u64) by {}
            }
            let r = crate::huff::decode_resume(lit, Ghost(ll), Ghost(wb), 0, 12, i as u64, wi);
            let e2: u16 = match r {
                Some((sy, l)) => {
                    proof {
                        lemma_find_sym_adv(ll, wb, 0, 1);
                        lemma_find_sym_sym(ll, wb, 0, 1);
                        assert(l <= 12 && sy < 1024);
                    }
                    (l * 1024 + sy as u64) as u16
                }
                None => 0,
            };
            proof {
                if e2 != 0 {
                    assert(e2 % 1024 == r.unwrap().0 && e2 / 1024 == r.unwrap().1);
                }
            }
            let v2 = pack_lit_x(e2);
            let ghost pt0 = pt@;
            let ghost et0 = et;
            assert forall|j: int| 0 <= j < i implies
                #[trigger] pt0[j] == pack_lit(et0[j]) && entry_ok(et0[j], ll, wbits(j as u64, 12)) by {
                assert(pt@[j] == pack_lit(et[j]) && entry_ok(et[j], ll, wbits(j as u64, 12)));
            }
            pt[i] = v2;
            proof {
                et = et.update(i as int, e2);
                lemma_lt_step(pt0, et0, pt@, et, ll, i as int, lit.tbl@, mk);
            }
        }
        i = i + 1;
    }
    (pt, Ghost(et))
}

pub open spec fn pt_ok(pt: &[u32; 1024], c: &Code) -> bool {
    forall|i: int| 0 <= i < 1024 ==> #[trigger] pt@[i] == pack_lit(c.tbl@[(i as u64 & c.mask) as int])
}

pub open spec fn dt_ok(dt: &[u32; 1024], c: &Code) -> bool {
    forall|i: int| 0 <= i < 1024 ==> #[trigger] dt@[i] == pack_dist(c.tbl@[(i as u64 & c.mask) as int])
}

/// The literal whose packed entry `pe` is the table's at the window's low
/// bits: written to the output, and the window's start moved past it. The
/// window holds `k + s` bits, of which `k` end at `q`.
#[inline(always)]
fn lit_take(lit: &Code, pt: &[u32; 4096], Ghost(et): Ghost<Seq<u16>>, Ghost(ll): Ghost<Seq<u8>>, Ghost(dl): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>,
            nbits: usize, q: usize, pe: u32, Ghost(s): Ghost<nat>,
            n: &mut usize, w: &mut u64, k: &mut u64, out: &mut Vec<u8>,
            Ghost(pos): Ghost<int>, Ghost(g0): Ghost<Seq<u8>>, Ghost(n0): Ghost<nat>)
    requires
        code_wf(lit, ll), lt_ok(pt, et, ll), b.len() == nbits, q <= nbits,
        15 <= *old(k), *old(k) + s <= 64, *old(k) <= q,
        win_k(b, q - *old(k), *old(w), (*old(k) + s) as nat), win_hi(b, q - *old(k), *old(w)),
        pe == pt@[(*old(w) & 4095) as int], pe >= 0x8000_0000,
        *old(n) < old(out)@.len(),
        fast_inv(ll, dl, b, pos, g0, n0, q - *old(k), *old(n) as nat, old(out)@),
    ensures
        final(out)@.len() == old(out)@.len(),
        *final(n) == *old(n) + 1 && *final(k) < *old(k) && *final(k) + 15 >= *old(k),
        win_k(b, q - *final(k), *final(w), (*final(k) + s) as nat), win_hi(b, q - *final(k), *final(w)),
        fast_inv(ll, dl, b, pos, g0, n0, q - *final(k), *final(n) as nat, final(out)@),
{
    let ghost p0 = q - *k;
    let ghost kk = (*k + s) as nat;
    proof { lemma_lt_sym(pt, et, ll, b, p0, *w, kk); }
    let ghost e = et[(*w & 4095) as int];
    let ghost sn = (e % 1024) as nat;
    let ghost ln = (e / 1024) as nat;
    proof {
        assert(e != 0 && sn < 256) by {
            reveal_with_fuel(p2, 14);
            if e == 0 || sn >= 256 {
                assert(ln <= 63);
                if sn == 256 { assert(pe == (0x4000_0000 + ln) as u32); }
                else if 257 <= sn <= 285 {
                    assert(len_base(sn) <= 258 && len_extra(sn) <= 5);
                    assert(pe as nat == len_base(sn) * 65536 + ln * 256 + (ln + len_extra(sn)));
                }
            }
        }
        assert(1 <= ln <= 15);
    }
    let l = (pe & 0xff) as u64;
    let sym = ((pe >> 16) & 0xff) as u8;
    proof {
        let s32 = sn as u32;
        let l32 = ln as u32;
        assert(pe == 0x8000_0000u32 + s32 * 65536 + l32);
        assert((pe & 0xff) == l32 && ((pe >> 16) & 0xff) == s32) by (bit_vector)
            requires pe == 0x8000_0000u32 + s32 * 65536 + l32, s32 < 256, l32 < 64;
    }
    let ghost lo = out@.take(*n as int);
    let ghost p1 = p0 + l;
    proof {
        lemma_find_sym_adv(ll, b, p0, 1);
        assert(sym_step(ll, dl, b, p0) == Some(Step::Lit(sym, p1)));
        lemma_win_shift(b, p0, *w, kk, l);
        lemma_hi_shift(b, p0, *w, l);
    }
    let ghost n1 = *n;
    let ghost o1 = out@;
    let olen = out.len();
    assert(n1 < o1.len() && olen == o1.len());
    vsimd::mem::vset(out, *n, sym);
    proof {
        assert(n0 <= n1);
        assert(out@.take(n1 + 1) =~= lo.push(sym));
        assert(out@.take(n0 as int) =~= lo.take(n0 as int));
        assert(lo.take(n0 as int) =~= o1.take(n0 as int));
        assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
            inflate_syms(ll, dl, f, p1, out@.take(n1 + 1)) == inflate_syms(ll, dl, f, pos, g0) by {
            lemma_step_ext(ll, dl, b, f, p0, lo);
        }
    }
    let nv = *n;
    assert(nv == n1 && n1 < olen);
    *n = nv + 1;
    *w = *w >> l;
    *k = *k - l;
}

/// The packed table's entry at the window's low bits.
#[inline(always)]
fn look(pt: &[u32; 4096], w: u64) -> (r: u32)
    ensures r == pt@[(w & 4095) as int],
{
    let i = w & 4095;
    assert(i < 4096) by (bit_vector) requires i == w & 4095;
    pt[i as usize]
}

proof fn lemma_len_bounds(s: nat)
    requires 257 <= s <= 285,
    ensures len_base(s) <= 258, len_extra(s) <= 5, 3 <= len_base(s),
{
}

proof fn lemma_dist_bounds(d: nat)
    requires d <= 29,
    ensures 1 <= dist_base(d) <= 24577, dist_extra(d) <= 13,
{
    reveal_with_fuel(p2, 14);
    if d >= 4 {
        vbits::prim_read::lemma_p2_mono(((d / 2) - 1) as nat, 13);
        assert(p2(13) == 8192);
        let e = ((d / 2) - 1) as nat;
        assert(p2(e) >= 1) by { vbits::bitspec::lemma_p2_pos(e); }
        assert(p2(e) * (2 + d % 2) <= 8192 * 3) by (nonlinear_arith) requires p2(e) <= 8192, d % 2 <= 1;
        assert(p2(e) * (2 + d % 2) >= 1) by (nonlinear_arith) requires p2(e) >= 1;
    }
}

/// The distance half of `len_dist`, from `q2`: the distance and the
/// position after its extra bits.
pub open spec fn dist_part(dl: Seq<u8>, b: Seq<bool>, q2: int) -> Option<(nat, int)> {
    match decode_sym(dl, b, q2) {
        None => None,
        Some((ds, p3)) =>
            if ds > 29 {
                None
            } else {
                match getbits(b, p3, dist_extra(ds)) {
                    None => None,
                    Some(e2) => Some((dist_base(ds) + e2, p3 + dist_extra(ds))),
                }
            },
    }
}

proof fn lemma_len_dist_parts(dl: Seq<u8>, b: Seq<bool>, p1: int, s: nat, e: nat, d: nat, p4: int)
    requires getbits(b, p1, len_extra(s)) == Some(e), dist_part(dl, b, p1 + len_extra(s)) == Some((d, p4)),
    ensures len_dist(dl, b, p1, s) == Some((len_base(s) + e, d, p4)),
{
}

/// The length after a length symbol from its packed entry `pe` (symbol
/// `sn`, code of `ln` bits at `p0`; the window `w` of `k` bits at `p0`):
/// the length, the bits the code and extra bits took, the window after.
#[inline(always)]
fn ld_len(Ghost(b): Ghost<Seq<bool>>, pe: u32, Ghost(sn): Ghost<nat>, Ghost(ln): Ghost<nat>,
          Ghost(p0): Ghost<int>, w: u64, Ghost(k): Ghost<nat>) -> (r: (usize, u64, u64))
    requires
        257 <= sn <= 285, 1 <= ln <= 15,
        pe as nat == len_base(sn) * 65536 + ln * 256 + (ln + len_extra(sn)),
        win_k(b, p0, w, k), 56 <= k <= 64, 0 <= p0, p0 + k <= b.len(), win_hi(b, p0, w),
    ensures
        ({
            let (len, tot, w2) = r;
            &&& tot == ln + len_extra(sn) && tot <= 20
            &&& getbits(b, p0 + ln, len_extra(sn)) == Some((len - len_base(sn)) as nat)
            &&& len >= len_base(sn) && 3 <= len <= 258
            &&& win_k(b, p0 + tot, w2, (k - tot) as nat) && win_hi(b, p0 + tot, w2)
        }),
{
    proof { lemma_len_bounds(sn); }
    let ghost lx = len_extra(sn);
    proof {
        let b32 = len_base(sn) as u32;
        let t32 = (ln + lx) as u32;
        let l32 = ln as u32;
        assert(pe == b32 * 65536 + l32 * 256 + t32);
        assert((pe & 0xff) == t32 && ((pe >> 8) & 0xff) == l32 && (pe >> 16) == b32) by (bit_vector)
            requires pe == b32 * 65536 + l32 * 256 + t32, b32 <= 258, t32 < 256, l32 < 256;
    }
    let tot = (pe & 0xff) as u64;
    let l = ((pe >> 8) & 0xff) as u64;
    let base = (pe >> 16) as usize;
    let lxe = tot - l;
    let w1 = w >> l;
    proof {
        lemma_win_shift(b, p0, w, k, l);
        lemma_win_getbits(b, p0 + l, w1, (k - l) as nat, lxe as nat);
        lemma_win_shift(b, p0, w, k, tot);
        lemma_hi_shift(b, p0, w, tot);
        reveal_with_fuel(p2, 6);
    }
    let el = low_bits(w1, lxe);
    assert(el < 32);
    ((base + el as usize), tot, w >> tot)
}

/// The distance from the packed distance table, from a window `w2` of `k2`
/// bits at `q2`: the distance, the bits its code and extra bits took, the
/// window after; `None` when the table has no entry there.
#[inline(always)]
fn ld_dist(dist: &Code, dt: &[u32; 1024], Ghost(dl): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>,
           Ghost(q2): Ghost<int>, w2: u64, Ghost(k2): Ghost<nat>) -> (r: Option<(usize, u64, u64)>)
    requires
        code_wf(dist, dl), dt_ok(dt, dist),
        win_k(b, q2, w2, k2), 36 <= k2 <= 64, 0 <= q2, q2 + k2 <= b.len(), win_hi(b, q2, w2),
    ensures
        match r {
            Some((d, dtot, w4)) => dist_part(dl, b, q2) == Some((d as nat, q2 + dtot)) && 1 <= dtot <= 28
                && win_k(b, q2 + dtot, w4, (k2 - dtot) as nat) && win_hi(b, q2 + dtot, w4) && 1 <= d,
            None => true,
        },
{
    proof { lemma_tbl_sym(dist, dl, b, q2, w2, k2); }
    let dwi = w2 & 1023;
    let ghost dwm = w2 & dist.mask;
    proof { lemma_mask1023(w2, dist.tb, dist.mask); }
    let de = dt[dwi as usize];
    if de == 0 {
        return None;
    }
    let ghost ed = dist.tbl@[dwm as int];
    let ghost ds = (ed % 1024) as nat;
    let ghost dln = (ed / 1024) as nat;
    proof {
        assert(ed != 0 && ds <= 29);
        assert(1 <= dln <= 15);
        lemma_dist_bounds(ds);
        let b32 = dist_base(ds) as u32;
        let t32 = (dln + dist_extra(ds)) as u32;
        let l32 = dln as u32;
        assert(de == b32 * 65536 + l32 * 256 + t32);
        assert((de & 0xff) == t32 && ((de >> 8) & 0xff) == l32 && (de >> 16) == b32) by (bit_vector)
            requires de == b32 * 65536 + l32 * 256 + t32, b32 <= 24577, t32 < 256, l32 < 256;
        lemma_find_sym_adv(dl, b, q2, 1);
    }
    let dtot = (de & 0xff) as u64;
    let dl8 = ((de >> 8) & 0xff) as u64;
    let dbase = (de >> 16) as usize;
    let dxe = dtot - dl8;
    let w3 = w2 >> dl8;
    proof {
        lemma_win_shift(b, q2, w2, k2, dl8);
        lemma_win_getbits(b, q2 + dl8, w3, (k2 - dl8) as nat, dxe as nat);
        lemma_win_shift(b, q2, w2, k2, dtot);
        lemma_hi_shift(b, q2, w2, dtot);
        reveal_with_fuel(p2, 14);
    }
    let ed2 = low_bits(w3, dxe);
    assert(ed2 < 8192);
    Some((dbase + ed2 as usize, dtot, w2 >> dtot))
}

/// A copy of `len` bytes from `d` back, appended to the output, keeping
/// the fast loop's state.
#[inline(always)]
fn copy_step(out: &mut Vec<u8>, n: &mut usize, d: usize, len: usize,
             Ghost(ll): Ghost<Seq<u8>>, Ghost(dl): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>,
             Ghost(p0): Ghost<int>, Ghost(p4): Ghost<int>,
             Ghost(pos): Ghost<int>, Ghost(g0): Ghost<Seq<u8>>, Ghost(n0): Ghost<nat>)
    requires
        1 <= d <= *old(n), 3 <= len <= 258, *old(n) + 272 <= old(out)@.len(), 0 <= p0,
        sym_step(ll, dl, b, p0) == Some(Step::Copy(len as nat, d as nat, p4)),
        fast_inv(ll, dl, b, pos, g0, n0, p0, *old(n) as nat, old(out)@),
    ensures
        final(out)@.len() == old(out)@.len(), *final(n) == *old(n) + len,
        fast_inv(ll, dl, b, pos, g0, n0, p4, *final(n) as nat, final(out)@),
{
    let ghost nn = *n;
    let ghost o0 = out@;
    let ghost lo = out@.take(*n as int);
    let olen = out.len();
    proof { lemma_lz_copy(lo, d as nat, len as nat); }
    fast_copy(out, *n, d, len);
    proof {
        assert(n0 <= nn);
        assert(out@.take(n0 as int) =~= out@.take((nn + len) as int).take(n0 as int));
        assert(lz_copy(lo, d as nat, len as nat).take(n0 as int) =~= lo.take(n0 as int)) by {
            assert(lz_copy(lo, d as nat, len as nat).take(n0 as int)
                =~= lz_copy(lo, d as nat, len as nat).take(lo.len() as int).take(n0 as int));
        }
        assert(lo.take(n0 as int) =~= o0.take(n0 as int));
        assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
            inflate_syms(ll, dl, f, p4, out@.take((nn + len) as int)) == inflate_syms(ll, dl, f, pos, g0) by {
            lemma_step_ext(ll, dl, b, f, p0, lo);
        }
    }
    let nv = *n;
    assert(nv == nn && nn + 272 <= olen && len <= 258);
    *n = nv + len;
}

/// A copy or end-of-block from the packed entry `pe`, the table's at the
/// window's low bits, as `other1`; 2 (nothing changed) for a symbol the
/// packed tables have no entry for. Taken just after a refill: the window
/// holds 64 bits, `k` of them ending at `q`.
#[inline(always)]
fn match_take(lit: &Code, dist: &Code, pt: &[u32; 4096], Ghost(et): Ghost<Seq<u16>>, dt: &[u32; 1024],
              Ghost(ll): Ghost<Seq<u8>>, Ghost(dl): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>,
              nbits: usize, q: usize, pe: u32, Ghost(s): Ghost<nat>,
              n: &mut usize, w: &mut u64, k: &mut u64, out: &mut Vec<u8>,
              Ghost(pos): Ghost<int>, Ghost(g0): Ghost<Seq<u8>>, Ghost(n0): Ghost<nat>) -> (r: (u8, usize))
    requires
        code_wf(lit, ll), code_wf(dist, dl), lt_ok(pt, et, ll), dt_ok(dt, dist),
        b.len() == nbits, b.len() <= 8 * max_input(), q <= nbits,
        56 <= *old(k), *old(k) + s == 64, *old(k) <= q,
        win_k(b, q - *old(k), *old(w), 64), win_hi(b, q - *old(k), *old(w)), q - *old(k) + 64 <= nbits,
        pe == pt@[(*old(w) & 4095) as int], pe < 0x8000_0000,
        *old(n) + 272 <= old(out)@.len(),
        fast_inv(ll, dl, b, pos, g0, n0, q - *old(k), *old(n) as nat, old(out)@),
    ensures
        final(out)@.len() == old(out)@.len(),
        r.0 <= 2,
        r.0 == 0 ==> *final(k) < *old(k) && *final(k) + 48 >= *old(k)
            && win_k(b, q - *final(k), *final(w), (*final(k) + s) as nat) && win_hi(b, q - *final(k), *final(w))
            && *final(n) <= *old(n) + 258
            && fast_inv(ll, dl, b, pos, g0, n0, q - *final(k), *final(n) as nat, final(out)@),
        r.0 == 1 ==> r.1 <= nbits && q - *old(k) < r.1 && *final(n) == *old(n) && n0 <= *final(n) <= final(out)@.len()
            && final(out)@.take(n0 as int) == g0
            && forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                inflate_syms(ll, dl, f, pos, g0) == Some((final(out)@.take(*final(n) as int), r.1 as int)),
        r.0 == 2 ==> *final(k) == *old(k) && *final(n) == *old(n) && *final(w) == *old(w) && final(out)@ == old(out)@,
{
    let ghost p0 = q - *k;
    let ghost lo = out@.take(*n as int);
    proof { lemma_lt_sym(pt, et, ll, b, p0, *w, 64); }
    let ghost wm = *w & 4095;
    if pe >= 0x4000_0000 {
        if pe == NO_LIT {
            return (2, 0);
        }
        // end-of-block
        let ghost e = et[wm as int];
        let ghost sn = (e % 1024) as nat;
        let ghost ln = (e / 1024) as nat;
        proof {
            assert(e != 0);
            assert(ln <= 63);
            assert(sn == 256) by {
                if sn < 256 { assert(pe as nat == 0x8000_0000 + sn * 65536 + ln); }
                if 257 <= sn <= 285 {
                    lemma_len_bounds(sn);
                    assert(pe as nat == len_base(sn) * 65536 + ln * 256 + (ln + len_extra(sn)));
                }
            }
            assert(1 <= ln <= 15);
            lemma_find_sym_adv(ll, b, p0, 1);
            let l32 = ln as u32;
            assert(pe == 0x4000_0000u32 + l32);
            assert(pe & 0xff == l32) by (bit_vector) requires pe == 0x4000_0000u32 + l32, l32 < 64;
        }
        let l = (pe & 0xff) as usize;
        let p1 = q - *k as usize + l;
        proof {
            assert(sym_step(ll, dl, b, p0) == Some(Step::End(p1 as int)));
            assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
                inflate_syms(ll, dl, f, pos, g0) == Some((lo, p1 as int)) by {
                lemma_step_ext(ll, dl, b, f, p0, lo);
            }
        }
        return (1, p1);
    }
    let ghost e = et[wm as int];
    let ghost sn = (e % 1024) as nat;
    let ghost ln = (e / 1024) as nat;
    proof {
        assert(e != 0);
        assert(ln <= 63);
        assert(257 <= sn <= 285) by {
            if sn < 256 { assert(pe as nat == 0x8000_0000 + sn * 65536 + ln); }
            if sn == 256 { assert(pe as nat == 0x4000_0000 + ln); }
        }
        assert(1 <= ln <= 15);
        lemma_find_sym_adv(ll, b, p0, 1);
        lemma_len_bounds(sn);
        assert(pe as nat == len_base(sn) * 65536 + ln * 256 + (ln + len_extra(sn)));
    }
    let (len, tot, w2) = ld_len(Ghost(b), pe, Ghost(sn), Ghost(ln), Ghost(p0), *w, Ghost(64));
    let (d, dtot, w4) = match ld_dist(dist, dt, Ghost(dl), Ghost(b), Ghost(p0 + tot), w2, Ghost((64 - tot) as nat)) {
        None => return (2, 0),
        Some(x) => x,
    };
    let used = tot + dtot;
    proof {
        lemma_len_dist_parts(dl, b, p0 + ln, sn, (len - len_base(sn)) as nat, d as nat, p0 + used);
        assert(sym_step(ll, dl, b, p0) == Some(Step::Copy(len as nat, d as nat, p0 + used)));
    }
    if d > *n {
        return (2, 0);
    }
    copy_step(out, n, d, len, Ghost(ll), Ghost(dl), Ghost(b), Ghost(p0), Ghost(p0 + used),
              Ghost(pos), Ghost(g0), Ghost(n0));
    *w = w4;
    *k = *k - used;
    (0, 0)
}

/// Decode a block's symbols from `pos` while the input has at least 8 bytes
/// past the bits in hand and the output has room for a longest copy: true
/// at end-of-block, false at anything else (a symbol it leaves to
/// `syms_run`, or the end of that room). The bits are a window `w` of `k`
/// bits ending at `q`, a byte boundary; each step begins with a refill to
/// 56 bits or more (one 8-byte load from `q`, which does not depend on the
/// symbol before), then takes up to three literals, or one other symbol.
/// The position is `q - k`, not kept.
fn fast_run(lit: &Code, dist: &Code, Ghost(ll): Ghost<Seq<u8>>, Ghost(dl): Ghost<Seq<u8>>,
            buf: &[u8], pos: usize, out: &mut Vec<u8>, n0: usize, max_out: usize)
    -> (r: (bool, usize, usize))
    requires
        code_wf(lit, ll), code_wf(dist, dl),
        buf.len() < max_input(), pos <= 8 * buf.len(),
        n0 <= max_out, n0 <= old(out)@.len(), max_out <= max_len(),
    ensures
        ({
            let (end, p, n) = r;
            let b = lbits(buf@);
            let g0 = old(out)@.take(n0 as int);
            let g = final(out)@.take(n as int);
            &&& p <= 8 * buf.len() && n <= max_out && n <= final(out)@.len()
            &&& final(out)@.len() == old(out)@.len()
            &&& n0 <= n && final(out)@.take(n0 as int) == g0 && pos <= p
            &&& end ==> forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                    inflate_syms(ll, dl, f, pos as int, g0) == Some((g, p as int))
            &&& !end ==> forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                    inflate_syms(ll, dl, f, pos as int, g0) == inflate_syms(ll, dl, f, p as int, g)
        }),
{
    let ghost b = lbits(buf@);
    let ghost g0 = out@.take(n0 as int);
    let nbits: usize = 8 * buf.len();
    let olen = out.len();
    let mut n = n0;
    if !(pos / 8 + 8 <= buf.len()) || olen < 272 || max_out < 258 {
        return (false, pos, n);
    }
    // Room for a longest copy and 8 bytes after it; 8 input bytes to load.
    let nlim = if olen - 272 < max_out - 258 { olen - 272 } else { max_out - 258 };
    let qlim = 8 * (buf.len() - 8);
    // The first window: from pos to the end of an 8-byte load, less than 64.
    let x0 = vbits::lsb::load_le64_in(buf, pos / 8);
    let off = (pos % 8) as u64;
    proof {
        lemma_load_win(buf@, (pos / 8) as int, x0);
        lemma_win_shift(b, 8 * (pos / 8) as int, x0, 64, off);
        lemma_full_hi(b, 8 * (pos / 8) as int, x0);
        lemma_hi_shift(b, 8 * (pos / 8) as int, x0, off);
    }
    let mut w: u64 = x0 >> off;
    let mut k: u64 = if off == 0 { 56 } else { 64 - off };
    let mut q: usize = pos + k as usize;
    // s: the bits the window holds past its k (all are the stream's)
    let ghost mut s: nat = if off == 0 { 8 } else { 0 };
    let (pt, Ghost(et)) = pack_lit12(lit, Ghost(ll));
    let dt = pack_dist_tab(dist, Ghost(dl));
    proof { assert(out@.take(n0 as int) =~= g0); }
    // the entry for the next symbol, looked up before the refill that
    // precedes its use, so that the refill is not on the lookup's path
    let mut pe = look(&pt, w);
    while q <= qlim && n <= nlim
        invariant
            code_wf(lit, ll), code_wf(dist, dl), lt_ok(&pt, et, ll), dt_ok(&dt, dist),
            buf.len() < max_input(), nbits == 8 * buf.len(), b == lbits(buf@), b.len() == nbits,
            buf.len() >= 8, qlim == 8 * (buf.len() - 8), nlim + 272 <= olen, nlim + 258 <= max_out,
            n <= max_out, max_out <= max_len(), pos <= nbits, out@.len() == olen,
            olen == old(out)@.len(), n0 <= max_out,
            k <= 63, k <= q, q % 8 == 0, q <= nbits, pos <= q - k,
            k + s <= 64, 15 <= k + s, win_k(b, q - k, w, (k + s) as nat), win_hi(b, q - k, w),
            pe == pt@[(w & 4095) as int],
            g0 == old(out)@.take(n0 as int),
            fast_inv(ll, dl, b, pos as int, g0, n0 as nat, q - k, n as nat, out@),
        decreases nbits - (q - k),
    {
        // Refill: k becomes 56 to 63, the end still on a byte boundary; the
        // window then holds 64 bits, and its low bits, so pe, are the same.
        let ghost p = q - k;
        let x = load64(buf, q / 8);
        proof {
            assert(q / 8 + 8 <= buf.len());
            lemma_load_win(buf@, (q / 8) as int, x);
            assert(8 * (q / 8) == q);
            lemma_win_weaken(b, p as int, w, (k + s) as nat, k as nat);
            lemma_refill_or(b, p as int, w, k, x);
            lemma_low12(b, p as int, w, (k + s) as nat, w | (x << k));
        }
        w = w | (x << k);
        let k2: u64 = k | 56;
        proof {
            assert(k2 == 56 + k % 8) by (bit_vector) requires k2 == k | 56, k <= 63;
            assert(p + 64 <= nbits);
        }
        q = q + (k2 - k) as usize;
        k = k2;
        proof { s = (64 - k2) as nat; }
        if pe >= 0x8000_0000 {
            // Up to three literals from one refill (each at most 15 bits).
            lit_take(lit, &pt, Ghost(et), Ghost(ll), Ghost(dl), Ghost(b), nbits, q, pe, Ghost(s), &mut n, &mut w, &mut k, out,
                     Ghost(pos as int), Ghost(g0), Ghost(n0 as nat));
            pe = look(&pt, w);
            if pe >= 0x8000_0000 {
                lit_take(lit, &pt, Ghost(et), Ghost(ll), Ghost(dl), Ghost(b), nbits, q, pe, Ghost(s), &mut n, &mut w, &mut k, out,
                         Ghost(pos as int), Ghost(g0), Ghost(n0 as nat));
                pe = look(&pt, w);
                if pe >= 0x8000_0000 {
                    lit_take(lit, &pt, Ghost(et), Ghost(ll), Ghost(dl), Ghost(b), nbits, q, pe, Ghost(s), &mut n, &mut w, &mut k, out,
                             Ghost(pos as int), Ghost(g0), Ghost(n0 as nat));
                    pe = look(&pt, w);
                }
            }
            continue;
        }
        let (r0, pe0) = match_take(lit, dist, &pt, Ghost(et), &dt, Ghost(ll), Ghost(dl), Ghost(b), nbits, q, pe, Ghost(s),
                                   &mut n, &mut w, &mut k, out, Ghost(pos as int), Ghost(g0), Ghost(n0 as nat));
        if r0 == 1 {
            proof { assert(n <= nlim); }
            return (true, pe0, n);
        } else if r0 == 0 {
            pe = look(&pt, w);
            continue;
        }
        proof { lemma_win_weaken(b, q - k, w, 64, k as nat); }
        // other1 is out of line, on copies, so that n, w and k stay in registers
        let mut n1 = n;
        let mut w1 = w;
        let mut k1 = k;
        let (r, pe1) = other1(lit, dist, Ghost(ll), Ghost(dl), Ghost(b), nbits, q, &mut n1, &mut w1, &mut k1, out,
                              Ghost(pos as int), Ghost(g0), Ghost(n0 as nat));
        n = n1;
        w = w1;
        k = k1;
        if r == 1 {
            proof { assert(n <= nlim); }
            return (true, pe1, n);
        } else if r == 2 {
            return (false, q - k as usize, n);
        }
        // Rare (long codes): other1 leaves bits past the window's k; clear
        // them, and refill without moving q, for the next lookup.
        proof { lemma_mask_hi(b, q - k, w, k); }
        assert(1u64 << k >= 1) by (bit_vector) requires k < 64;
        let m = (1u64 << k) - 1;
        assert(m == kmask(k));
        w = w & m;
        if q > qlim {
            return (false, q - k as usize, n);
        }
        let x1 = load64(buf, q / 8);
        proof {
            assert(q / 8 + 8 <= buf.len());
            lemma_load_win(buf@, (q / 8) as int, x1);
            assert(8 * (q / 8) == q);
            lemma_refill_or(b, q - k, w, k, x1);
        }
        w = w | (x1 << k);
        proof { s = (64 - k) as nat; }
        pe = look(&pt, w);
    }
    (false, q - k as usize, n)
}

/// A window of `m` bits is one of `n <= m`.
proof fn lemma_win_weaken(b: Seq<bool>, p: int, w: u64, m: nat, n: nat)
    requires win_k(b, p, w, m), n <= m,
    ensures win_k(b, p, w, n),
{
    assert forall|j: int| 0 <= j < n && p + j < b.len() implies
        #[trigger] b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64) by {
        assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
    }
}

proof fn lemma_bit_eq(b: Seq<bool>, p: int, w: u64, v: nat, w2: u64, j: u64)
    requires win_k(b, p, w, v), j < v, win_k(b, p, w2, 64), j < 64, 0 <= p, p + j < b.len(),
    ensures ((w >> j) & 1u64) == ((w2 >> j) & 1u64),
{
    assert(b[p + j] == ((w >> ((j as int) as u64)) & 1u64 == 1u64));
    assert(b[p + j] == ((w2 >> ((j as int) as u64)) & 1u64 == 1u64));
    assert(((w >> j) & 1u64) <= 1u64 && ((w2 >> j) & 1u64) <= 1u64) by (bit_vector);
}

/// Two windows at `p` of at least 12 bits have the same low 12 bits.
proof fn lemma_low12(b: Seq<bool>, p: int, w: u64, v: nat, w2: u64)
    requires win_k(b, p, w, v), 12 <= v, win_k(b, p, w2, 64), 0 <= p, p + 12 <= b.len(),
    ensures (w2 & 4095) == (w & 4095),
{
    lemma_bit_eq(b, p, w, v, w2, 0);
    lemma_bit_eq(b, p, w, v, w2, 1);
    lemma_bit_eq(b, p, w, v, w2, 2);
    lemma_bit_eq(b, p, w, v, w2, 3);
    lemma_bit_eq(b, p, w, v, w2, 4);
    lemma_bit_eq(b, p, w, v, w2, 5);
    lemma_bit_eq(b, p, w, v, w2, 6);
    lemma_bit_eq(b, p, w, v, w2, 7);
    lemma_bit_eq(b, p, w, v, w2, 8);
    lemma_bit_eq(b, p, w, v, w2, 9);
    lemma_bit_eq(b, p, w, v, w2, 10);
    lemma_bit_eq(b, p, w, v, w2, 11);
    assert((w2 & 4095) == (w & 4095)) by (bit_vector)
        requires
            ((w >> 0u64) & 1u64) == ((w2 >> 0u64) & 1u64), ((w >> 1u64) & 1u64) == ((w2 >> 1u64) & 1u64),
            ((w >> 2u64) & 1u64) == ((w2 >> 2u64) & 1u64), ((w >> 3u64) & 1u64) == ((w2 >> 3u64) & 1u64),
            ((w >> 4u64) & 1u64) == ((w2 >> 4u64) & 1u64), ((w >> 5u64) & 1u64) == ((w2 >> 5u64) & 1u64),
            ((w >> 6u64) & 1u64) == ((w2 >> 6u64) & 1u64), ((w >> 7u64) & 1u64) == ((w2 >> 7u64) & 1u64),
            ((w >> 8u64) & 1u64) == ((w2 >> 8u64) & 1u64), ((w >> 9u64) & 1u64) == ((w2 >> 9u64) & 1u64),
            ((w >> 10u64) & 1u64) == ((w2 >> 10u64) & 1u64), ((w >> 11u64) & 1u64) == ((w2 >> 11u64) & 1u64);
}

/// Decode a block's symbols from `pos`, appending to the output
/// `out@.take(n0)`, until end-of-block or a step it cannot take: the way it
/// stopped, the position, and the output's new length. What it says holds
/// for every stream that starts with `buf`, so a stream that arrives in
/// pieces can be decoded as far as its input goes and resumed. The bits come
/// from a window `w` of `k` bits at `p`, reloaded (56 bits) when fewer than
/// 15 are left for a lit/length code, and after each match.
#[verifier::spinoff_prover]
pub fn syms_run(lit: &Code, dist: &Code, Ghost(ll): Ghost<Seq<u8>>, Ghost(dl): Ghost<Seq<u8>>,
                buf: &[u8], pos: usize, out: &mut Vec<u8>, n0: usize, max_out: usize)
    -> (r: (Run, usize, usize))
    requires
        code_wf(lit, ll), code_wf(dist, dl),
        buf.len() < max_input(), pos <= 8 * buf.len(),
        n0 <= max_out, n0 <= old(out)@.len(), max_out <= max_len(),
    ensures
        ({
            let (run, p, n) = r;
            let b = lbits(buf@);
            let g0 = old(out)@.take(n0 as int);
            let g = final(out)@.take(n as int);
            &&& p <= 8 * buf.len() && n <= max_out && n <= final(out)@.len()
            &&& n0 <= n && final(out)@.take(n0 as int) == g0 && pos <= p
            &&& match run {
                Run::End => forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                    inflate_syms(ll, dl, f, pos as int, g0) == Some((g, p as int)),
                Run::Pause => (forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                        inflate_syms(ll, dl, f, pos as int, g0) == inflate_syms(ll, dl, f, p as int, g))
                    && sym_step(ll, dl, b, p as int) is None && 8 * buf.len() < p + 48,
                Run::Bad => forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                    inflate_syms(ll, dl, f, pos as int, g0) is None,
                Run::TooBig => forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                    (inflate_syms(ll, dl, f, pos as int, g0) matches Some((o, _)) ==> o.len() > max_out),
            }
        }),
{
    let ghost b = lbits(buf@);
    let ghost g0 = out@.take(n0 as int);
    let nbits: usize = 8 * buf.len();
    let mut p = pos;
    let mut n = n0;
    let mut w: u64 = 0;
    let mut k: u64 = 0;
    loop
        invariant
            code_wf(lit, ll), code_wf(dist, dl),
            buf.len() < max_input(), nbits == 8 * buf.len(), b == lbits(buf@), b.len() == nbits,
            p <= nbits, n <= max_out, n <= out@.len(), max_out <= max_len(), pos <= nbits,
            k <= 56, win_k(b, p as int, w, k as nat),
            g0 == old(out)@.take(n0 as int), n0 <= n, out@.take(n0 as int) == g0, pos <= p,
            forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                inflate_syms(ll, dl, f, p as int, out@.take(n as int)) == inflate_syms(ll, dl, f, pos as int, g0),
        decreases nbits - p,
    {
        let ghost pre = out@;
        grow(out, n, n + 272);
        proof { assert(out@.take(n0 as int) =~= out@.take(n as int).take(n0 as int)); assert(pre.take(n as int).take(n0 as int) =~= pre.take(n0 as int)); }
        if p / 8 + 8 <= buf.len() && n + 272 <= out.len() && n + 258 <= max_out {
            let ghost pre2 = out@;
            let (end, p2, n2) = fast_run(lit, dist, Ghost(ll), Ghost(dl), buf, p, out, n, max_out);
            proof {
                assert(out@.take(n0 as int) =~= out@.take(n as int).take(n0 as int));
                assert(pre2.take(n as int).take(n0 as int) =~= pre2.take(n0 as int));
            }
            if end {
                return (Run::End, p2, n2);
            }
            p = p2;
            n = n2;
            k = 0;
            let ghost pre3 = out@;
            grow(out, n, n + 272);
            proof { assert(out@.take(n0 as int) =~= out@.take(n as int).take(n0 as int)); assert(pre3.take(n as int).take(n0 as int) =~= pre3.take(n0 as int)); }
        }
        let ghost lo = out@.take(n as int);
        if k < 15 {
            w = peek_lsb(buf, p, 56);
            k = 56;
            proof { lemma_peek_win_k(buf@, p as int, 56, w); }
        }
        let avail = nbits - p;
        let (s, l) = match decode_win(lit, Ghost(ll), Ghost(b), p, avail, w, Ghost(k as nat)) {
            None => {
                proof { assert(sym_step(ll, dl, b, p as int) is None); }
                if avail >= 48 {
                    proof {
                        assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
                            inflate_syms(ll, dl, f, pos as int, g0) is None by {
                            lemma_step_none_ext(ll, dl, b, f, p as int);
                            lemma_syms_unfold(ll, dl, f, p as int, lo);
                        }
                    }
                    return (Run::Bad, p, n);
                }
                return (Run::Pause, p, n);
            }
            Some(x) => x,
        };
        let p1 = p + l as usize;
        proof { lemma_find_sym_adv(ll, b, p as int, 1); }
        if s < 256 {
            proof { assert(sym_step(ll, dl, b, p as int) == Some(Step::Lit(s as u8, p1 as int))); }
            if n >= max_out {
                proof {
                    assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
                        (inflate_syms(ll, dl, f, pos as int, g0) matches Some((o, _)) ==> o.len() > max_out) by {
                        lemma_step_ext(ll, dl, b, f, p as int, lo);
                        lemma_syms_grow(ll, dl, f, p1 as int, lo.push(s as u8));
                    }
                }
                return (Run::TooBig, p, n);
            }
            out.set(n, s as u8);
            proof {
                assert(out@.take(n as int + 1) =~= lo.push(s as u8));
                assert(out@.take(n0 as int) =~= lo.take(n0 as int));
                lemma_win_shift(b, p as int, w, k as nat, l);
                assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
                    inflate_syms(ll, dl, f, p1 as int, out@.take(n as int + 1)) == inflate_syms(ll, dl, f, pos as int, g0) by {
                    lemma_step_ext(ll, dl, b, f, p as int, lo);
                }
            }
            n = n + 1;
            p = p1;
            w = w >> l;
            k = k - l;
        } else if s == 256 {
            proof {
                assert(sym_step(ll, dl, b, p as int) == Some(Step::End(p1 as int)));
                assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
                    inflate_syms(ll, dl, f, pos as int, g0) == Some((lo, p1 as int)) by {
                    lemma_step_ext(ll, dl, b, f, p as int, lo);
                }
            }
            return (Run::End, p1, n);
        } else if s > 285 {
            proof { assert(sym_step(ll, dl, b, p as int) is None); }
            if avail >= 48 {
                proof {
                    assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
                        inflate_syms(ll, dl, f, pos as int, g0) is None by {
                        lemma_step_none_ext(ll, dl, b, f, p as int);
                        lemma_syms_unfold(ll, dl, f, p as int, lo);
                    }
                }
                return (Run::Bad, p, n);
            }
            return (Run::Pause, p, n);
        } else {
            let (w1, k1): (u64, u64) = if k - l >= 33 {
                proof { lemma_win_shift(b, p as int, w, k as nat, l); }
                (w >> l, k - l)
            } else {
                let w1 = peek_lsb(buf, p1, 56);
                proof { lemma_peek_win_k(buf@, p1 as int, 56, w1); }
                (w1, 56)
            };
            let (len, d, p4) = match len_dist_x(dist, Ghost(dl), Ghost(b), p1, nbits - p1, w1,
                                                Ghost(k1 as nat), s as u64) {
                Err(_) => {
                    proof { assert(sym_step(ll, dl, b, p as int) is None); }
                    if avail >= 48 {
                        proof {
                            assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
                                inflate_syms(ll, dl, f, pos as int, g0) is None by {
                                lemma_step_none_ext(ll, dl, b, f, p as int);
                                lemma_syms_unfold(ll, dl, f, p as int, lo);
                            }
                        }
                        return (Run::Bad, p, n);
                    }
                    return (Run::Pause, p, n);
                }
                Ok(x) => x,
            };
            proof {
                assert(sym_step(ll, dl, b, p as int) == Some(Step::Copy(len as nat, d as nat, p4 as int)));
            }
            if d > n {
                proof {
                    assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
                        inflate_syms(ll, dl, f, pos as int, g0) is None by {
                        lemma_step_ext(ll, dl, b, f, p as int, lo);
                    }
                }
                return (Run::Bad, p, n);
            }
            proof { lemma_lz_copy(lo, d as nat, len as nat); }
            if len > max_out - n {
                proof {
                    assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
                        (inflate_syms(ll, dl, f, pos as int, g0) matches Some((o, _)) ==> o.len() > max_out) by {
                        lemma_step_ext(ll, dl, b, f, p as int, lo);
                        lemma_syms_grow(ll, dl, f, p4 as int, lz_copy(lo, d as nat, len as nat));
                    }
                }
                return (Run::TooBig, p, n);
            }
            copy_match(out, n, d, len);
            proof {
                assert(out@.take(n0 as int) =~= out@.take((n + len) as int).take(n0 as int));
                assert(lz_copy(lo, d as nat, len as nat).take(n0 as int) =~= lo.take(n0 as int)) by {
                    assert(lz_copy(lo, d as nat, len as nat).take(n0 as int)
                        =~= lz_copy(lo, d as nat, len as nat).take(lo.len() as int).take(n0 as int));
                }
                assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
                    inflate_syms(ll, dl, f, p4 as int, out@.take((n + len) as int)) == inflate_syms(ll, dl, f, pos as int, g0) by {
                    lemma_step_ext(ll, dl, b, f, p as int, lo);
                }
            }
            n = n + len;
            p = p4;
            k = 0;
        }
    }
}

/// Decode a block's symbols from `pos` to its end-of-block code, appending
/// to the output `out@.take(n0)`: the position after end-of-block, and the
/// output's new length.
pub fn inflate_syms_x(lit: &Code, dist: &Code, Ghost(ll): Ghost<Seq<u8>>, Ghost(dl): Ghost<Seq<u8>>,
                      buf: &[u8], pos: usize, out: &mut Vec<u8>, n0: usize, max_out: usize)
    -> (r: Result<(usize, usize), Error>)
    requires
        code_wf(lit, ll), code_wf(dist, dl),
        buf.len() < max_input(), pos <= 8 * buf.len(),
        n0 <= max_out, n0 <= old(out)@.len(), max_out <= max_len(),
    ensures
        match r {
            Ok((q, n2)) => q <= 8 * buf.len() && n2 <= max_out,
            _ => true,
        },
        outcome_n(r, inflate_syms(ll, dl, lbits(buf@), pos as int, old(out)@.take(n0 as int)),
                  max_out as nat, final(out)@),
{
    let ghost b = lbits(buf@);
    let (run, p, n) = syms_run(lit, dist, Ghost(ll), Ghost(dl), buf, pos, out, n0, max_out);
    proof { assert(is_prefix(b, b)); }
    match run {
        Run::End => Ok((p, n)),
        Run::Pause => {
            proof { lemma_syms_unfold(ll, dl, b, p as int, out@.take(n as int)); }
            Err(Error::Bad)
        }
        Run::Bad => Err(Error::Bad),
        Run::TooBig => Err(Error::TooBig),
    }
}

// ---------------------------------------------------- stored blocks

/// The byte at a byte-aligned bit position is the buffer's byte.
proof fn lemma_aligned_byte(buf: Seq<u8>, k: int)
    requires 0 <= k < buf.len(),
    ensures lval(lbits(buf).subrange(8 * k, 8 * k + 8)) == buf[k] as nat,
{
    assert(lbits(buf).subrange(8 * k, 8 * k + 8) =~= lbits(seq![buf[k]])) by {
        assert forall|i: int| 0 <= i < 8 implies
            #[trigger] lbits(buf).subrange(8 * k, 8 * k + 8)[i] == lbits(seq![buf[k]])[i] by {
            assert((8 * k + i) / 8 == k) by (nonlinear_arith) requires 0 <= i < 8;
            assert((8 * k + i) % 8 == i) by (nonlinear_arith) requires 0 <= i < 8;
        }
    }
    lemma_lval_byte(buf[k]);
}

/// A stored block from `pos` (after its header bits): its bytes appended to
/// the output `out@.take(n)`; the position after them, and the new length.
fn stored_x(buf: &[u8], pos: usize, out: &mut Vec<u8>, n: usize, max_out: usize)
    -> (r: Result<(usize, usize), Error>)
    requires
        buf.len() < max_input(), pos <= 8 * buf.len(),
        n <= max_out, n <= old(out)@.len(), max_out <= max_len(),
    ensures
        match r {
            Ok((q, n2)) => q <= 8 * buf.len() && n2 <= max_out,
            _ => true,
        },
        outcome_n(r,
                  match stored(lbits(buf@), pos as int) {
                      Some((bytes, q)) => Some((old(out)@.take(n as int) + bytes, q)),
                      None => None,
                  },
                  max_out as nat, final(out)@),
{
    let ghost b = lbits(buf@);
    let nbits = 8 * buf.len();
    let q: usize = if pos % 8 == 0 { pos } else { pos + (8 - pos % 8) };
    if q > nbits {
        return Err(Error::Bad);
    }
    let len = match getbits_x(buf, q, 16) { None => return Err(Error::Bad), Some(v) => v };
    let nlen = match getbits_x(buf, q + 16, 16) { None => return Err(Error::Bad), Some(v) => v };
    proof {
        lemma_getbits_bound(b, q as int, 16);
        lemma_getbits_bound(b, q + 16, 16);
        reveal_with_fuel(p2, 17);
    }
    if len + nlen != 65535 {
        return Err(Error::Bad);
    }
    let len = len as usize;
    let start = q / 8 + 4;
    assert(q % 8 == 0 && 8 * (q / 8) == q) by (nonlinear_arith)
        requires q as int == (if pos % 8 == 0 { pos as int } else { pos + (8 - pos % 8) });
    if start > buf.len() || len > buf.len() - start {
        return Err(Error::Bad);
    }
    let ghost bytes = Seq::new(len as nat, |j: int| lval(b.subrange(q + 32 + 8 * j, q + 40 + 8 * j)) as u8);
    let ghost lo = out@.take(n as int);
    if len > max_out - n {
        return Err(Error::TooBig);
    }
    grow(out, n, n + len);
    let mut j: usize = 0;
    while j < len
        invariant
            j <= len, start + len <= buf.len(), start == q / 8 + 4, 8 * (q / 8) == q,
            b == lbits(buf@), n + len <= max_out, n + len <= out@.len(),
            bytes == Seq::new(len as nat, |j: int| lval(b.subrange(q + 32 + 8 * j, q + 40 + 8 * j)) as u8),
            out@.take(n + j) == lo + bytes.take(j as int),
        decreases len - j,
    {
        proof {
            lemma_aligned_byte(buf@, (start + j) as int);
            assert(8 * (start + j) == q + 32 + 8 * j);
            assert(bytes.take(j as int + 1) =~= bytes.take(j as int).push(buf@[start + j]));
        }
        let ghost o1 = out@;
        out.set(n + j, buf[start + j]);
        proof { assert(out@.take(n + j + 1) =~= o1.take(n + j).push(buf@[start + j])); }
        j = j + 1;
    }
    proof { assert(bytes.take(len as int) =~= bytes); }
    Ok((q + 32 + 8 * len, n + len))
}

// ------------------------------------------------ code length checks

/// The Kraft sum of `lens`, as the spec's `kraft`.
pub fn kraft_x(lens: &[u8]) -> (k: u64)
    requires lens.len() <= 320, lens_ok(lens@),
    ensures k as nat == kraft(lens@, lens.len() as int), k <= 320 * 16384,
{
    let mut k: u64 = 0;
    let mut i: usize = 0;
    while i < lens.len()
        invariant
            i <= lens.len(), lens.len() <= 320, lens_ok(lens@),
            k as nat == kraft(lens@, i as int), k <= i * 16384,
        decreases lens.len() - i,
    {
        let l = lens[i] as u64;
        assert(lens@[i as int] <= 15);
        if 1 <= l && l <= 15 {
            let e = 15 - l;
            proof {
                lemma_p2_eq_pow2(e as nat);
                lemma_u64_pow2_no_overflow(e as nat);
                lemma_u64_shl_is_mul(1u64, e);
                vbits::prim_read::lemma_p2_mono(e as nat, 14);
                reveal_with_fuel(p2, 15);
                assert(p2(14) == 16384);
            }
            k = k + (1u64 << e);
        }
        i = i + 1;
    }
    k
}

/// Whether some symbol has a code.
fn nonempty_x(lens: &[u8]) -> (r: bool)
    ensures r == nonempty(lens@),
{
    let mut i: usize = 0;
    while i < lens.len()
        invariant i <= lens.len(), forall|j: int| 0 <= j < i ==> lens@[j] == 0,
        decreases lens.len() - i,
    {
        if lens[i] != 0 {
            return true;
        }
        i = i + 1;
    }
    false
}

/// The number of codes of length 1.
fn count1_x(lens: &[u8]) -> (c: u64)
    requires lens.len() <= 320,
    ensures c as nat == bl_count(lens@, 1),
{
    let mut c: u64 = 0;
    let mut i: usize = 0;
    while i < lens.len()
        invariant i <= lens.len(), lens.len() <= 320, c as nat == count_len(lens@, 1, i as int), c <= i,
        decreases lens.len() - i,
    {
        if lens[i] == 1 {
            c = c + 1;
        }
        i = i + 1;
    }
    c
}

fn zlib_ok_x(lens: &[u8], cl_code: bool) -> (r: bool)
    requires lens.len() <= 320, lens_ok(lens@),
    ensures r == zlib_ok(lens@, cl_code),
{
    let k = kraft_x(lens);
    proof { reveal_with_fuel(p2, 16); assert(p2(15) == 32768 && p2(14) == 16384); }
    !nonempty_x(lens) || k == 32768 || (!cl_code && count1_x(lens) == 1 && k == 16384)
}

// ------------------------------------------------------ the fixed codes

pub fn fixed_lit_x() -> (v: Vec<u8>)
    ensures v@ == fixed_lit(),
{
    let mut v: Vec<u8> = Vec::with_capacity(288);
    let mut i: usize = 0;
    while i < 288
        invariant i <= 288, v@ =~= fixed_lit().take(i as int),
        decreases 288 - i,
    {
        let x: u8 = if i < 144 { 8 } else if i < 256 { 9 } else if i < 280 { 7 } else { 8 };
        proof { assert(fixed_lit().take(i as int + 1) =~= fixed_lit().take(i as int).push(x)); }
        v.push(x);
        i = i + 1;
    }
    proof { assert(fixed_lit().take(288) =~= fixed_lit()); }
    v
}

pub fn fixed_dist_x() -> (v: Vec<u8>)
    ensures v@ == fixed_dist(),
{
    let mut v: Vec<u8> = Vec::with_capacity(32);
    let mut i: usize = 0;
    while i < 32
        invariant i <= 32, v@ =~= fixed_dist().take(i as int),
        decreases 32 - i,
    {
        proof { assert(fixed_dist().take(i as int + 1) =~= fixed_dist().take(i as int).push(5u8)); }
        v.push(5);
        i = i + 1;
    }
    proof { assert(fixed_dist().take(32) =~= fixed_dist()); }
    v
}

// ---------------------------------------------------- the dynamic header

pub fn cl_order_x(i: u64) -> (r: usize)
    requires i < 19,
    ensures r as nat == cl_order(i as nat), r < 19,
{
    if i == 0 { 16 } else if i == 1 { 17 } else if i == 2 { 18 } else if i == 3 { 0 }
    else if i % 2 == 0 { (8 + (i - 4) / 2) as usize } else { (7 - (i - 5) / 2) as usize }
}

/// The code length code lengths.
fn read_cl_x(buf: &[u8], pos: usize, hclen: u64) -> (r: Result<(Vec<u8>, usize), Error>)
    requires buf.len() < max_input(), pos <= 8 * buf.len(), hclen <= 19,
    ensures
        match r {
            Ok((cl, q)) => read_cl(lbits(buf@), pos as int, hclen as nat, 0, Seq::new(19, |_i: int| 0u8))
                    == Some((cl@, q as int))
                && q <= 8 * buf.len() && cl@.len() == 19
                && forall|i: int| 0 <= i < 19 ==> #[trigger] cl@[i] < 8,
            Err(_) => read_cl(lbits(buf@), pos as int, hclen as nat, 0, Seq::new(19, |_i: int| 0u8)) is None,
        },
{
    let ghost b = lbits(buf@);
    let mut cl: Vec<u8> = vec![0u8; 19];
    let mut p = pos;
    let mut i: u64 = 0;
    proof { assert(cl@ =~= Seq::new(19, |_i: int| 0u8)); }
    while i < hclen
        invariant
            buf.len() < max_input(), p <= 8 * buf.len(), hclen <= 19, i <= hclen, b == lbits(buf@),
            cl@.len() == 19, forall|j: int| 0 <= j < 19 ==> #[trigger] cl@[j] < 8,
            read_cl(b, p as int, hclen as nat, i as nat, cl@)
                == read_cl(b, pos as int, hclen as nat, 0, Seq::new(19, |_i: int| 0u8)),
        decreases hclen - i,
    {
        let v = match getbits_x(buf, p, 3) {
            None => return Err(Error::Bad),
            Some(v) => v,
        };
        proof { lemma_getbits_bound(b, p as int, 3); reveal_with_fuel(p2, 4); }
        let k = cl_order_x(i);
        cl.set(k, v as u8);
        p = p + 3;
        i = i + 1;
    }
    Ok((cl, p))
}

/// Code lengths, decoded with the code length code, until there are `total`.
fn read_lens_x(cl: &Code, Ghost(cll): Ghost<Seq<u8>>, buf: &[u8], pos: usize, total: usize)
    -> (r: Result<(Vec<u8>, usize), Error>)
    requires code_wf(cl, cll), buf.len() < max_input(), pos <= 8 * buf.len(), total <= 320,
    ensures
        match r {
            Ok((v, q)) => read_lens(cll, lbits(buf@), pos as int, total as nat, Seq::empty())
                    == Some((v@, q as int))
                && q <= 8 * buf.len() && v@.len() == total && lens_ok(v@),
            Err(_) => read_lens(cll, lbits(buf@), pos as int, total as nat, Seq::empty()) is None,
        },
{
    let ghost b = lbits(buf@);
    let ghost target = read_lens(cll, b, pos as int, total as nat, Seq::empty());
    let mut acc: Vec<u8> = Vec::with_capacity(total);
    let mut p = pos;
    proof { assert(acc@ =~= Seq::<u8>::empty()); }
    while acc.len() < total
        invariant
            code_wf(cl, cll), buf.len() < max_input(), p <= 8 * buf.len(), total <= 320, b == lbits(buf@),
            acc@.len() <= total, lens_ok(acc@),
            read_lens(cll, b, p as int, total as nat, acc@) == target,
            target == read_lens(cll, lbits(buf@), pos as int, total as nat, Seq::empty()),
        decreases total - acc@.len(),
    {
        let (s, p1) = match decode(cl, Ghost(cll), buf, p) {
            None => return Err(Error::Bad),
            Some(x) => x,
        };
        proof { lemma_find_sym_adv(cll, b, p as int, 1); }
        if s < 16 {
            proof { assert(lens_ok(acc@.push(s as u8))) by {
                assert forall|i: int| 0 <= i < acc@.len() + 1 implies #[trigger] acc@.push(s as u8)[i] <= 15 by {
                    if i < acc@.len() { assert(acc@[i] <= 15); }
                }
            } }
            acc.push(s as u8);
            p = p1;
        } else {
            let (nb, base): (u64, usize) = if s == 16 { (2, 3) } else if s == 17 { (3, 3) } else { (7, 11) };
            let e = match getbits_x(buf, p1, nb) {
                None => return Err(Error::Bad),
                Some(e) => e,
            };
            proof { lemma_getbits_bound(b, p1 as int, nb as nat); reveal_with_fuel(p2, 8); }
            let rep: usize = base + e as usize;
            if s > 18 || (s == 16 && acc.len() == 0) || rep > total - acc.len() {
                return Err(Error::Bad);
            }
            let v: u8 = if s == 16 { acc[acc.len() - 1] } else { 0 };
            proof { if s == 16 { assert(acc@[acc@.len() - 1] <= 15); } }
            let ghost acc0 = acc@;
            let mut j: usize = 0;
            while j < rep
                invariant
                    j <= rep, acc0.len() + rep <= total, v <= 15, lens_ok(acc0),
                    acc@ =~= acc0 + Seq::new(j as nat, |_i: int| v),
                decreases rep - j,
            {
                acc.push(v);
                j = j + 1;
                proof { assert(acc@ =~= acc0 + Seq::new(j as nat, |_i: int| v)); }
            }
            proof {
                assert forall|i: int| 0 <= i < acc@.len() implies #[trigger] acc@[i] <= 15 by {
                    if i < acc0.len() { assert(acc0[i] <= 15); }
                }
            }
            p = p1 + nb as usize;
        }
    }
    Ok((acc, p))
}

fn copy_range(v: &Vec<u8>, a: usize, b: usize) -> (r: Vec<u8>)
    requires a <= b <= v@.len(),
    ensures r@ == v@.subrange(a as int, b as int),
{
    let mut r: Vec<u8> = Vec::with_capacity(b - a);
    let mut i = a;
    while i < b
        invariant a <= i <= b, b <= v@.len(), r@ =~= v@.subrange(a as int, i as int),
        decreases b - i,
    {
        r.push(v[i]);
        i = i + 1;
        proof { assert(r@ =~= v@.subrange(a as int, i as int)); }
    }
    r
}

/// A dynamic block's header: the lit/length and distance code lengths, the
/// position after them, and whether zlib accepts them.
pub fn dyn_header_x(buf: &[u8], pos: usize) -> (r: Result<(Vec<u8>, Vec<u8>, usize, bool), Error>)
    requires buf.len() < max_input(), pos <= 8 * buf.len(),
    ensures
        match r {
            Ok((lit, dist, q, st)) => dyn_header(lbits(buf@), pos as int) == Some((lit@, dist@, q as int, st))
                && q <= 8 * buf.len() && lit@.len() <= 286 && dist@.len() <= 32
                && lens_ok(lit@) && lens_ok(dist@),
            Err(_) => dyn_header(lbits(buf@), pos as int) is None,
        },
{
    let ghost b = lbits(buf@);
    let hlit = match getbits_x(buf, pos, 5) { None => return Err(Error::Bad), Some(v) => v };
    let hdist = match getbits_x(buf, pos + 5, 5) { None => return Err(Error::Bad), Some(v) => v };
    let hclen = match getbits_x(buf, pos + 10, 4) { None => return Err(Error::Bad), Some(v) => v };
    proof {
        lemma_getbits_bound(b, pos as int, 5);
        lemma_getbits_bound(b, pos + 5, 5);
        lemma_getbits_bound(b, pos + 10, 4);
        reveal_with_fuel(p2, 6);
    }
    let nlit = (hlit + 257) as usize;
    let ndist = (hdist + 1) as usize;
    if nlit > 286 {
        return Err(Error::Bad);
    }
    let (cl, q) = match read_cl_x(buf, pos + 14, hclen + 4) {
        Err(e) => return Err(e),
        Ok(x) => x,
    };
    proof { assert(lens_ok(cl@)) by { assert forall|i: int| 0 <= i < cl@.len() implies #[trigger] cl@[i] <= 15 by { assert(cl@[i] < 8); } } }
    if kraft_x(&cl) > 32768 {
        proof { reveal_with_fuel(p2, 16); }
        return Err(Error::Bad);
    }
    proof { reveal_with_fuel(p2, 16); }
    let clh = build_code(&cl, 7);
    let (lens, r) = match read_lens_x(&clh, Ghost(cl@), buf, q, nlit + ndist) {
        Err(e) => return Err(e),
        Ok(x) => x,
    };
    let lit = copy_range(&lens, 0, nlit);
    let dist = copy_range(&lens, nlit, nlit + ndist);
    proof {
        assert(lit@ =~= lens@.subrange(0, nlit as int));
        assert(dist@ =~= lens@.subrange(nlit as int, (nlit + ndist) as int));
        assert(lens_ok(lit@)) by { assert forall|i: int| 0 <= i < lit@.len() implies #[trigger] lit@[i] <= 15 by { assert(lens@[i] <= 15); } }
        assert(lens_ok(dist@)) by { assert forall|i: int| 0 <= i < dist@.len() implies #[trigger] dist@[i] <= 15 by { assert(lens@[nlit + i] <= 15); } }
    }
    if lit[256] == 0 || kraft_x(&lit) > 32768 || kraft_x(&dist) > 32768 {
        return Err(Error::Bad);
    }
    let st = zlib_ok_x(&cl, true) && zlib_ok_x(&lit, false) && zlib_ok_x(&dist, false) && ndist <= 30;
    Ok((lit, dist, r, st))
}

// ------------------------------------------------------------- blocks

pub open spec fn outcome3(r: Result<(usize, bool), Error>, sp: Option<(Seq<u8>, int, bool)>,
                          max_out: nat, got: Seq<u8>) -> bool {
    match r {
        Ok((q, st)) => sp == Some((got, q as int, st)),
        Err(Error::Bad) => sp is None,
        Err(Error::TooBig) => sp matches Some((o, _, _)) ==> o.len() > max_out,
    }
}

/// The fixed codes, once built.
pub open spec fn fixed_ok(f: Option<(Code, Code)>) -> bool {
    f matches Some((l, d)) ==> code_wf(&l, fixed_lit()) && code_wf(&d, fixed_dist())
}

fn block_x(buf: &[u8], pos: usize, btype: u64, out: &mut Vec<u8>, n: usize, max_out: usize,
           fixed: &mut Option<(Code, Code)>)
    -> (r: Result<(usize, usize, bool), Error>)
    requires
        buf.len() < max_input(), pos <= 8 * buf.len(),
        n <= max_out, n <= old(out)@.len(), max_out <= max_len(),
        fixed_ok(*old(fixed)),
    ensures
        fixed_ok(*final(fixed)),
        match r {
            Ok((q, n2, st)) => q <= 8 * buf.len() && n2 <= max_out && n2 <= final(out)@.len()
                && block(lbits(buf@), pos as int, btype as nat, old(out)@.take(n as int))
                    == Some((final(out)@.take(n2 as int), q as int, st)),
            Err(Error::Bad) => block(lbits(buf@), pos as int, btype as nat, old(out)@.take(n as int)) is None,
            Err(Error::TooBig) => block(lbits(buf@), pos as int, btype as nat, old(out)@.take(n as int))
                matches Some((o, _, _)) ==> o.len() > max_out,
        },
{
    if btype == 0 {
        match stored_x(buf, pos, out, n, max_out) {
            Ok((q, n2)) => Ok((q, n2, true)),
            Err(e) => Err(e),
        }
    } else if btype == 1 {
        if fixed.is_none() {
            let ll = fixed_lit_x();
            let dl = fixed_dist_x();
            proof {
                assert(lens_ok(ll@)) by { assert forall|i: int| 0 <= i < ll@.len() implies #[trigger] ll@[i] <= 15 by {} }
                assert(lens_ok(dl@)) by { assert forall|i: int| 0 <= i < dl@.len() implies #[trigger] dl@[i] <= 15 by {} }
            }
            *fixed = Some((build_code(&ll, 10), build_code(&dl, 5)));
        }
        let (lh, dh) = match fixed {
            Some(x) => (&x.0, &x.1),
            None => return Err(Error::Bad),  // not reached
        };
        match inflate_syms_x(lh, dh, Ghost(fixed_lit()), Ghost(fixed_dist()), buf, pos, out, n, max_out) {
            Ok((q, n2)) => Ok((q, n2, true)),
            Err(e) => Err(e),
        }
    } else if btype == 2 {
        let (ll, dl, q, st) = match dyn_header_x(buf, pos) {
            Err(e) => return Err(e),
            Ok(x) => x,
        };
        let lh = build_code(&ll, 10);
        let dh = build_code(&dl, 10);
        match inflate_syms_x(&lh, &dh, Ghost(ll@), Ghost(dl@), buf, q, out, n, max_out) {
            Ok((r, n2)) => Ok((r, n2, st)),
            Err(e) => Err(e),
        }
    } else {
        Err(Error::Bad)
    }
}

pub proof fn lemma_block_grow(b: Seq<bool>, p: int, btype: nat, out: Seq<u8>)
    ensures block(b, p, btype, out) matches Some((o, q, s)) ==> o.len() >= out.len(),
{
    if btype == 1 {
        lemma_syms_grow(fixed_lit(), fixed_dist(), b, p, out);
    } else if btype == 2 {
        match dyn_header(b, p) {
            None => {}
            Some((lit, dist, q, st)) => { lemma_syms_grow(lit, dist, b, q, out); }
        }
    }
}

pub proof fn lemma_blocks_grow(b: Seq<bool>, p: int, out: Seq<u8>, st: bool)
    ensures inflate_blocks(b, p, out, st) matches Some((o, q, s)) ==> o.len() >= out.len(),
    decreases b.len() - p,
{
    match (getbits(b, p, 1), getbits(b, p + 1, 2)) {
        (Some(bfinal), Some(btype)) => {
            lemma_block_grow(b, p + 3, btype, out);
            match block(b, p + 3, btype, out) {
                None => {}
                Some((o, q, s)) => {
                    if bfinal != 1 && !(q <= p || q > b.len()) {
                        lemma_blocks_grow(b, q, o, st && s);
                    }
                }
            }
        }
        _ => {}
    }
}

/// Decode a raw DEFLATE stream as if `out@.take(n0)` were the output
/// before it (a preset dictionary, which its distances may reach into): the
/// output grows after it, and the rest of `out` is scratch.
pub fn inflate_raw_after(buf: &[u8], out: &mut Vec<u8>, n0: usize, max_out: usize)
    -> (r: Result<(usize, usize, bool), Error>)
    requires buf.len() < max_input(), max_out <= max_len(), n0 <= max_out, n0 <= old(out)@.len(),
    ensures
        match r {
            Ok((n, q, st)) => n <= final(out)@.len() && q <= 8 * buf.len()
                && inflate_blocks(lbits(buf@), 0, old(out)@.take(n0 as int), true)
                    == Some((final(out)@.take(n as int), q as int, st)),
            Err(Error::Bad) => inflate_blocks(lbits(buf@), 0, old(out)@.take(n0 as int), true) is None,
            Err(Error::TooBig) => inflate_blocks(lbits(buf@), 0, old(out)@.take(n0 as int), true)
                matches Some((o, _, _)) ==> o.len() > max_out,
        },
{
    let ghost b = lbits(buf@);
    let nbits: usize = 8 * buf.len();
    let ghost g0 = out@.take(n0 as int);
    let mut n: usize = n0;
    let mut p: usize = 0;
    let mut st = true;
    let mut fixed: Option<(Code, Code)> = None;
    loop
        invariant
            fixed_ok(fixed),
            buf.len() < max_input(), nbits == 8 * buf.len(), b == lbits(buf@), b.len() == nbits,
            p <= nbits, n <= max_out, n <= out@.len(), max_out <= max_len(),
            g0 == old(out)@.take(n0 as int),
            inflate_blocks(b, p as int, out@.take(n as int), st) == inflate_blocks(b, 0, g0, true),
        decreases nbits - p,
    {
        let bfinal = match getbits_x(buf, p, 1) { None => return Err(Error::Bad), Some(v) => v };
        let btype = match getbits_x(buf, p + 1, 2) { None => return Err(Error::Bad), Some(v) => v };
        let ghost lo = out@.take(n as int);
        let (q, n2, s) = match block_x(buf, p + 3, btype, out, n, max_out, &mut fixed) {
            Err(e) => {
                proof {
                    if e == Error::TooBig {
                        match block(b, p + 3, btype as nat, lo) {
                            None => {}
                            Some((o, q, s)) => {
                                if bfinal != 1 && !(q <= p || q > b.len()) {
                                    lemma_blocks_grow(b, q, o, st && s);
                                }
                            }
                        }
                    }
                }
                return Err(e);
            }
            Ok(x) => x,
        };
        n = n2;
        if bfinal == 1 {
            return Ok((n, q, st && s));
        }
        if q <= p {
            return Err(Error::Bad);
        }
        p = q;
        st = st && s;
    }
}

/// Decode a raw DEFLATE stream into `out`, whose contents are scratch: the
/// data is `out@.take(n)` for the `n` returned, with the bits the stream took
/// and whether zlib accepts it. `out` is grown as needed and never shrunk, so
/// a buffer reused across calls is not cleared again. `Ok` is exactly the
/// spec's result; `Err(Bad)`, that it has none; `Err(TooBig)`, that it has
/// none or one longer than `max_out`.
pub fn inflate_raw_into(buf: &[u8], out: &mut Vec<u8>, max_out: usize)
    -> (r: Result<(usize, usize, bool), Error>)
    requires buf.len() < max_input(), max_out <= max_len(),
    ensures
        match r {
            Ok((n, q, st)) => n <= final(out)@.len() && q <= 8 * buf.len()
                && inflate(lbits(buf@)) == Some((final(out)@.take(n as int), q as nat, st)),
            Err(Error::Bad) => inflate(lbits(buf@)) is None,
            Err(Error::TooBig) => inflate(lbits(buf@)) matches Some((o, _, _)) ==> o.len() > max_out,
        },
{
    proof { assert(out@.take(0) =~= Seq::<u8>::empty()); }
    inflate_raw_after(buf, out, 0, max_out)
}

/// Decode a raw DEFLATE stream: the data, the bits the stream took, and
/// whether zlib accepts it. `Ok` is exactly the spec's result; `Err(Bad)`,
/// that it has none; `Err(TooBig)`, that it has none or one longer than
/// `max_out`.
pub fn inflate_raw(buf: &[u8], max_out: usize) -> (r: Result<(Vec<u8>, usize, bool), Error>)
    requires buf.len() < max_input(), max_out <= max_len(),
    ensures
        match r {
            Ok((o, q, st)) => inflate(lbits(buf@)) == Some((o@, q as nat, st)) && q <= 8 * buf.len(),
            Err(Error::Bad) => inflate(lbits(buf@)) is None,
            Err(Error::TooBig) => inflate(lbits(buf@)) matches Some((o, _, _)) ==> o.len() > max_out,
        },
{
    // a first guess at the output's size; it grows as needed
    let guess: usize = if buf.len() < max_out / 3 { 3 * buf.len() + 1024 } else { max_out };
    // from the allocator's zeroed memory (fresh pages are not filled again)
    let mut out: Vec<u8> = vec![0u8; guess];
    match inflate_raw_into(buf, &mut out, max_out) {
        Ok((n, q, st)) => {
            out.truncate(n);
            Ok((out, q, st))
        }
        Err(e) => Err(e),
    }
}

} // verus!








