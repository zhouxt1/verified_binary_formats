//! A bit window over the input, kept across fields and symbols: bits `p`
//! onwards of the stream are the low `k` bits of `w` (as far as the stream
//! goes). Loading 56 bits at a time spares a load per field.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
use vbits::lsb::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::{getbits, decode_sym};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::{find_sym, codebits, next_code};
use vdeflate::huff::*;
use crate::spec::*;
use crate::code::*;

verus! {

pub struct Br {
    pub w: u64,
    pub k: u64,
    pub p: usize,
}

/// The window holds only bits of the stream (`k` at most what is left), so
/// a field of at most `k` bits is in the stream.
pub open spec fn br_wf(buf: Seq<u8>, x: Br) -> bool {
    &&& x.p <= 8 * buf.len() && x.k <= 56 && buf_ok(buf)
    &&& x.k + x.p <= 8 * buf.len()
    &&& win_k(lbits(buf), x.p as int, x.w, x.k as nat)
}

/// A window at `p` with nothing in it yet.
pub fn br_at(buf: &[u8], p: usize) -> (r: Br)
    requires buf_ok(buf@), p <= 8 * buf.len(),
    ensures br_wf(buf@, r), r.p == p,
{
    Br { w: 0, k: 0, p }
}

/// A window at `p`: 56 bits, or all that is left.
#[inline(never)]
pub fn load_win(buf: &[u8], p: usize) -> (r: (u64, u64))
    requires buf_ok(buf@), p <= 8 * buf.len(),
    ensures
        r.1 <= 56, r.1 + p <= 8 * buf.len(), win_k(lbits(buf@), p as int, r.0, r.1 as nat),
        r.1 == 56 || r.1 + p == 8 * buf.len(),
{
    let w = peek_lsb(buf, p, 56);
    proof { lemma_peek_win_k(buf@, p as int, 56, w); }
    let left = 8 * buf.len() - p;
    (w, if left < 56 { left as u64 } else { 56 })
}

/// The window refilled.
#[inline(always)]
pub fn refill(buf: &[u8], x: &mut Br)
    requires br_wf(buf@, *old(x)),
    ensures
        br_wf(buf@, *final(x)), final(x).p == old(x).p,
        final(x).k == 56 || final(x).k + final(x).p == 8 * buf.len(),
{
    let (w, k) = load_win(buf, x.p);
    x.w = w;
    x.k = k;
}

/// `n` bits (n <= 24): `getbits`.
#[inline(always)]
pub fn take(buf: &[u8], x: &mut Br, n: u64) -> (r: Option<u64>)
    requires br_wf(buf@, *old(x)), n <= 24,
    ensures
        br_wf(buf@, *final(x)), old(x).p <= final(x).p,
        match r {
            Some(v) => getbits(lbits(buf@), old(x).p as int, n as nat) == Some(v as nat)
                && final(x).p == old(x).p + n && (v as nat) < p2(n as nat),
            None => getbits(lbits(buf@), old(x).p as int, n as nat) is None,
        },
{
    if n > x.k {
        refill(buf, x);
        if n > x.k {
            return None;
        }
    }
    assert(1u64 << n >= 1) by (bit_vector) requires n <= 24;
    let mask: u64 = (1u64 << n) - 1;
    let v = x.w & mask;
    proof {
        lemma_win_getbits(lbits(buf@), x.p as int, x.w, x.k as nat, n as nat);
        vbits::prim_read::lemma_p2_eq_pow2(n as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(n as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, n);
        assert(mask == vstd::bits::low_bits_mask(n as nat) as u64);
        vstd::bits::lemma_u64_low_bits_mask_is_mod(x.w, n as nat);
        lemma_win_shift(lbits(buf@), x.p as int, x.w, x.k as nat, n);
    }
    x.w = x.w >> n;
    x.k = x.k - n;
    x.p = x.p + n as usize;
    Some(v)
}

/// A table entry that is no code's, with at least 15 bits in the window:
/// the code of the table's bits, and nothing shorter matches.
proof fn lemma_miss(d: &Dec, b: Seq<bool>, buf: Seq<u8>, x: Br, wi: u64, e: u16)
    requires
        dec_wf(d), b == lbits(buf), br_wf(buf, x), x.k >= 15,
        wi == x.w & 1023, e == d.c.tbl@[wi as int], e / 1024 > x.k,
    ensures
        1 <= d.c.tb <= 10, win_ok(b, x.p as int, x.w), x.p + d.c.tb <= b.len(),
        (e % 1024) as nat == codebits(b, x.p as int, d.c.tb as nat),
        find_sym(d.lens@, b, x.p as int, 1) == find_sym(d.lens@, b, x.p as int, (d.c.tb + 1) as nat),
        d.nfirst as nat == next_code(d.lens@, (d.c.tb + 1) as nat),
        d.nfirst as nat <= 2048 * (p2(d.c.tb as nat) - 1),
        d.nindex as nat == d.c.h.offs[d.c.tb as int + 1], d.nindex <= 1024, huff_wf(&d.c.h, d.lens@),
{
    reveal(dec_tbl);
    reveal(btbl);
    let (p, w, k) = (x.p as int, x.w, x.k as nat);
    let lens = d.lens@;
    let t = d.c.tb as nat;
    let mask: u64 = 1023;
    let tb: u64 = 10;
    let wb = vdeflate::huff::wbits(wi, 10);
    assert(wi < 1024) by (bit_vector) requires wi == w & 1023;
    assert(p2(10) == 1024) by { reveal_with_fuel(p2, 11); }
    assert(bentry(d.c.tbl@[wi as int], lens, wb, d.single, d.sym, t));
    lemma_win_15(b, p, w, k);
    assert(b.len() == 8 * buf.len());
    assert(!d.single && e / 1024 == 63 && t <= 10);
    let v = wb.subrange(0, t as int);
    assert forall|j: int| 0 <= j < v.len() implies #[trigger] b[p + j] == v[j] by {
        let jj = j as u64;
        assert(((wi >> jj) & 1u64) == ((w >> jj) & 1u64)) by (bit_vector)
            requires wi == w & mask, mask == 1023, jj < 10;
        assert(p + j < b.len() && j < k);
        assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
        assert(wb[j] == ((wi >> jj) & 1u64 == 1u64));
    }
    lemma_find_sym_past(lens, v, b, p, 1);
    assert(b.subrange(p, p + t) =~= v) by {
        assert forall|j: int| 0 <= j < t implies #[trigger] b.subrange(p, p + t)[j] == v[j] by {
            assert(b[p + j] == v[j]);
        }
    }
}

/// One symbol: `dsym`. From the window, refilled if it has fewer than 15
/// bits; near the end of the stream, from the buffer.
#[inline(always)]
pub fn sym(d: &Dec, buf: &[u8], x: &mut Br) -> (r: Option<u16>)
    requires dec_wf(d), br_wf(buf@, *old(x)),
    ensures
        br_wf(buf@, *final(x)), old(x).p <= final(x).p,
        match r {
            Some(s) => dsym(d.lens@, lbits(buf@), old(x).p as int) == Some((s as nat, final(x).p as int))
                && (s as int) < d.lens@.len() && old(x).p <= final(x).p,
            None => dsym(d.lens@, lbits(buf@), old(x).p as int) is None,
        },
{
    proof { reveal(dec_tbl); }
    let ghost b = lbits(buf@);
    let ghost lens = d.lens@;
    let c = &d.c;
    proof { reveal(btbl); }
    let ghost tb: u64 = 10;
    let mask: u64 = 1023;
    let xw = x.w;
    let wi = xw & 1023;
    assert(wi < 1024 && wi == xw & mask && mask == (1u64 << tb) - 1) by (bit_vector)
        requires wi == xw & 1023, mask == 1023, tb == 10;
    let e = c.tbl[wi as usize];
    let l = (e / 1024) as u64;
    // one comparison: a code of at most the window's bits (a one-symbol
    // code's 0 included); no code is 63, more than the window
    if l <= x.k {
        proof {
            let p = x.p as int;
            let w = x.w;
            let wb = vdeflate::huff::wbits(wi, tb as nat);
            vbits::prim_read::lemma_p2_eq_pow2(tb as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(tb as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, tb);
            assert(wi < (1u64 << tb)) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
            assert(bentry(c.tbl@[wi as int], lens, wb, d.single, d.sym, c.tb as nat));
            if d.single {
                lemma_first_nz_found(lens, 0);
                assert(e == d.sym && l == 0);
                lemma_win_shift(b, p, w, x.k as nat, l);
                assert(w >> 0u64 == w) by (bit_vector);
            } else {
                let s = (e % 1024) as nat;
                assert(1 <= l <= 15);
                vdeflate::spec::lemma_find_sym_adv(lens, wb, 0, 1);
                assert forall|j: int| 0 <= j < l implies #[trigger] b[p + j] == wb[0 + j] by {
                    let jj = j as u64;
                    assert(((wi >> jj) & 1u64) == ((w >> jj) & 1u64)) by (bit_vector)
                        requires wi == w & mask, mask == (1u64 << tb) - 1, jj < tb, tb <= 10;
                    assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
                }
                lemma_find_sym_agree(lens, b, p, wb, 0, 1, s, l as nat);
                lemma_find_sym_sym(lens, b, p, 1);
                lemma_win_shift(b, p, w, x.k as nat, l);
            }
        }
        x.w = x.w >> l;
        x.k = x.k - l;
        x.p = x.p + l as usize;
        return Some(e % 1024);
    }
    proof {
        if d.single {
            // a one-symbol code's entries are length 0
            let wb = vdeflate::huff::wbits(wi, tb as nat);
            vbits::prim_read::lemma_p2_eq_pow2(tb as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(tb as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, tb);
            let w = x.w;
            assert(wi < (1u64 << tb)) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
            assert(bentry(c.tbl@[wi as int], lens, wb, d.single, d.sym, c.tb as nat));
            assert(false);
        }
    }
    // a miss: a longer code than the window's bits, or no code of at most
    // the table's width; with fewer than 15 bits, refill and look again
    if x.k < 15 {
        refill(buf, x);
        if x.k < 15 {
            // near the end of the stream: from the buffer
            return match sym_end(d, buf, x.p) {
                None => None,
                Some((s, q)) => {
                    *x = br_at(buf, q);
                    Some(s)
                }
            };
        }
        return sym_full(d, buf, x);
    }
    proof { lemma_win_15(b, x.p as int, x.w, x.k as nat); }
    proof { lemma_miss(d, b, buf@, *x, wi, e); }
    // resume past the table's bits, from the code the entry holds
    match decode_from(&c.h, Ghost(lens), Ghost(b), x.p, 8 * buf.len() - x.p, x.w, c.tb + 1, (e % 1024) as u64,
                      d.nfirst, d.nindex) {
        None => None,
        Some((s, l)) => {
            proof {
                lemma_find_sym_sym(lens, b, x.p as int, 1);
                vdeflate::spec::lemma_find_sym_adv(lens, b, x.p as int, 1);
                lemma_win_shift(b, x.p as int, x.w, x.k as nat, l);
            }
            x.w = x.w >> l;
            x.k = x.k - l;
            x.p = x.p + l as usize;
            Some(s)
        }
    }
}

/// One symbol with at least 15 bits in the window: the table, then one bit
/// at a time.
#[inline(always)]
fn sym_full(d: &Dec, buf: &[u8], x: &mut Br) -> (r: Option<u16>)
    requires dec_wf(d), br_wf(buf@, *old(x)), old(x).k >= 15,
    ensures
        br_wf(buf@, *final(x)), old(x).p <= final(x).p,
        match r {
            Some(s) => dsym(d.lens@, lbits(buf@), old(x).p as int) == Some((s as nat, final(x).p as int))
                && (s as int) < d.lens@.len() && old(x).p <= final(x).p,
            None => dsym(d.lens@, lbits(buf@), old(x).p as int) is None,
        },
{
    proof { reveal(dec_tbl); }
    let ghost b = lbits(buf@);
    let ghost lens = d.lens@;
    let c = &d.c;
    proof { lemma_win_15(b, x.p as int, x.w, x.k as nat); reveal(btbl); }
    let ghost tb: u64 = 10;
    let mask: u64 = 1023;
    let xw = x.w;
    let wi = xw & 1023;
    assert(wi < 1024 && wi == xw & mask && mask == (1u64 << tb) - 1) by (bit_vector)
        requires wi == xw & 1023, mask == 1023, tb == 10;
    let e = c.tbl[wi as usize];
    let l = (e / 1024) as u64;
    if l <= x.k {
        proof {
            let p = x.p as int;
            let w = x.w;
            let wb = vdeflate::huff::wbits(wi, tb as nat);
            vbits::prim_read::lemma_p2_eq_pow2(tb as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(tb as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, tb);
            assert(wi < (1u64 << tb)) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
            assert(bentry(c.tbl@[wi as int], lens, wb, d.single, d.sym, c.tb as nat));
            if d.single {
                lemma_first_nz_found(lens, 0);
                assert(e == d.sym && l == 0);
                lemma_win_shift(b, p, w, x.k as nat, l);
                assert(w >> 0u64 == w) by (bit_vector);
            } else {
                let s = (e % 1024) as nat;
                assert(1 <= l <= 15);
                vdeflate::spec::lemma_find_sym_adv(lens, wb, 0, 1);
                assert forall|j: int| 0 <= j < l implies #[trigger] b[p + j] == wb[0 + j] by {
                    let jj = j as u64;
                    assert(((wi >> jj) & 1u64) == ((w >> jj) & 1u64)) by (bit_vector)
                        requires wi == w & mask, mask == (1u64 << tb) - 1, jj < tb, tb <= 10;
                    assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
                }
                lemma_find_sym_agree(lens, b, p, wb, 0, 1, s, l as nat);
                lemma_find_sym_sym(lens, b, p, 1);
                lemma_win_shift(b, p, w, x.k as nat, l);
            }
        }
        x.w = x.w >> l;
        x.k = x.k - l;
        x.p = x.p + l as usize;
        return Some(e % 1024);
    }
    proof {
        if d.single {
            let wb = vdeflate::huff::wbits(wi, tb as nat);
            vbits::prim_read::lemma_p2_eq_pow2(tb as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(tb as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, tb);
            let w = x.w;
            assert(wi < (1u64 << tb)) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
            assert(bentry(c.tbl@[wi as int], lens, wb, d.single, d.sym, c.tb as nat));
            assert(false);
        }
    }
    proof { lemma_miss(d, b, buf@, *x, wi, e); }
    // resume past the table's bits, from the code the entry holds
    match decode_from(&c.h, Ghost(lens), Ghost(b), x.p, 8 * buf.len() - x.p, x.w, c.tb + 1, (e % 1024) as u64,
                      d.nfirst, d.nindex) {
        None => None,
        Some((s, l)) => {
            proof {
                lemma_find_sym_sym(lens, b, x.p as int, 1);
                vdeflate::spec::lemma_find_sym_adv(lens, b, x.p as int, 1);
                lemma_win_shift(b, x.p as int, x.w, x.k as nat, l);
            }
            x.w = x.w >> l;
            x.k = x.k - l;
            x.p = x.p + l as usize;
            Some(s)
        }
    }
}

/// A symbol near the end of the stream (fewer than 15 bits left), from the
/// buffer, one bit at a time: the symbol and the position after it.
#[inline(never)]
fn sym_end(d: &Dec, buf: &[u8], p: usize) -> (r: Option<(u16, usize)>)
    requires dec_wf(d), buf_ok(buf@), p <= 8 * buf.len(),
    ensures
        match r {
            Some((s, q)) => dsym(d.lens@, lbits(buf@), p as int) == Some((s as nat, q as int))
                && (s as int) < d.lens@.len() && p <= q <= 8 * buf.len(),
            None => dsym(d.lens@, lbits(buf@), p as int) is None,
        },
{
    proof { reveal(dec_tbl); }
    if d.single {
        proof { lemma_first_nz_found(d.lens@, 0); }
        return Some((d.sym, p));
    }
    let r = decode_slow(&d.c.h, Ghost(d.lens@), buf, p);
    proof {
        vdeflate::spec::lemma_find_sym_adv(d.lens@, lbits(buf@), p as int, 1);
        lemma_find_sym_sym(d.lens@, lbits(buf@), p as int, 1);
    }
    r
}

} // verus!
