//! Bit fields and prefix codes (RFC 7932 3), each proved to compute its
//! spec function on `lbits(input)`.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::{p2, lemma_p2_pos};
use vbits::lsb::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::{getbits, decode_sym, lens_ok, bl_count, count_len, find_sym, codebits, next_code};
use vdeflate::huff::*;
use crate::spec::*;

verus! {

// ------------------------------------------------------------ bit fields

/// The input is a buffer whose bit count fits a `usize` comfortably.
pub open spec fn buf_ok(buf: Seq<u8>) -> bool { buf.len() < max_input() }

/// `n` bits at `pos` (n <= 32), LSB first.
#[inline(always)]
pub fn getbits_x(buf: &[u8], pos: usize, n: u64) -> (r: Option<u64>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), n <= 32,
    ensures
        match r {
            Some(v) => getbits(lbits(buf@), pos as int, n as nat) == Some(v as nat)
                && pos + n <= 8 * buf.len() && (v as nat) < p2(n as nat),
            None => getbits(lbits(buf@), pos as int, n as nat) is None,
        },
{
    if n as usize > 8 * buf.len() - pos {
        return None;
    }
    if n == 0 {
        proof {
            assert(lbits(buf@).subrange(pos as int, pos as int) =~= Seq::<bool>::empty());
            assert(p2(0) == 1);
        }
        return Some(0);
    }
    let v = peek_lsb(buf, pos, n);
    proof {
        lemma_lview_inside(buf@, pos as int, pos as int + n);
        lemma_lval_bound(lbits(buf@).subrange(pos as int, pos as int + n));
    }
    Some(v)
}

pub proof fn lemma_getbits_bound(b: Seq<bool>, p: int, n: nat)
    requires getbits(b, p, n) is Some,
    ensures getbits(b, p, n).unwrap() < p2(n),
{
    lemma_lval_bound(b.subrange(p, p + n));
}

pub fn align8_x(p: usize) -> (r: usize)
    requires p < usize::MAX - 8,
    ensures r as int == align8(p as int), p <= r <= p + 7,
{
    if p % 8 == 0 { p } else { p + (8 - p % 8) }
}

/// The fill bits from `p` to the next byte boundary are there and zero.
pub fn zero_fill_x(buf: &[u8], p: usize) -> (r: bool)
    requires buf_ok(buf@), p <= 8 * buf.len(),
    ensures r == zero_fill(lbits(buf@), p as int), r ==> align8(p as int) <= 8 * buf.len(),
{
    let a = align8_x(p);
    match getbits_x(buf, p, (a - p) as u64) {
        None => false,
        Some(v) => v == 0,
    }
}

/// `cnt` bytes from the byte boundary `q`, written after `out@.take(n)`.
pub fn bytes_at_x(buf: &[u8], q: usize, cnt: usize, out: &mut Vec<u8>, n: usize)
    requires buf_ok(buf@), q % 8 == 0, q + 8 * cnt <= 8 * buf.len(), n + cnt <= old(out)@.len(),
        n + cnt < 0x1000_0000_0000_0000,
    ensures
        final(out)@.len() == old(out)@.len(),
        final(out)@.take(n + cnt) == old(out)@.take(n as int) + bytes_at(lbits(buf@), q as int, cnt as nat),
{
    let ghost o0 = old(out)@.take(n as int);
    let ghost b = lbits(buf@);
    let i0 = q / 8;
    proof {
        assert(i0 + cnt <= buf.len()) by (nonlinear_arith) requires i0 == q / 8, q % 8 == 0, q + 8 * cnt <= 8 * buf.len();
        assert forall|j: int| 0 <= j < cnt implies #[trigger] bytes_at(b, q as int, cnt as nat)[j] == buf@[i0 + j] by {
            let x = buf@[i0 + j];
            let t = b.subrange(q + 8 * j, q + 8 * j + 8);
            assert(t =~= lbits(seq![x])) by {
                assert forall|k: int| 0 <= k < 8 implies #[trigger] t[k] == lbits(seq![x])[k] by {
                    assert((q + 8 * j + k) / 8 == i0 + j) by (nonlinear_arith)
                        requires i0 == q / 8, q % 8 == 0, 0 <= k < 8;
                    assert((q + 8 * j + k) % 8 == k) by (nonlinear_arith)
                        requires q % 8 == 0, 0 <= k < 8;
                }
            }
            lemma_lval_byte(x);
        }
        assert(bytes_at(b, q as int, cnt as nat) =~= buf@.subrange(i0 as int, i0 + cnt));
    }
    let ghost o = out@;
    let _pl = out.len();
    out.as_mut_slice()[n..n + cnt].copy_from_slice(vstd::slice::slice_subrange(buf, i0, i0 + cnt));
    proof {
        assert(out@.take(n + cnt) =~= o0 + buf@.subrange(i0 as int, i0 + cnt)) by {
            assert forall|i: int| 0 <= i < n + cnt implies #[trigger] out@.take(n + cnt)[i] == (o0 + buf@.subrange(i0 as int, i0 + cnt))[i] by {
                if i < n {
                    assert(out@.subrange(0, n as int)[i] == o.subrange(0, n as int)[i]);
                } else {
                    assert(out@.subrange(n as int, n + cnt)[i - n] == out@[i]);
                }
            }
        }
    }
}

// --------------------------------------------------------- prefix codes

/// A prefix code ready to decode with: its lengths (ghost), its table, and
/// for a code of one symbol, that symbol.
/// A code's canonical table and its fast table (vdeflate's `Code` has, in
/// addition, what vdeflate's long-code search resumes from, which this
/// table keeps in its entries instead).
pub struct BCode {
    pub h: Huff,
    pub tbl: [u16; 1024],
    pub tb: u64,
    pub mask: u64,
}

pub struct Dec {
    pub lens: Ghost<Seq<u8>>,
    pub single: bool,
    pub sym: u16,
    pub c: BCode,
    /// The first code of `c.tb + 1` bits and its symbols' place in the list:
    /// where a miss in the table resumes.
    pub nfirst: u64,
    pub nindex: u64,
}

pub open spec fn dec_wf(d: &Dec) -> bool {
    &&& d.lens@.len() <= 1024
    &&& lens_ok(d.lens@)
    &&& dec_tbl(d)
}

/// The tables decode `lens` (opaque: other modules pass it along whole).
#[verifier::opaque]
pub open spec fn dec_tbl(d: &Dec) -> bool {
    let lens = d.lens@;
    &&& huff_wf(&d.c.h, lens)
    &&& btbl(d.c.tbl@, lens, 10, d.single, d.sym, d.c.tb as nat)
    &&& 1 <= d.c.tb <= 10
    &&& d.nfirst as nat == next_code(lens, (d.c.tb + 1) as nat) && d.nfirst as nat <= 2048 * (p2(d.c.tb as nat) - 1)
    &&& d.nindex as nat == d.c.h.offs[d.c.tb as int + 1] && d.nindex <= 1024
    &&& d.single == (nnz(lens, lens.len() as int) == 1)
    &&& d.single ==> d.sym as int == first_nz(lens, 0) && d.sym < 1024
}

/// A table entry, in the decoder's format: a code's length times 1024 plus
/// its symbol; the one symbol, with length 0, for a code of one symbol; and
/// length 63 (more bits than a window holds) where the table has no code,
/// with the code of the table's `t` bits, no code's prefix, from which a
/// search resumes. So one comparison of the length with the window's bits
/// decides.
pub open spec fn bentry(e: u16, lens: Seq<u8>, wb: Seq<bool>, single: bool, sym: u16, t: nat) -> bool {
    let l = (e / 1024) as nat;
    let s = (e % 1024) as nat;
    if single { e == sym }
    else if l == 63 {
        t <= wb.len() && t <= 10 && s == codebits(wb, 0, t) && find_sym(lens, wb.subrange(0, t as int), 0, 1) is None
    }
    else { 1 <= l <= 15 && find_sym(lens, wb, 0, 1) == Some((s, l as int)) }
}

/// Every `tb`-bit window's entry (opaque: revealed where built and read).
#[verifier::opaque]
pub open spec fn btbl(tbl: Seq<u16>, lens: Seq<u8>, tb: nat, single: bool, sym: u16, t: nat) -> bool {
    &&& tbl.len() == 1024
    &&& forall|w: int| 0 <= w < p2(tb) ==> bentry(#[trigger] tbl[w], lens, vdeflate::huff::wbits(w as u64, tb), single, sym, t)
}

proof fn lemma_nnz_le(lens: Seq<u8>, upto: int)
    requires 0 <= upto <= lens.len(),
    ensures nnz(lens, upto) <= upto,
    decreases upto,
{
    if upto > 0 { lemma_nnz_le(lens, upto - 1); }
}

/// No nonzero length before `i`, so the first from 0 is the first from `i`.
proof fn lemma_first_nz_skip(lens: Seq<u8>, i: int)
    requires 0 <= i <= lens.len(), nnz(lens, i) == 0,
    ensures first_nz(lens, 0) == first_nz(lens, i),
    decreases i,
{
    if i > 0 {
        lemma_nnz_le(lens, i - 1);
        assert(lens[i - 1] == 0);
        assert(nnz(lens, i - 1) == 0);
        lemma_first_nz_skip(lens, i - 1);
        assert(first_nz(lens, i - 1) == first_nz(lens, i));
    }
}

/// The first nonzero length is a symbol with a nonzero length.
pub proof fn lemma_first_nz_found(lens: Seq<u8>, i: int)
    requires 0 <= i <= lens.len(), nnz(lens, lens.len() as int) >= 1, nnz(lens, i) == 0,
    ensures 0 <= first_nz(lens, i) < lens.len(), lens[first_nz(lens, i)] != 0,
    decreases lens.len() - i,
{
    if i == lens.len() {
        assert(false);
    } else if lens[i] == 0 {
        assert(nnz(lens, i + 1) == 0);
        lemma_first_nz_found(lens, i + 1);
    }
}

proof fn lemma_tot_step_b(lens: Seq<u8>, l: nat, n: int)
    requires 0 <= n < lens.len(),
    ensures tot(lens, l, n + 1) == tot(lens, l, n) + (if 1 <= lens[n] <= l { 1nat } else { 0nat }),
    decreases l,
{
    if l > 0 { lemma_tot_step_b(lens, (l - 1) as nat, n); }
}

proof fn lemma_tot_zero_b(lens: Seq<u8>, l: nat)
    ensures tot(lens, l, 0) == 0,
    decreases l,
{
    if l > 0 { lemma_tot_zero_b(lens, (l - 1) as nat); }
}

/// The nonzero lengths are the codes of lengths 1 to 15.
proof fn lemma_nnz_tot(lens: Seq<u8>, n: int)
    requires 0 <= n <= lens.len(), lens_ok(lens),
    ensures nnz(lens, n) == tot(lens, 15, n),
    decreases n,
{
    if n == 0 {
        lemma_tot_zero_b(lens, 15);
    } else {
        lemma_nnz_tot(lens, n - 1);
        lemma_tot_step_b(lens, 15, n - 1);
        assert(lens[n - 1] <= 15);
    }
}

/// Where the codes of length `l` start in the symbol list: after those of
/// lengths 1 to `l - 1`.
proof fn lemma_offs_tot(h: &Huff, lens: Seq<u8>, l: int)
    requires huff_wf(h, lens), 1 <= l <= 15,
    ensures h.offs[l] as nat == tot(lens, (l - 1) as nat, lens.len() as int),
    decreases l,
{
    if l > 1 {
        lemma_offs_tot(h, lens, l - 1);
        assert(h.offs[(l - 1) + 1] as nat == h.offs[l - 1] + h.count[l - 1]);
        assert(h.count[l - 1] as nat == bl_count(lens, (l - 1) as nat));
    }
}

/// The symbol list has a place for each symbol with a code.
proof fn lemma_syms_len(h: &Huff, lens: Seq<u8>)
    requires huff_wf(h, lens),
    ensures h.syms@.len() == nnz(lens, lens.len() as int),
{
    lemma_offs_tot(h, lens, 15);
    assert(h.count[15] as nat == bl_count(lens, 15));
    lemma_nnz_tot(lens, lens.len() as int);
}

/// The first symbol with a code, of a code with at least one.
fn first_code(lens: &Vec<u8>) -> (r: u16)
    requires lens@.len() <= 1024, nnz(lens@, lens@.len() as int) >= 1,
    ensures r as int == first_nz(lens@, 0),
{
    let n = lens.len();
    let mut i: usize = 0;
    while i < n
        invariant n == lens@.len(), n <= 1024, i <= n, nnz(lens@, i as int) == 0, nnz(lens@, n as int) >= 1,
        decreases n - i,
    {
        if lens[i] != 0 {
            proof { lemma_first_nz_skip(lens@, i as int); }
            return i as u16;
        }
        proof { assert(nnz(lens@, i + 1) == 0); }
        i = i + 1;
    }
    proof { assert(false); }
    0
}

/// Counts agree over lengths that agree.
proof fn lemma_count_agree(a: Seq<u8>, b: Seq<u8>, l: nat, u: int)
    requires 0 <= u <= a.len(), u <= b.len(), forall|j: int| 0 <= j < u ==> #[trigger] a[j] == b[j],
    ensures count_len(a, l, u) == count_len(b, l, u),
    decreases u,
{
    if u > 0 { lemma_count_agree(a, b, l, u - 1); assert(a[u - 1] == b[u - 1]); }
}

/// Zero lengths add no codes.
proof fn lemma_count_zeros(a: Seq<u8>, l: nat, u: int, v: int)
    requires 1 <= l, 0 <= u <= v <= a.len(), forall|j: int| u <= j < v ==> #[trigger] a[j] == 0,
    ensures count_len(a, l, v) == count_len(a, l, u),
    decreases v - u,
{
    if v > u { lemma_count_zeros(a, l, u, v - 1); assert(a[v - 1] == 0); }
}

/// A symbol list built from the lengths up to `last` is the lengths' own,
/// when all after `last` are zero.
proof fn lemma_huff_trim(h: &Huff, lens: Seq<u8>, last: int)
    requires
        0 <= last <= lens.len(), lens.len() <= 1024, lens_ok(lens),
        forall|j: int| last <= j < lens.len() ==> #[trigger] lens[j] == 0,
        huff_wf(h, lens.take(last)),
    ensures huff_wf(h, lens),
{
    let t = lens.take(last);
    assert forall|l: int| 1 <= l <= 15 implies #[trigger] h.count[l] as nat == bl_count(lens, l as nat) by {
        assert(h.count[l] as nat == bl_count(t, l as nat));
        lemma_count_agree(t, lens, l as nat, last);
        lemma_count_zeros(lens, l as nat, last, lens.len() as int);
    }
    assert forall|n: int| 0 <= n < lens.len() && 1 <= lens[n] implies
        (h.offs[lens[n] as int] + count_len(lens, lens[n] as nat, n) < h.syms@.len()
         && h.syms@[h.offs[lens[n] as int] + count_len(lens, lens[n] as nat, n)] == n) by {
        assert(n < last);
        assert(t[n] == lens[n]);
        lemma_count_agree(t, lens, lens[n] as nat, n);
    }
}

/// Make a code from its lengths, all zero from `last` on: the symbol list
/// from the lengths up to `last` only.
pub fn mk_dec_to(lens: &Vec<u8>, last: usize) -> (d: Dec)
    requires lens@.len() <= 1024, lens_ok(lens@), last <= lens@.len(),
        forall|j: int| last <= j < lens@.len() ==> #[trigger] lens@[j] == 0,
    ensures dec_wf(&d), d.lens@ == lens@,
{
    let sl = vstd::slice::slice_subrange(lens.as_slice(), 0, last);
    proof { assert(sl@ =~= lens@.take(last as int)); }
    let h = build(sl);
    proof { lemma_huff_trim(&h, lens@, last as int); }
    mk_dec_h(lens, h)
}

/// Make a code from its lengths.
pub fn mk_dec(lens: &Vec<u8>) -> (d: Dec)
    requires lens@.len() <= 1024, lens_ok(lens@),
    ensures dec_wf(&d), d.lens@ == lens@,
{
    let h = build(lens.as_slice());
    mk_dec_h(lens, h)
}

/// An entry for a window is right for a wider window that starts with it.
proof fn lemma_bentry_widen(e: u16, lens: Seq<u8>, w1: u64, n1: nat, w2: u64, n2: nat, single: bool, sym: u16, t: nat)
    requires
        bentry(e, lens, vdeflate::huff::wbits(w1, n1), single, sym, t), n1 <= n2 <= 64,
        forall|j: u64| j < n1 ==> #[trigger] ((w1 >> j) & 1u64) == ((w2 >> j) & 1u64),
    ensures bentry(e, lens, vdeflate::huff::wbits(w2, n2), single, sym, t),
{
    if !single {
        let l = (e / 1024) as nat;
        if l == 63 {
            let b1 = vdeflate::huff::wbits(w1, n1);
            let b2 = vdeflate::huff::wbits(w2, n2);
            assert(b2.subrange(0, t as int) =~= b1.subrange(0, t as int)) by {
                assert forall|j: int| 0 <= j < t implies #[trigger] b2.subrange(0, t as int)[j] == b1.subrange(0, t as int)[j] by {
                    assert(((w1 >> (j as u64)) & 1u64) == ((w2 >> (j as u64)) & 1u64));
                }
            }
        }
        if 1 <= l <= 15 {
            let s = (e % 1024) as nat;
            let b1 = vdeflate::huff::wbits(w1, n1);
            let b2 = vdeflate::huff::wbits(w2, n2);
            vdeflate::spec::lemma_find_sym_adv(lens, b1, 0, 1);
            assert forall|j: int| 0 <= j < l implies #[trigger] b2[0 + j] == b1[0 + j] by {
                assert(((w1 >> (j as u64)) & 1u64) == ((w2 >> (j as u64)) & 1u64));
            }
            lemma_find_sym_agree(lens, b2, 0, b1, 0, 1, s, l);
        }
    }
}

/// A code from its lengths and their symbol list: the list's counts give
/// the table's width and whether the code has one symbol (no pass over the
/// lengths).
fn mk_dec_h(lens: &Vec<u8>, h: Huff) -> (d: Dec)
    requires lens@.len() <= 1024, lens_ok(lens@), huff_wf(&h, lens@),
    ensures dec_wf(&d), d.lens@ == lens@,
{
    proof { lemma_syms_len(&h, lens@); }
    // a table as wide as the longest code, up to 10 bits
    let mut m: usize = 15;
    while m > 1 && h.count[m] == 0
        invariant 1 <= m <= 15,
        decreases m,
    {
        m = m - 1;
    }
    let tb: u64 = if m > 10 { 10 } else { m as u64 };
    let single = h.syms.len() == 1;
    let sym = if single { first_code(lens) } else { 0 };
    let (mut tbl, code, nfirst) = build_table_c(&h, Ghost(lens@), tb);
    let nindex = h.offs[tb as usize + 1] as u64;
    proof {
        lemma_offs_end(&h, lens@, tb as int + 1);
        vbits::prim_read::lemma_p2_eq_pow2(tb as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(tb as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, tb);
        vbits::prim_read::lemma_p2_mono(tb as nat, 10);
        assert(p2(10) == 1024) by { reveal_with_fuel(p2, 11); }
        if single { lemma_first_nz_found(lens@, 0); }
    }
    // the decoder's format: no code is length 63; one symbol is length 0
    let nw: usize = (1u64 << tb) as usize;
    let mut w: usize = 0;
    while w < nw
        invariant
            nw as nat == p2(tb as nat), nw <= 1024, w <= nw, tbl@.len() == 1024, single == (h.syms@.len() == 1),
            single ==> sym < 1024,
            1 <= tb <= 10, code@.len() == 1024,
            forall|v: int| 0 <= v < w ==> bentry(#[trigger] tbl@[v], lens@, vdeflate::huff::wbits(v as u64, tb as nat), single, sym, tb as nat),
            forall|v: int| w <= v < nw ==> lvl_ok(#[trigger] tbl@[v], code@[v], lens@, v as u64, tb as nat),
        decreases nw - w,
    {
        if single {
            tbl[w] = sym;
        } else if tbl[w] == 0 {
            proof {
                let wb = vdeflate::huff::wbits(w as u64, tb as nat);
                assert(wb.subrange(0, tb as int) =~= wb);
                vbits::bitspec::lemma_bits_val_bound(wb.subrange(0, tb as int));
                vbits::prim_read::lemma_p2_mono(tb as nat, 10);
            }
            tbl[w] = 0xFC00 + code[w];
        }
        w = w + 1;
    }
    // the table repeated to 10 bits, so that a symbol's lookup masks with a
    // constant
    let mut m: u64 = tb;
    while m < 10
        invariant
            1 <= m <= 10, tbl@.len() == 1024, single ==> sym < 1024,
            forall|v: int| 0 <= v < p2(m as nat) ==>
                bentry(#[trigger] tbl@[v], lens@, vdeflate::huff::wbits(v as u64, m as nat), single, sym, tb as nat),
        decreases 10 - m,
    {
        proof {
            vbits::prim_read::lemma_p2_eq_pow2(m as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(m as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, m);
            vbits::prim_read::lemma_p2_mono(m as nat, 9);
            assert(p2(9) == 512) by { reveal_with_fuel(p2, 10); }
        }
        let half: usize = (1u64 << m) as usize;
        let ghost t0 = tbl@;
        tbl.copy_within(0..half, half);
        proof {
            assert forall|u: int| 0 <= u < half implies #[trigger] tbl@[u] == t0[u] by {}
            assert forall|u: int| 0 <= u < half implies #[trigger] tbl@[half + u] == t0[u] by {}
        }
        proof {
            assert(p2(m as nat + 1) == 2 * p2(m as nat)) by { reveal_with_fuel(p2, 2); }
            assert forall|u: int| 0 <= u < p2(m as nat + 1) implies
                bentry(#[trigger] tbl@[u], lens@, vdeflate::huff::wbits(u as u64, (m + 1) as nat), single, sym, tb as nat) by {
                let uu = u as u64;
                let h64 = half as u64;
                if u < half {
                    assert(tbl@[u] == t0[u]);
                    assert forall|j: u64| j < m implies #[trigger] ((uu >> j) & 1u64) == ((uu >> j) & 1u64) by {}
                    lemma_bentry_widen(t0[u], lens@, uu, m as nat, uu, (m + 1) as nat, single, sym, tb as nat);
                } else {
                    let lo = (u - half) as u64;
                    assert(tbl@[half + (u - half)] == t0[u - half]);
                    assert(tbl@[u] == t0[u - half]);
                    assert forall|j: u64| j < m implies #[trigger] ((lo >> j) & 1u64) == ((uu >> j) & 1u64) by {
                        assert(((lo >> j) & 1u64) == ((uu >> j) & 1u64)) by (bit_vector)
                            requires uu == lo + h64, h64 == (1u64 << m), lo < h64, j < m, m < 10;
                    }
                    lemma_bentry_widen(t0[u - half], lens@, lo, m as nat, uu, (m + 1) as nat, single, sym, tb as nat);
                }
            }
        }
        m = m + 1;
    }
    assert(1u64 << tb >= 2) by (bit_vector) requires 1 <= tb <= 10;
    let c = BCode { h, tbl, tb, mask: (1u64 << tb) - 1 };
    let d = Dec { lens: Ghost(lens@), single, sym, c, nfirst, nindex };
    proof { reveal(dec_tbl); reveal(btbl); assert(p2(10) == 1024) by { reveal_with_fuel(p2, 11); } }
    d
}

/// One symbol: `dsym`, with the symbol's bound.
#[inline(always)]
pub fn dsym_x(d: &Dec, buf: &[u8], pos: usize) -> (r: Option<(u16, usize)>)
    requires dec_wf(d), buf_ok(buf@), pos <= 8 * buf.len(),
    ensures
        match r {
            Some((s, q)) => dsym(d.lens@, lbits(buf@), pos as int) == Some((s as nat, q as int))
                && (s as int) < d.lens@.len() && pos <= q <= 8 * buf.len(),
            None => dsym(d.lens@, lbits(buf@), pos as int) is None,
        },
{
    let mut x = crate::br::br_at(buf, pos);
    match crate::br::sym(d, buf, &mut x) {
        None => None,
        Some(s) => Some((s, x.p)),
    }
}

pub fn abits_x(asize: u64) -> (r: u64)
    ensures r as nat == abits(asize as nat), 1 <= r <= 11,
{
    if asize <= 2 { 1 } else if asize <= 4 { 2 } else if asize <= 8 { 3 } else if asize <= 16 { 4 }
    else if asize <= 32 { 5 } else if asize <= 64 { 6 } else if asize <= 128 { 7 }
    else if asize <= 256 { 8 } else if asize <= 512 { 9 } else if asize <= 1024 { 10 } else { 11 }
}

/// A sequence of `u16`s as the spec's `nat`s.
pub open spec fn nats(v: Seq<u16>) -> Seq<nat> { v.map_values(|x: u16| x as nat) }

fn read_syms_x(buf: &[u8], pos: usize, asize: u64, n: u64) -> (r: Option<(Vec<u16>, usize)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), 2 <= asize <= 1024, n <= 4,
    ensures
        match r {
            Some((v, q)) => read_syms(lbits(buf@), pos as int, asize as nat, n as nat, Seq::empty())
                    == Some((nats(v@), q as int))
                && q <= 8 * buf.len() && v@.len() == n
                && forall|i: int| 0 <= i < v@.len() ==> (#[trigger] v@[i] as nat) < asize,
            None => read_syms(lbits(buf@), pos as int, asize as nat, n as nat, Seq::empty()) is None,
        },
{
    let ghost b = lbits(buf@);
    let ghost target = read_syms(b, pos as int, asize as nat, n as nat, Seq::empty());
    let k = abits_x(asize);
    let mut v: Vec<u16> = Vec::new();
    let mut p = pos;
    proof { assert(nats(v@) =~= Seq::<nat>::empty()); }
    while (v.len() as u64) < n
        invariant
            buf_ok(buf@), p <= 8 * buf.len(), b == lbits(buf@), 2 <= asize <= 1024, n <= 4,
            k as nat == abits(asize as nat), v@.len() <= n,
            read_syms(b, p as int, asize as nat, n as nat, nats(v@)) == target,
            target == read_syms(lbits(buf@), pos as int, asize as nat, n as nat, Seq::empty()),
            forall|i: int| 0 <= i < v@.len() ==> (#[trigger] v@[i] as nat) < asize,
        decreases n - v@.len(),
    {
        proof { assert(nats(v@).len() == v@.len()); }
        let x = match getbits_x(buf, p, k) {
            None => {
                assert(getbits(b, p as int, abits(asize as nat)) is None);
                assert(read_syms(b, p as int, asize as nat, n as nat, nats(v@)) is None);
                return None;
            }
            Some(x) => x,
        };
        if x >= asize {
            return None;
        }
        proof { assert(nats(v@.push(x as u16)) =~= nats(v@).push(x as nat)); }
        v.push(x as u16);
        p = p + k as usize;
    }
    Some((v, p))
}

/// `n` zero bytes.
pub fn zeros(n: usize) -> (r: Vec<u8>)
    ensures r@ == Seq::new(n as nat, |_i: int| 0u8),
{
    let r = vec![0u8; n];
    proof { assert(r@ =~= Seq::new(n as nat, |_i: int| 0u8)); }
    r
}

/// Lengths of at most `m` are lengths DEFLATE's code search takes.
pub open spec fn lens_le(lens: Seq<u8>, m: u8) -> bool {
    forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] <= m
}

/// Whether a symbol list repeats a symbol.
fn has_dup(s: &Vec<u16>) -> (r: bool)
    requires s@.len() <= 4,
    ensures r == !distinct(nats(s@)),
{
    let ghost sn = nats(s@);
    let n = s.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == s@.len(), n <= 4, i <= n, sn == nats(s@),
            forall|a: int, c: int| 0 <= a < i && a < c < n ==> sn[a] != sn[c],
        decreases n - i,
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                n == s@.len(), n <= 4, i < n, i + 1 <= j <= n, sn == nats(s@),
                forall|a: int, c: int| 0 <= a < i && a < c < n ==> sn[a] != sn[c],
                forall|c: int| i < c < j ==> sn[i as int] != sn[c],
            decreases n - j,
        {
            if s[i] == s[j] {
                proof { assert(!distinct(sn)) by { assert(sn[i as int] == sn[j as int]); } }
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}

fn simple_code_x(buf: &[u8], pos: usize, asize: u64) -> (r: Option<(Vec<u8>, usize)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), 2 <= asize <= 1024,
    ensures
        match r {
            Some((v, q)) => simple_code(lbits(buf@), pos as int, asize as nat) == Some((v@, q as int))
                && q <= 8 * buf.len() && v@.len() == asize && lens_le(v@, 3),
            None => simple_code(lbits(buf@), pos as int, asize as nat) is None,
        },
{
    let ghost b = lbits(buf@);
    let m = match getbits_x(buf, pos, 2) {
        None => return None,
        Some(m) => m,
    };
    proof { reveal_with_fuel(p2, 3); }
    let (s, q) = match read_syms_x(buf, pos + 2, asize, m + 1) {
        None => return None,
        Some(x) => x,
    };
    let ghost sn = nats(s@);
    if has_dup(&s) {
        return None;
    }
    proof { assert(distinct(sn)); }
    let mut z = zeros(asize as usize);
    let ghost z0 = z@;
    proof {
        assert forall|k: int| 0 <= k < s@.len() implies (#[trigger] sn[k]) == s@[k] as nat by {}
    }
    if m == 0 {
        z.set(s[0] as usize, 1);
        proof { assert(lens_le(z@, 3)); }
        return Some((z, q));
    } else if m == 1 {
        z.set(s[0] as usize, 1);
        z.set(s[1] as usize, 1);
        proof { assert(lens_le(z@, 3)); }
        return Some((z, q));
    } else if m == 2 {
        z.set(s[0] as usize, 1);
        z.set(s[1] as usize, 2);
        z.set(s[2] as usize, 2);
        proof { assert(lens_le(z@, 3)); }
        return Some((z, q));
    }
    let ts = match getbits_x(buf, q, 1) {
        None => return None,
        Some(t) => t,
    };
    if ts == 0 {
        z.set(s[0] as usize, 2);
        z.set(s[1] as usize, 2);
        z.set(s[2] as usize, 2);
        z.set(s[3] as usize, 2);
    } else {
        z.set(s[0] as usize, 1);
        z.set(s[1] as usize, 2);
        z.set(s[2] as usize, 3);
        z.set(s[3] as usize, 3);
    }
    proof { assert(lens_le(z@, 3)); }
    Some((z, q + 1))
}

fn cl_len_x(buf: &[u8], p: usize) -> (r: Option<(u64, usize)>)
    requires buf_ok(buf@), p <= 8 * buf.len(),
    ensures
        match r {
            Some((v, q)) => cl_len(lbits(buf@), p as int) == Some((v as nat, q as int))
                && v <= 5 && p < q <= 8 * buf.len(),
            None => cl_len(lbits(buf@), p as int) is None,
        },
{
    let v = match getbits_x(buf, p, 2) { None => return None, Some(v) => v };
    proof { reveal_with_fuel(p2, 3); }
    if v == 0 {
        Some((0, p + 2))
    } else if v == 2 {
        Some((3, p + 2))
    } else if v == 1 {
        Some((4, p + 2))
    } else {
        let x = match getbits_x(buf, p + 2, 1) { None => return None, Some(x) => x };
        if x == 0 {
            Some((2, p + 3))
        } else {
            let y = match getbits_x(buf, p + 3, 1) { None => return None, Some(y) => y };
            if y == 0 { Some((1, p + 4)) } else { Some((5, p + 4)) }
        }
    }
}

pub const CL_ORDER: [u8; 18] = [1, 2, 3, 4, 0, 5, 17, 6, 16, 7, 8, 9, 10, 11, 12, 13, 14, 15];

proof fn lemma_cl_order()
    ensures forall|i: int| 0 <= i < 18 ==> #[trigger] CL_ORDER@[i] as nat == cl_order()[i] && CL_ORDER@[i] < 18,
{
    assert(forall|i: int| 0 <= i < 18 ==> #[trigger] CL_ORDER@[i] as nat == cl_order()[i] && CL_ORDER@[i] < 18)
        by (compute);
}

fn read_cl_x(buf: &[u8], pos: usize, h: u64) -> (r: Option<(Vec<u8>, usize)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), h <= 3,
    ensures
        match r {
            Some((v, q)) => read_cl(lbits(buf@), pos as int, h as nat, Seq::new(18, |_i: int| 0u8), 32, 0)
                    == Some((v@, q as int))
                && q <= 8 * buf.len() && v@.len() == 18 && lens_le(v@, 5),
            None => read_cl(lbits(buf@), pos as int, h as nat, Seq::new(18, |_i: int| 0u8), 32, 0) is None,
        },
{
    let ghost b = lbits(buf@);
    let ghost target = read_cl(b, pos as int, h as nat, Seq::new(18, |_i: int| 0u8), 32, 0);
    let mut acc = zeros(18);
    let mut p = pos;
    let mut i: u64 = h;
    let mut space: u64 = 32;
    let mut num: u64 = 0;
    proof { lemma_cl_order(); }
    while i < 18
        invariant
            buf_ok(buf@), p <= 8 * buf.len(), b == lbits(buf@), i <= 18, acc@.len() == 18,
            1 <= space <= 32, num <= i,
            lens_le(acc@, 5),
            read_cl(b, p as int, i as nat, acc@, space as int, num as nat) == target,
            target == read_cl(lbits(buf@), pos as int, h as nat, Seq::new(18, |_i: int| 0u8), 32, 0),
            forall|k: int| 0 <= k < 18 ==> #[trigger] CL_ORDER@[k] as nat == cl_order()[k] && CL_ORDER@[k] < 18,
        decreases 18 - i,
    {
        let (v, q) = match cl_len_x(buf, p) { None => return None, Some(x) => x };
        let k = CL_ORDER[i as usize] as usize;
        acc.set(k, v as u8);
        proof { assert(lens_le(acc@, 5)); }
        if v != 0 {
            let d: u64 = 32 >> v;
            proof {
                reveal_with_fuel(p2, 6);
                assert(d as nat == 32nat / p2(v as nat)) by {
                    assert(32u64 >> v == 32u64 / (1u64 << v)) by (bit_vector) requires 1 <= v <= 5;
                    assert(1u64 << v == p2(v as nat)) by {
                        vbits::prim_read::lemma_p2_eq_pow2(v as nat);
                        vstd::bits::lemma_u64_shl_is_mul(1u64, v);
                        vstd::bits::lemma_u64_pow2_no_overflow(v as nat);
                    }
                }
            }
            if d == space {
                return Some((acc, q));
            } else if d > space {
                return None;
            }
            space = space - d;
            num = num + 1;
        }
        p = q;
        i = i + 1;
    }
    if num == 1 { Some((acc, p)) } else { None }
}

/// The lengths of the symbols `sym..sym + delta` set to `nl`.
fn set_run(acc: &mut Vec<u8>, sym: usize, delta: usize, nl: u8)
    requires sym + delta <= old(acc)@.len(), old(acc)@.len() <= 1024,
    ensures final(acc)@ == Seq::new(old(acc)@.len(), |j: int| if sym <= j < sym + delta { nl } else { old(acc)@[j] }),
{
    let ghost a0 = old(acc)@;
    let mut j: usize = sym;
    while j < sym + delta
        invariant
            sym <= j <= sym + delta, sym + delta <= a0.len(), a0.len() <= 1024, acc@.len() == a0.len(),
            acc@ =~= Seq::new(a0.len(), |i: int| if sym <= i < j { nl } else { a0[i] }),
        decreases sym + delta - j,
    {
        acc.set(j, nl);
        j = j + 1;
    }
}

fn read_lens_x(cl: &Dec, buf: &[u8], pos: usize, asize: u64) -> (r: Option<(Vec<u8>, usize, usize)>)
    requires dec_wf(cl), cl.lens@.len() == 18, buf_ok(buf@), pos <= 8 * buf.len(), 2 <= asize <= 1024,
    ensures
        match r {
            Some((v, q, last)) => read_lens(cl.lens@, lbits(buf@), pos as int, asize as nat,
                                            Seq::new(asize as nat, |_i: int| 0u8), 0, 32768, 8, 0, 0)
                    == Some((v@, q as int))
                && q <= 8 * buf.len() && v@.len() == asize && lens_ok(v@)
                && last <= asize && (forall|j: int| last <= j < asize ==> #[trigger] v@[j] == 0),
            None => read_lens(cl.lens@, lbits(buf@), pos as int, asize as nat,
                              Seq::new(asize as nat, |_i: int| 0u8), 0, 32768, 8, 0, 0) is None,
        },
{
    let ghost b = lbits(buf@);
    let ghost cll = cl.lens@;
    let ghost target = read_lens(cll, b, pos as int, asize as nat, Seq::new(asize as nat, |_i: int| 0u8),
                                 0, 32768, 8, 0, 0);
    let mut acc = zeros(asize as usize);
    let mut x = crate::br::br_at(buf, pos);
    let mut sym: u64 = 0;
    let mut space: i64 = 32768;
    let mut prev: u64 = 8;
    let mut rep: u64 = 0;
    let mut rep_len: u64 = 0;
    // past the last symbol with a code so far
    let mut last: u64 = 0;
    proof { reveal_with_fuel(p2, 16); }
    loop
        invariant
            dec_wf(cl), cll == cl.lens@, cll.len() == 18, buf_ok(buf@), crate::br::br_wf(buf@, x), b == lbits(buf@),
            2 <= asize <= 1024, acc@.len() == asize, lens_ok(acc@),
            sym <= asize, rep <= sym, 1 <= prev <= 15, rep_len <= 15, rep == 0 || rep >= 3,
            -0x1000_0000 <= space <= 32768,
            p2(15) == 32768,
            forall|j: int| sym <= j < asize ==> #[trigger] acc@[j] == 0,
            last <= sym, forall|j: int| last <= j < sym ==> #[trigger] acc@[j] == 0,
            read_lens(cll, b, x.p as int, asize as nat, acc@, sym as nat, space as int, prev as nat,
                      rep as nat, rep_len as nat) == target,
            target == read_lens(cll, lbits(buf@), pos as int, asize as nat, Seq::new(asize as nat, |_i: int| 0u8),
                                0, 32768, 8, 0, 0),
        decreases asize - sym,
    {
        if sym >= asize || space <= 0 {
            if space == 0 { return Some((acc, x.p, last as usize)); } else { return None; }
        }
        let s = match crate::br::sym(cl, buf, &mut x) { None => return None, Some(s) => s };
        if s == 0 {
            sym = sym + 1;
            rep = 0;
        } else if s < 16 {
            proof {
                vbits::prim_read::lemma_p2_eq_pow2(s as nat);
                vstd::bits::lemma_u64_pow2_no_overflow(s as nat);
                vstd::bits::lemma_u64_shl_is_mul(1u64, s as u64);
                assert((32768u64 >> (s as u64)) == 32768u64 / (1u64 << (s as u64))) by (bit_vector)
                    requires 1 <= s < 16;
                assert(lens_ok(acc@.update(sym as int, s as u8)));
            }
            acc.set(sym as usize, s as u8);
            space = space - (32768u64 >> (s as u64)) as i64;
            sym = sym + 1;
            last = sym;
            prev = s as u64;
            rep = 0;
        } else {
            let nb: u64 = if s == 16 { 2 } else { 3 };
            let nl: u64 = if s == 16 { prev } else { 0 };
            let e = match crate::br::take(buf, &mut x, nb) { None => return None, Some(e) => e };
            let old: u64 = if rep_len == nl { rep } else { 0 };
            let mul: u64 = if nb == 2 { 4 } else { 8 };
            assert(mul as nat == p2(nb as nat)) by { reveal_with_fuel(p2, 4); }
            let r: u64 = (if old > 0 { (old - 2) * mul } else { 0 }) + e + 3;
            proof {
                if old > 0 {
                    assert((old - 2) * mul >= (old - 2) * 4) by (nonlinear_arith) requires mul >= 4, old >= 2;
                }
            }
            let delta = r - old;
            if s > 17 || sym + delta > asize {
                return None;
            }
            proof {
                if nl != 0 {
                    vbits::prim_read::lemma_p2_eq_pow2(nl as nat);
                    vstd::bits::lemma_u64_pow2_no_overflow(nl as nat);
                    vstd::bits::lemma_u64_shl_is_mul(1u64, nl);
                    assert((32768u64 >> nl) == 32768u64 / (1u64 << nl)) by (bit_vector) requires 1 <= nl <= 15;
                }
            }
            let ghost a0 = acc@;
            // a run of zeros is there already
            if nl != 0 {
                set_run(&mut acc, sym as usize, delta as usize, nl as u8);
            }
            proof {
                assert(acc@ =~= Seq::new(asize as nat, |j: int|
                    if sym <= j < sym + delta { nl as u8 } else { a0[j] }));
                assert(lens_ok(acc@)) by {
                    assert forall|i: int| 0 <= i < acc@.len() implies #[trigger] acc@[i] <= 15 by {
                        if !(sym <= i < sym + delta) { assert(a0[i] <= 15); }
                    }
                }
            }
            if nl != 0 {
                let per: u64 = 32768u64 >> nl;
                assert(per <= 16384) by (bit_vector) requires per == 32768u64 >> nl, 1 <= nl <= 15;
                assert(delta * per <= 1024 * 16384) by (nonlinear_arith) requires delta <= 1024, per <= 16384;
                space = space - (delta * per) as i64;
            }
            sym = sym + delta;
            if nl != 0 && delta > 0 {
                last = sym;
            }
            rep = r;
            rep_len = nl;
        }
    }
}

/// A prefix code over an alphabet of `asize` symbols: its lengths.
pub fn read_code_x(buf: &[u8], pos: usize, asize: u64) -> (r: Option<(Vec<u8>, usize, usize)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), 2 <= asize <= 1024,
    ensures
        match r {
            Some((v, q, last)) => read_code(lbits(buf@), pos as int, asize as nat) == Some((v@, q as int))
                && q <= 8 * buf.len() && v@.len() == asize && lens_ok(v@)
                && last <= asize && (forall|j: int| last <= j < asize ==> #[trigger] v@[j] == 0),
            None => read_code(lbits(buf@), pos as int, asize as nat) is None,
        },
{
    let h = match getbits_x(buf, pos, 2) { None => return None, Some(h) => h };
    proof { reveal_with_fuel(p2, 3); }
    if h == 1 {
        let r = simple_code_x(buf, pos + 2, asize);
        proof {
            if let Some((v, q)) = &r {
                assert(lens_ok(v@)) by { assert forall|i: int| 0 <= i < v@.len() implies #[trigger] v@[i] <= 15 by {
                    assert(v@[i] <= 3);
                } }
            }
        }
        match r {
            None => None,
            Some((v, q)) => {
                let n = v.len();
                Some((v, q, n))
            }
        }
    } else {
        let (cl, q) = match read_cl_x(buf, pos + 2, h) { None => return None, Some(x) => x };
        proof { assert(lens_ok(cl@)) by { assert forall|i: int| 0 <= i < cl@.len() implies #[trigger] cl@[i] <= 15 by {
            assert(cl@[i] <= 5);
        } } }
        let d = mk_dec(&cl);
        read_lens_x(&d, buf, q, asize)
    }
}

/// A prefix code over an alphabet of `asize` symbols, ready to decode with.
pub fn read_dec(buf: &[u8], pos: usize, asize: u64) -> (r: Option<(Dec, usize)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), 2 <= asize <= 1024,
    ensures
        match r {
            Some((d, q)) => read_code(lbits(buf@), pos as int, asize as nat) == Some((d.lens@, q as int))
                && q <= 8 * buf.len() && dec_wf(&d) && d.lens@.len() == asize,
            None => read_code(lbits(buf@), pos as int, asize as nat) is None,
        },
{
    match read_code_x(buf, pos, asize) {
        None => None,
        Some((v, q, last)) => Some((mk_dec_to(&v, last), q)),
    }
}

} // verus!
