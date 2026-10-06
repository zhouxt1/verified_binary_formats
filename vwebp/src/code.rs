//! Prefix codes (RFC 9649 3.7.2.1): reading their code lengths, checking
//! them, and decoding symbols, each proved to compute its spec function on
//! `lbits(input)`.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
use vbits::lsb::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::{getbits, decode_sym, find_sym, lens_ok, kraft, complete, next_code};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::huff::{lemma_find_n, win_k};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbrotli::spec::{nnz, first_nz, dsym};
pub use vbrotli::code::{getbits_x, zeros};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
pub use vbrotli::code::buf_ok;
use crate::huff::*;
use crate::spec::*;

verus! {

// --------------------------------------------------------------- lemmas

/// A symbol `find_sym` finds is in the alphabet, and its code in the stream.
pub proof fn lemma_find_sym_bound(lens: Seq<u8>, b: Seq<bool>, p: int, l: nat)
    ensures
        match find_sym(lens, b, p, l) {
            Some((s, q)) => s < lens.len() && p < q <= b.len(),
            None => true,
        },
    decreases 16 - l,
{
    if !(l == 0 || l > 15 || p < 0 || p + l > b.len()) {
        lemma_find_n(lens, b, p, l, 0);
        if find_n_is_none(lens, b, p, l) {
            lemma_find_sym_bound(lens, b, p, l + 1);
        }
    }
}

spec fn find_n_is_none(lens: Seq<u8>, b: Seq<bool>, p: int, l: nat) -> bool {
    vdeflate::spec::find_n(lens, b, p, l, 0) is None
}

/// With no nonzero length before `i`, the first nonzero one is the first from `i`.
pub proof fn lemma_first_nz_from(lens: Seq<u8>, i: int)
    requires 0 <= i <= lens.len(), nnz(lens, i) == 0,
    ensures first_nz(lens, 0) == first_nz(lens, i),
    decreases i,
{
    if i > 0 {
        assert(nnz(lens, i) == nnz(lens, i - 1) + (if lens[i - 1] != 0 { 1nat } else { 0nat }));
        lemma_first_nz_from(lens, i - 1);
    }
}

/// The first nonzero length of lengths with some is one of them.
pub proof fn lemma_first_nz_in(lens: Seq<u8>, i: int)
    requires 0 <= i <= lens.len(), nnz(lens, lens.len() as int) >= 1, nnz(lens, i) == 0,
    ensures 0 <= first_nz(lens, i) < lens.len(), lens[first_nz(lens, i)] != 0,
    decreases lens.len() - i,
{
    if i == lens.len() {
        assert(false);
    } else if lens[i] == 0 {
        assert(nnz(lens, i + 1) == 0);
        lemma_first_nz_in(lens, i + 1);
    }
}

proof fn lemma_nnz_le(lens: Seq<u8>, i: int)
    requires 0 <= i,
    ensures nnz(lens, i) <= i,
    decreases i,
{
    if i > 0 { lemma_nnz_le(lens, i - 1); }
}

pub proof fn lemma_p2_consts()
    ensures p2(14) == 16384, p2(15) == 32768, p2(8) == 256, p2(0) == 1, p2(16) == 65536,
        p2(1) == 2, p2(2) == 4, p2(3) == 8, p2(4) == 16, p2(7) == 128,
{
    reveal_with_fuel(p2, 16);
}

/// `1 << k` is `p2(k)`.
pub proof fn lemma_shl1(k: u64)
    requires k < 64,
    ensures (1u64 << k) as nat == p2(k as nat),
{
    vbits::prim_read::lemma_p2_eq_pow2(k as nat);
    vstd::bits::lemma_u64_pow2_no_overflow(k as nat);
    assert(1 * vstd::arithmetic::power2::pow2(k as nat) <= u64::MAX);
    vstd::bits::lemma_u64_shl_is_mul(1u64, k);
}

// ---------------------------------------------------------- the code type

/// A prefix code ready to decode with: its lengths (ghost), whether it has
/// one symbol and which, its symbol list, and a table for its `tb`-bit
/// windows (`mask` is `2^tb - 1`).
pub struct Code {
    pub lens: Ghost<Seq<u8>>,
    pub single: bool,
    pub sym: u16,
    pub h: Huff,
    pub tbl: Vec<u16>,
    pub mask: u64,
    pub first: u64,
    pub idx: u64,
    pub tb: u64,
}

pub open spec fn code_wf(c: &Code) -> bool {
    &&& c.lens@.len() <= 4096
    &&& huff_wf(&c.h, c.lens@)
    &&& tb_ok(c.tb) && c.mask == (1u64 << c.tb) - 1
    &&& fast_wf(c.tbl@, c.lens@, c.tb as nat)
    &&& c.first as nat == next_code(c.lens@, (c.tb + 1) as nat) && c.first as nat <= 8192 * (p2(c.tb as nat) - 1)
    &&& c.idx == c.h.offs[(c.tb + 1) as int]
    &&& c.single == (nnz(c.lens@, c.lens@.len() as int) == 1)
    &&& c.single ==> c.sym as int == first_nz(c.lens@, 0) && (c.sym as int) < c.lens@.len()
}

/// The number of nonzero lengths (up to 2), and the first nonzero one.
fn count_nz(lens: &Vec<u8>) -> (r: (u64, usize))
    requires lens@.len() <= 4096,
    ensures
        (r.0 == 0) == (nnz(lens@, lens@.len() as int) == 0),
        (r.0 == 1) == (nnz(lens@, lens@.len() as int) == 1),
        r.0 <= 2,
        r.0 >= 1 ==> r.1 as int == first_nz(lens@, 0) && r.1 < lens@.len() && lens@[r.1 as int] != 0,
{
    let n = lens.len();
    let mut cnt: u64 = 0;
    let mut first: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            n == lens@.len(), n <= 4096, i <= n, cnt as nat == nnz(lens@, i as int), cnt <= i, cnt <= 1,
            cnt >= 1 ==> first as int == first_nz(lens@, 0) && first < n && lens@[first as int] != 0,
        decreases n - i,
    {
        proof { assert(nnz(lens@, i + 1) == nnz(lens@, i as int) + (if lens@[i as int] != 0 { 1nat } else { 0nat })); }
        if lens[i] != 0 {
            if cnt == 0 {
                proof {
                    lemma_first_nz_from(lens@, i as int);
                }
                first = i;
            }
            cnt = cnt + 1;
            if cnt == 2 {
                // a third or more only adds to the count
                proof {
                    lemma_nnz_mono(lens@, i + 1, n as int);
                }
                return (2, first);
            }
        }
        i = i + 1;
    }
    (cnt, first)
}

proof fn lemma_nnz_mono(lens: Seq<u8>, a: int, b: int)
    requires 0 <= a <= b,
    ensures nnz(lens, a) <= nnz(lens, b),
    decreases b - a,
{
    if a < b { lemma_nnz_mono(lens, a, b - 1); }
}

/// The Kraft sum of the lengths, in units of 2^-15, and whether it is 1.
fn is_complete(lens: &Vec<u8>) -> (r: bool)
    requires lens@.len() <= 4096,
    ensures r == complete(lens@),
{
    let n = lens.len();
    let mut sum: u64 = 0;
    let mut i: usize = 0;
    proof { lemma_p2_consts(); }
    while i < n
        invariant
            n == lens@.len(), n <= 4096, i <= n, sum as nat == kraft(lens@, i as int), sum <= i * 16384,
            p2(14) == 16384, p2(15) == 32768,
        decreases n - i,
    {
        let l = lens[i] as u64;
        if 1 <= l && l <= 15 {
            let d: u64 = 1u64 << (15 - l);
            proof {
                lemma_shl1((15 - l) as u64);
                vbits::prim_read::lemma_p2_mono((15 - l) as nat, 14);
            }
            sum = sum + d;
        }
        i = i + 1;
    }
    sum == 32768
}

/// `code_ok`: whether a decoder takes these lengths, and whether the RFC does.
pub fn code_ok_x(lens: &Vec<u8>) -> (r: Option<bool>)
    requires lens@.len() <= 4096,
    ensures r == code_ok(lens@),
{
    let (cnt, first) = count_nz(lens);
    if cnt == 0 {
        None
    } else if cnt == 1 {
        Some(lens[first] == 1)
    } else if is_complete(lens) {
        Some(true)
    } else {
        None
    }
}

/// Make a code from its lengths.
pub fn mk_code(lens: &Vec<u8>) -> (c: Code)
    requires lens@.len() <= 4096, lens_ok(lens@),
    ensures code_wf(&c), c.lens@ == lens@,
{
    let (cnt, first) = count_nz(lens);
    let h = build(lens.as_slice());
    let m = max_len(&h);
    let tb: u64 = if m > 10 { 10 } else { m };
    let (tbl, fc) = build_table(&h, Ghost(lens@), tb);
    assert(1u64 << tb >= 2) by (bit_vector) requires 1 <= tb <= 10;
    let idx = h.offs[(tb + 1) as usize] as u64;
    Code { lens: Ghost(lens@), single: cnt == 1, sym: first as u16, h, tbl, mask: (1u64 << tb) - 1, first: fc, idx, tb }
}

/// One symbol: `dsym`.
pub fn dsym_x(c: &Code, buf: &[u8], pos: usize) -> (r: Option<(u16, usize)>)
    requires code_wf(c), buf_ok(buf@), pos <= 8 * buf.len(),
    ensures
        match r {
            Some((s, q)) => dsym(c.lens@, lbits(buf@), pos as int) == Some((s as nat, q as int))
                && (s as int) < c.lens@.len() && pos <= q <= 8 * buf.len(),
            None => dsym(c.lens@, lbits(buf@), pos as int) is None,
        },
{
    if c.single {
        return Some((c.sym, pos));
    }
    let w = peek_lsb(buf, pos, 15);
    proof {
        vdeflate::huff::lemma_peek_win_k(buf@, pos as int, 15, w);
        lemma_find_sym_bound(c.lens@, lbits(buf@), pos as int, 1);
    }
    match decode_win(&c.h, &c.tbl, c.mask, c.first, c.idx, c.tb, Ghost(c.lens@), Ghost(lbits(buf@)), pos,
                     8 * buf.len() - pos, w, Ghost(15)) {
        Some((s, l)) => Some((s, pos + l as usize)),
        None => None,
    }
}

/// One symbol from a window `w` of `k` bits at `pos`, taking in 56 bits
/// first if fewer than 15 are left: `dsym`, and the window after it.
#[inline(always)]
pub fn dsym_w(c: &Code, buf: &[u8], Ghost(b): Ghost<Seq<bool>>, pos: usize, w: u64, k: u64)
    -> (r: Option<(u16, usize, u64, u64)>)
    requires code_wf(c), buf_ok(buf@), b == lbits(buf@), pos <= 8 * buf.len(), k <= 56, win_k(b, pos as int, w, k as nat),
    ensures
        match r {
            Some((s, q, w2, k2)) => dsym(c.lens@, b, pos as int) == Some((s as nat, q as int))
                && (s as int) < c.lens@.len() && pos <= q <= 8 * buf.len()
                && k2 <= 56 && win_k(b, q as int, w2, k2 as nat),
            None => dsym(c.lens@, b, pos as int) is None,
        },
{
    if c.single {
        return Some((c.sym, pos, w, k));
    }
    let (w, k) = if k < 15 {
        let w = peek_lsb(buf, pos, 56);
        proof { vdeflate::huff::lemma_peek_win_k(buf@, pos as int, 56, w); }
        (w, 56u64)
    } else {
        (w, k)
    };
    proof { lemma_find_sym_bound(c.lens@, b, pos as int, 1); }
    let avail = 8 * buf.len() - pos;
    let wi = w & c.mask;
    proof { lemma_fast_len(c.tbl@, c.lens@, c.tb, c.mask, w); }
    let e = vsimd::mem::get(c.tbl.as_slice(), wi as usize);
    let l = (e >> 12u16) as u64;
    let r = if e >= 4096 && l as usize <= avail {
        proof { lemma_hit(c.tbl@, c.lens@, c.tb, c.mask, b, pos as int, avail as int, w, k as nat, e); }
        Some((e & 0xfff, l))
    } else {
        dsym_miss(c, Ghost(b), pos, avail, w, Ghost(k as nat), e, wi)
    };
    match r {
        Some((s, l)) => {
            proof { vdeflate::huff::lemma_win_shift(b, pos as int, w, k as nat, l); }
            Some((s, pos + l as usize, w >> l, k - l))
        }
        None => None,
    }
}

/// `dsym_w` for a window the table does not decode, out of line.
#[inline(never)]
fn dsym_miss(c: &Code, Ghost(b): Ghost<Seq<bool>>, pos: usize, avail: usize, w: u64, Ghost(k): Ghost<nat>, e: u16, wi: u64)
    -> (r: Option<(u16, u64)>)
    requires code_wf(c), pos + avail == b.len(), win_k(b, pos as int, w, k), 15 <= k <= 64,
        wi == w & c.mask, wi < c.tbl@.len(), e == c.tbl@[wi as int],
    ensures
        match r {
            Some((s, l)) => find_sym(c.lens@, b, pos as int, 1) == Some((s as nat, pos + l)) && 1 <= l <= 15,
            None => find_sym(c.lens@, b, pos as int, 1) is None,
        },
{
    decode_miss(&c.h, e, wi, c.mask, c.first, c.idx, c.tb, Ghost(c.lens@), Ghost(c.tbl@), Ghost(b), pos, avail, w, Ghost(k))
}

// ---------------------------------------------------- reading the lengths

/// `set_one`.
fn set_one_x(v: &mut Vec<u8>, s: u64)
    requires old(v)@.len() <= 4096,
    ensures final(v)@ == set_one(old(v)@, s as nat),
{
    if s < v.len() as u64 {
        v.set(s as usize, 1);
    }
}

fn simple_code_x(buf: &[u8], pos: usize, asize: u64) -> (r: Option<(Vec<u8>, usize, bool)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), asize <= 4096,
    ensures
        match r {
            Some((v, q, st)) => simple_code(lbits(buf@), pos as int, asize as nat) == Some((v@, q as int, st))
                && q <= 8 * buf.len() && v@.len() == asize && lens_ok(v@),
            None => simple_code(lbits(buf@), pos as int, asize as nat) is None,
        },
{
    let ns = match getbits_x(buf, pos, 1) { None => return None, Some(x) => x };
    let first8 = match getbits_x(buf, pos + 1, 1) { None => return None, Some(x) => x };
    let nb: u64 = if first8 == 1 { 8 } else { 1 };
    let s0 = match getbits_x(buf, pos + 2, nb) { None => return None, Some(x) => x };
    let mut v = zeros(asize as usize);
    let q = pos + 2 + nb as usize;
    set_one_x(&mut v, s0);
    if ns == 0 {
        proof { assert(lens_ok(v@)); }
        return Some((v, q, s0 < asize));
    }
    let s1 = match getbits_x(buf, q, 8) { None => return None, Some(x) => x };
    set_one_x(&mut v, s1);
    proof { assert(lens_ok(v@)); }
    Some((v, q + 8, s0 < asize && s1 < asize))
}

pub const CL_ORDER: [u8; 19] = [17, 18, 0, 1, 2, 3, 4, 5, 16, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];

proof fn lemma_cl_order()
    ensures forall|i: int| 0 <= i < 19 ==> #[trigger] CL_ORDER@[i] as nat == cl_order()[i] && CL_ORDER@[i] < 19,
{
    assert(forall|i: int| 0 <= i < 19 ==> #[trigger] CL_ORDER@[i] as nat == cl_order()[i] && CL_ORDER@[i] < 19)
        by (compute);
}

/// Lengths of at most `m`.
pub open spec fn lens_le(lens: Seq<u8>, m: u8) -> bool {
    forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] <= m
}

fn read_cl_x(buf: &[u8], pos: usize, n: u64) -> (r: Option<(Vec<u8>, usize)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), n <= 19,
    ensures
        match r {
            Some((v, q)) => read_cl(lbits(buf@), pos as int, 0, n as nat, Seq::new(19, |_i: int| 0u8))
                    == Some((v@, q as int))
                && q <= 8 * buf.len() && v@.len() == 19 && lens_le(v@, 7),
            None => read_cl(lbits(buf@), pos as int, 0, n as nat, Seq::new(19, |_i: int| 0u8)) is None,
        },
{
    let ghost b = lbits(buf@);
    let ghost target = read_cl(b, pos as int, 0, n as nat, Seq::new(19, |_i: int| 0u8));
    let mut acc = zeros(19);
    let mut p = pos;
    let mut i: u64 = 0;
    proof { lemma_cl_order(); }
    while i < n
        invariant
            buf_ok(buf@), p <= 8 * buf.len(), b == lbits(buf@), i <= n, n <= 19, acc@.len() == 19,
            lens_le(acc@, 7),
            read_cl(b, p as int, i as nat, n as nat, acc@) == target,
            target == read_cl(lbits(buf@), pos as int, 0, n as nat, Seq::new(19, |_i: int| 0u8)),
            forall|k: int| 0 <= k < 19 ==> #[trigger] CL_ORDER@[k] as nat == cl_order()[k] && CL_ORDER@[k] < 19,
        decreases n - i,
    {
        let v = match getbits_x(buf, p, 3) { None => return None, Some(v) => v };
        proof { lemma_p2_small(3); }
        acc.set(CL_ORDER[i as usize] as usize, v as u8);
        p = p + 3;
        i = i + 1;
    }
    Some((acc, p))
}

proof fn lemma_p2_small(n: nat)
    requires n <= 8,
    ensures p2(n) <= 256, n == 3 ==> p2(n) == 8, n == 2 ==> p2(n) == 4, n == 7 ==> p2(n) == 128,
        n == 4 ==> p2(n) == 16, n == 1 ==> p2(n) == 2,
{
    reveal_with_fuel(p2, 9);
}

/// The lengths of the symbols `sym..sym + r` set to `v`.
fn set_run(acc: &mut Vec<u8>, sym: usize, r: usize, v: u8)
    requires sym + r <= old(acc)@.len(), old(acc)@.len() <= 4096,
    ensures final(acc)@ == Seq::new(old(acc)@.len(), |j: int| if sym <= j < sym + r { v } else { old(acc)@[j] }),
{
    let ghost a0 = old(acc)@;
    let mut j: usize = sym;
    while j < sym + r
        invariant
            sym <= j <= sym + r, sym + r <= a0.len(), a0.len() <= 4096, acc@.len() == a0.len(),
            acc@ =~= Seq::new(a0.len(), |i: int| if sym <= i < j { v } else { a0[i] }),
        decreases sym + r - j,
    {
        acc.set(j, v);
        j = j + 1;
    }
}

fn read_lens_x(cl: &Code, buf: &[u8], pos: usize, asize: u64, left0: u64) -> (r: Option<(Vec<u8>, usize)>)
    requires code_wf(cl), cl.lens@.len() == 19, buf_ok(buf@), pos <= 8 * buf.len(), asize <= 4096,
    ensures
        match r {
            Some((v, q)) => read_lens(cl.lens@, lbits(buf@), pos as int, asize as nat,
                                      Seq::new(asize as nat, |_i: int| 0u8), 0, left0 as nat, 8)
                    == Some((v@, q as int))
                && q <= 8 * buf.len() && v@.len() == asize && lens_ok(v@),
            None => read_lens(cl.lens@, lbits(buf@), pos as int, asize as nat,
                              Seq::new(asize as nat, |_i: int| 0u8), 0, left0 as nat, 8) is None,
        },
{
    let ghost b = lbits(buf@);
    let ghost target = read_lens(cl.lens@, b, pos as int, asize as nat, Seq::new(asize as nat, |_i: int| 0u8), 0, left0 as nat, 8);
    let mut acc = zeros(asize as usize);
    let mut p = pos;
    let mut sym: u64 = 0;
    let mut left: u64 = left0;
    let mut prev: u64 = 8;
    proof { lemma_p2_consts(); }
    while sym < asize && left > 0
        invariant
            code_wf(cl), cl.lens@.len() == 19, buf_ok(buf@), p <= 8 * buf.len(), b == lbits(buf@),
            sym <= asize, asize <= 4096, acc@.len() == asize, lens_ok(acc@), 1 <= prev <= 15,
            read_lens(cl.lens@, b, p as int, asize as nat, acc@, sym as nat, left as nat, prev as nat) == target,
            target == read_lens(cl.lens@, lbits(buf@), pos as int, asize as nat,
                                Seq::new(asize as nat, |_i: int| 0u8), 0, left0 as nat, 8),
            p2(7) == 128, p2(3) == 8, p2(2) == 4,
        decreases asize - sym,
    {
        let (c, q) = match dsym_x(cl, buf, p) {
            None => {
                assert(read_lens(cl.lens@, b, p as int, asize as nat, acc@, sym as nat, left as nat, prev as nat) is None);
                return None;
            }
            Some(x) => x,
        };
        if c < 16 {
            acc.set(sym as usize, c as u8);
            if c != 0 {
                prev = c as u64;
            }
            sym = sym + 1;
            p = q;
        } else {
            let eb: u64 = if c == 16 { 2 } else if c == 17 { 3 } else { 7 };
            let off: u64 = if c == 18 { 11 } else { 3 };
            let v: u64 = if c == 16 { prev } else { 0 };
            let e = match getbits_x(buf, q, eb) { None => return None, Some(e) => e };
            let r = e + off;
            if sym + r > asize {
                assert(read_lens(cl.lens@, b, p as int, asize as nat, acc@, sym as nat, left as nat, prev as nat) is None);
                return None;
            }
            set_run(&mut acc, sym as usize, r as usize, v as u8);
            proof {
                assert(acc@ =~= Seq::new(asize as nat, |j: int| if sym <= j < sym + r { v as u8 } else { acc@[j] }));
            }
            sym = sym + r;
            p = q + eb as usize;
        }
        left = left - 1;
    }
    Some((acc, p))
}

fn normal_code_x(buf: &[u8], pos: usize, asize: u64) -> (r: Option<(Vec<u8>, usize, bool)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), asize <= 4096,
    ensures
        match r {
            Some((v, q, st)) => normal_code(lbits(buf@), pos as int, asize as nat) == Some((v@, q as int, st))
                && q <= 8 * buf.len() && v@.len() == asize && lens_ok(v@),
            None => normal_code(lbits(buf@), pos as int, asize as nat) is None,
        },
{
    let n = match getbits_x(buf, pos, 4) { None => return None, Some(n) => n };
    proof { lemma_p2_small(4); }
    let (cll, q) = match read_cl_x(buf, pos + 4, n + 4) { None => return None, Some(x) => x };
    let st = match code_ok_x(&cll) { None => return None, Some(st) => st };
    let cl = mk_code(&cll);
    let use_len = match getbits_x(buf, q, 1) { None => return None, Some(u) => u };
    if use_len == 0 {
        match read_lens_x(&cl, buf, q + 1, asize, asize) {
            None => None,
            Some((lens, r)) => Some((lens, r, st)),
        }
    } else {
        let k = match getbits_x(buf, q + 1, 3) { None => return None, Some(k) => k };
        proof { lemma_p2_small(3); }
        let nb = 2 + 2 * k;
        let m = match getbits_x(buf, q + 4, nb) { None => return None, Some(m) => m };
        proof { lemma_p2_consts(); vbits::prim_read::lemma_p2_mono(nb as nat, 16); }
        if m + 2 > asize {
            return None;
        }
        match read_lens_x(&cl, buf, q + 4 + nb as usize, asize, m + 2) {
            None => None,
            Some((lens, r)) => Some((lens, r, st)),
        }
    }
}

/// A prefix code over an alphabet of `asize` symbols: `read_code`.
pub fn read_code_x(buf: &[u8], pos: usize, asize: u64) -> (r: Option<(Code, usize, bool)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), asize <= 4096,
    ensures
        match r {
            Some((c, q, st)) => read_code(lbits(buf@), pos as int, asize as nat) == Some((c.lens@, q as int, st))
                && code_wf(&c) && c.lens@.len() == asize && q <= 8 * buf.len(),
            None => read_code(lbits(buf@), pos as int, asize as nat) is None,
        },
{
    let simple = match getbits_x(buf, pos, 1) { None => return None, Some(s) => s };
    let (lens, q, st) = if simple == 1 {
        match simple_code_x(buf, pos + 1, asize) { None => return None, Some(x) => x }
    } else {
        match normal_code_x(buf, pos + 1, asize) { None => return None, Some(x) => x }
    };
    let st2 = match code_ok_x(&lens) { None => return None, Some(s) => s };
    Some((mk_code(&lens), q, st && st2))
}

} // verus!
