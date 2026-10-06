//! The spec's steps depend only on the bits they read, wherever those bits
//! are: `same(b1, pa, b2, pb, n)` says bits `pa..pa + n` of `b1` are bits
//! `pb..pb + n` of `b2`, at an offset that keeps byte alignment. A step that
//! reads bits `pa..q` of `b1` gives the same result on `b2` at `pb`, its
//! position moved by `pb - pa`. With `pa == pb` this is decoding a prefix of
//! the stream as the stream; with an offset, it is decoding the stream after
//! dropping whole bytes already used. And each step reads a bounded number of
//! bits, so a step that fails with that many bits in hand fails on every
//! stream that has them.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::{p2, bits_val};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::lsb::lval;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::{getbits, codebits, find_n, find_sym, decode_sym, maxbits};
use crate::spec::*;

verus! {

pub open spec fn same(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, n: int) -> bool {
    &&& 0 <= pa && 0 <= pb && 0 <= n && pa + n <= b1.len() && pb + n <= b2.len()
    &&& (pb - pa) % 8 == 0
    &&& forall|j: int| 0 <= j < n ==> #[trigger] b1[pa + j] == b2[pb + j]
}

/// A position moved from `b1` at `pa` to `b2` at `pb`.
pub open spec fn mv(q: int, pa: int, pb: int) -> int { q - pa + pb }

pub proof fn lemma_same_sub(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, n: int, a: int, m: int)
    requires same(b1, pa, b2, pb, n), 0 <= a, 0 <= m, a + m <= n,
    ensures same(b1, pa + a, b2, pb + a, m),
{
    assert forall|j: int| 0 <= j < m implies #[trigger] b1[(pa + a) + j] == b2[(pb + a) + j] by {
        assert(b1[pa + (a + j)] == b2[pb + (a + j)]);
    }
}

// ------------------------------------------------------------ bit fields

pub proof fn lemma_getbits_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, n: int, k: nat)
    requires same(b1, pa, b2, pb, n), k <= n,
    ensures getbits(b2, pb, k) == getbits(b1, pa, k), getbits(b1, pa, k) is Some,
{
    assert(b1.subrange(pa, pa + k) =~= b2.subrange(pb, pb + k)) by {
        assert forall|j: int| 0 <= j < k implies #[trigger] b1.subrange(pa, pa + k)[j] == b2.subrange(pb, pb + k)[j] by {
            assert(b1[pa + j] == b2[pb + j]);
        }
    }
}

pub proof fn lemma_getbits_pos(b: Seq<bool>, p: int, k: nat)
    ensures getbits(b, p, k) is Some ==> 0 <= p && p + k <= b.len(),
{
}

/// Fill bits: the same after a move by whole bytes.
pub proof fn lemma_zero_fill_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, n: int)
    requires same(b1, pa, b2, pb, n), align8(pa) - pa <= n,
    ensures zero_fill(b2, pb) == zero_fill(b1, pa), align8(pb) == mv(align8(pa), pa, pb),
{
    assert(align8(pb) - pb == align8(pa) - pa) by {
        assert(pb % 8 == pa % 8) by (nonlinear_arith) requires (pb - pa) % 8 == 0;
    }
    lemma_getbits_mv(b1, pa, b2, pb, n, (align8(pa) - pa) as nat);
}

pub proof fn lemma_bytes_at_mv(b1: Seq<bool>, q1: int, b2: Seq<bool>, q2: int, n: int, m: nat)
    requires same(b1, q1, b2, q2, n), 8 * m <= n,
    ensures bytes_at(b2, q2, m) == bytes_at(b1, q1, m),
{
    assert(bytes_at(b2, q2, m) =~= bytes_at(b1, q1, m)) by {
        assert forall|j: int| 0 <= j < m implies #[trigger] bytes_at(b2, q2, m)[j] == bytes_at(b1, q1, m)[j] by {
            assert(b1.subrange(q1 + 8 * j, q1 + 8 * j + 8) =~= b2.subrange(q2 + 8 * j, q2 + 8 * j + 8)) by {
                assert forall|i: int| 0 <= i < 8 implies
                    #[trigger] b1.subrange(q1 + 8 * j, q1 + 8 * j + 8)[i] == b2.subrange(q2 + 8 * j, q2 + 8 * j + 8)[i] by {
                    assert(b1[q1 + (8 * j + i)] == b2[q2 + (8 * j + i)]);
                }
            }
        }
    }
}

// --------------------------------------------------------- prefix codes

proof fn lemma_find_n_mv(lens: Seq<u8>, b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, l: nat, n: int)
    requires codebits(b1, pa, l) == codebits(b2, pb, l),
    ensures find_n(lens, b1, pa, l, n) == find_n(lens, b2, pb, l, n),
    decreases lens.len() - n,
{
    if 0 <= n < lens.len() {
        lemma_find_n_mv(lens, b1, pa, b2, pb, l, n + 1);
    }
}

pub proof fn lemma_find_sym_bound(lens: Seq<u8>, b: Seq<bool>, p: int, l: nat)
    ensures find_sym(lens, b, p, l) matches Some((s, q)) ==> p + l <= q <= p + 15 && q <= b.len() && 0 <= p,
    decreases 16 - l,
{
    if !(l == 0 || l > maxbits() || p < 0 || p + l > b.len()) {
        lemma_find_sym_bound(lens, b, p, l + 1);
    }
}

proof fn lemma_find_sym_mv(lens: Seq<u8>, b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, n: int, l: nat)
    requires
        find_sym(lens, b1, pa, l) matches Some((s, q)) && q - pa <= n,
        same(b1, pa, b2, pb, n),
    ensures
        find_sym(lens, b2, pb, l) == (match find_sym(lens, b1, pa, l) {
            Some((s, q)) => Some((s, mv(q, pa, pb))),
            None => None,
        }),
    decreases 16 - l,
{
    lemma_find_sym_bound(lens, b1, pa, l);
    let q = find_sym(lens, b1, pa, l).unwrap().1;
    assert(l <= q - pa);
    assert(b1.subrange(pa, pa + l) =~= b2.subrange(pb, pb + l)) by {
        assert forall|j: int| 0 <= j < l implies #[trigger] b1.subrange(pa, pa + l)[j] == b2.subrange(pb, pb + l)[j] by {
            assert(b1[pa + j] == b2[pb + j]);
        }
    }
    lemma_find_n_mv(lens, b1, pa, b2, pb, l, 0);
    if find_n(lens, b1, pa, l, 0) is None {
        lemma_find_sym_mv(lens, b1, pa, b2, pb, n, l + 1);
    }
}

pub proof fn lemma_dsym_mv(lens: Seq<u8>, b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, n: int)
    requires dsym(lens, b1, pa) matches Some((s, q)) && q - pa <= n, same(b1, pa, b2, pb, n),
    ensures dsym(lens, b2, pb) == (match dsym(lens, b1, pa) { Some((s, q)) => Some((s, mv(q, pa, pb))), None => None }),
{
    if nnz(lens, lens.len() as int) != 1 {
        lemma_find_sym_mv(lens, b1, pa, b2, pb, n, 1);
    }
}

/// A symbol takes at most 15 bits (none, for a code of one symbol), and a
/// found symbol is one of the code's.
pub proof fn lemma_dsym_pos(lens: Seq<u8>, b: Seq<bool>, p: int)
    ensures dsym(lens, b, p) matches Some((s, q)) ==> p <= q <= p + 15 && (q == p || q <= b.len()) && s < lens.len(),
{
    if nnz(lens, lens.len() as int) == 1 {
        crate::code::lemma_first_nz_found(lens, 0);
    } else {
        lemma_find_sym_bound(lens, b, p, 1);
        vdeflate::huff::lemma_find_sym_sym(lens, b, p, 1);
    }
}

/// A result with a position, the position moved by `d`.
pub open spec fn sh2<A>(r: Option<(A, int)>, d: int) -> Option<(A, int)> {
    match r { Some((a, q)) => Some((a, q + d)), None => None }
}

pub open spec fn sh3<A, B>(r: Option<(A, B, int)>, d: int) -> Option<(A, B, int)> {
    match r { Some((a, b, q)) => Some((a, b, q + d)), None => None }
}

pub open spec fn pos2<A>(r: Option<(A, int)>) -> int { match r { Some((a, q)) => q, None => 0 } }

pub open spec fn pos3<A, B>(r: Option<(A, B, int)>) -> int { match r { Some((a, b, q)) => q, None => 0 } }

// ------------------------------------------------------ simple prefix codes

pub proof fn lemma_read_syms_pos(b: Seq<bool>, p: int, asize: nat, n: nat, acc: Seq<nat>)
    ensures read_syms(b, p, asize, n, acc) matches Some((v, q)) ==>
        p <= q && (acc.len() <= n ==> q <= p + 11 * (n - acc.len())),
    decreases n - acc.len(),
{
    if acc.len() < n {
        if let Some(v) = getbits(b, p, abits(asize)) {
            if v < asize {
                lemma_read_syms_pos(b, p + abits(asize), asize, n, acc.push(v));
            }
        }
    }
}

pub proof fn lemma_read_syms_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int, asize: nat, n: nat, acc: Seq<nat>)
    requires read_syms(b1, pa, asize, n, acc) is Some, pos2(read_syms(b1, pa, asize, n, acc)) - pa <= nn,
        same(b1, pa, b2, pb, nn),
    ensures read_syms(b2, pb, asize, n, acc) == sh2(read_syms(b1, pa, asize, n, acc), pb - pa),
    decreases n - acc.len(),
{
    if acc.len() < n {
        let k = abits(asize);
        let v = getbits(b1, pa, k).unwrap();
        lemma_read_syms_pos(b1, pa + k, asize, n, acc.push(v));
        lemma_getbits_mv(b1, pa, b2, pb, nn, k);
        lemma_same_sub(b1, pa, b2, pb, nn, k as int, nn - k);
        lemma_read_syms_mv(b1, pa + k, b2, pb + k, nn - k, asize, n, acc.push(v));
    }
}

pub proof fn lemma_simple_code_pos(b: Seq<bool>, p: int, asize: nat)
    ensures simple_code(b, p, asize) matches Some((v, q)) ==> p + 2 <= q <= p + 47,
{
    if let Some(m) = getbits(b, p, 2) {
        lemma_getbits_bound_(b, p, 2);
        assert(p2(2) == 4) by { reveal_with_fuel(p2, 3); }
        lemma_read_syms_pos(b, p + 2, asize, m + 1, Seq::empty());
    }
}

pub proof fn lemma_getbits_bound_(b: Seq<bool>, p: int, n: nat)
    requires getbits(b, p, n) is Some,
    ensures getbits(b, p, n).unwrap() < p2(n),
{
    vbits::lsb::lemma_lval_bound(b.subrange(p, p + n));
}

pub proof fn lemma_simple_code_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int, asize: nat)
    requires simple_code(b1, pa, asize) is Some, pos2(simple_code(b1, pa, asize)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures simple_code(b2, pb, asize) == sh2(simple_code(b1, pa, asize), pb - pa),
{
    let m = getbits(b1, pa, 2).unwrap();
    lemma_getbits_bound_(b1, pa, 2);
    assert(p2(2) == 4) by { reveal_with_fuel(p2, 3); }
    let (sy, q) = read_syms(b1, pa + 2, asize, m + 1, Seq::empty()).unwrap();
    lemma_read_syms_pos(b1, pa + 2, asize, m + 1, Seq::empty());
    lemma_simple_code_pos(b1, pa, asize);
    let fq = pos2(simple_code(b1, pa, asize));
    assert(q <= fq);
    lemma_getbits_mv(b1, pa, b2, pb, nn, 2);
    lemma_same_sub(b1, pa, b2, pb, nn, 2, nn - 2);
    lemma_read_syms_mv(b1, pa + 2, b2, pb + 2, nn - 2, asize, m + 1, Seq::empty());
    assert(read_syms(b2, pb + 2, asize, m + 1, Seq::empty()) == Some((sy, mv(q, pa, pb))));
    if m == 3 {
        assert(fq == q + 1);
        lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
        lemma_getbits_mv(b1, q, b2, mv(q, pa, pb), nn - (q - pa), 1);
        assert(getbits(b2, mv(q, pa, pb), 1) == getbits(b1, q, 1));
    }
}

// ----------------------------------------------------- complex prefix codes

pub proof fn lemma_cl_len_pos(b: Seq<bool>, p: int)
    ensures cl_len(b, p) matches Some((v, q)) ==> p + 2 <= q <= p + 4,
{
}

pub proof fn lemma_cl_len_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int)
    requires cl_len(b1, pa) is Some, pos2(cl_len(b1, pa)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures cl_len(b2, pb) == sh2(cl_len(b1, pa), pb - pa),
{
    lemma_cl_len_pos(b1, pa);
    let q = pos2(cl_len(b1, pa));
    lemma_getbits_mv(b1, pa, b2, pb, nn, 2);
    let v = getbits(b1, pa, 2).unwrap();
    lemma_getbits_bound_(b1, pa, 2);
    assert(p2(2) == 4) by { reveal_with_fuel(p2, 3); }
    if v == 3 {
        assert(q >= pa + 3);
        lemma_same_sub(b1, pa, b2, pb, nn, 2, nn - 2);
        lemma_getbits_mv(b1, pa + 2, b2, pb + 2, nn - 2, 1);
        let x = getbits(b1, pa + 2, 1).unwrap();
        if x != 0 {
            assert(q == pa + 4);
            lemma_same_sub(b1, pa, b2, pb, nn, 3, nn - 3);
            lemma_getbits_mv(b1, pa + 3, b2, pb + 3, nn - 3, 1);
            let y = getbits(b1, pa + 3, 1).unwrap();
            assert(cl_len(b2, pb) == Some((if y == 0 { 1nat } else { 5nat }, pb + 4)));
        } else {
            assert(cl_len(b2, pb) == Some((2nat, pb + 3)));
        }
    }
}

pub proof fn lemma_read_cl_pos(b: Seq<bool>, p: int, i: nat, acc: Seq<u8>, space: int, num: nat)
    ensures read_cl(b, p, i, acc, space, num) matches Some((v, q)) ==>
        p <= q && (i <= 18 ==> q <= p + 4 * (18 - i)),
    decreases 18 - i,
{
    if i < 18 {
        lemma_cl_len_pos(b, p);
        if let Some((v, q)) = cl_len(b, p) {
            let acc2 = acc.update(cl_order()[i as int] as int, v as u8);
            if v == 0 {
                lemma_read_cl_pos(b, q, i + 1, acc2, space, num);
            } else {
                let s2 = space - (32nat / p2(v)) as int;
                lemma_read_cl_pos(b, q, i + 1, acc2, s2, num + 1);
            }
        }
    }
}

pub proof fn lemma_read_cl_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int,
                              i: nat, acc: Seq<u8>, space: int, num: nat)
    requires read_cl(b1, pa, i, acc, space, num) is Some, pos2(read_cl(b1, pa, i, acc, space, num)) - pa <= nn,
        same(b1, pa, b2, pb, nn),
    ensures read_cl(b2, pb, i, acc, space, num) == sh2(read_cl(b1, pa, i, acc, space, num), pb - pa),
    decreases 18 - i,
{
    if i < 18 {
        let (v, q) = cl_len(b1, pa).unwrap();
        lemma_cl_len_pos(b1, pa);
        let acc2 = acc.update(cl_order()[i as int] as int, v as u8);
        let s2 = space - (32nat / p2(v)) as int;
        if v == 0 {
            lemma_read_cl_pos(b1, q, i + 1, acc2, space, num);
        } else if s2 > 0 {
            lemma_read_cl_pos(b1, q, i + 1, acc2, s2, num + 1);
        }
        lemma_cl_len_mv(b1, pa, b2, pb, nn);
        lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
        if v == 0 {
            lemma_read_cl_mv(b1, q, b2, mv(q, pa, pb), nn - (q - pa), i + 1, acc2, space, num);
        } else if s2 > 0 {
            lemma_read_cl_mv(b1, q, b2, mv(q, pa, pb), nn - (q - pa), i + 1, acc2, s2, num + 1);
        }
    }
}

pub proof fn lemma_read_lens_pos(cl: Seq<u8>, b: Seq<bool>, p: int, asize: nat, acc: Seq<u8>, sym: nat,
                                 space: int, prev: nat, rep: nat, rep_len: nat)
    ensures read_lens(cl, b, p, asize, acc, sym, space, prev, rep, rep_len) matches Some((v, q)) ==>
        p <= q && (sym <= asize ==> q <= p + 18 * (asize - sym)),
    decreases asize - sym,
{
    if !(sym >= asize || space <= 0) {
        lemma_dsym_pos(cl, b, p);
        if let Some((s, q)) = dsym(cl, b, p) {
            if s == 0 {
                lemma_read_lens_pos(cl, b, q, asize, acc, sym + 1, space, prev, 0, rep_len);
            } else if s < 16 {
                lemma_read_lens_pos(cl, b, q, asize, acc.update(sym as int, s as u8), sym + 1,
                                    space - (32768nat / p2(s)) as int, s, 0, rep_len);
            } else {
                let nb: nat = if s == 16 { 2 } else { 3 };
                let nl: nat = if s == 16 { prev } else { 0 };
                if let Some(e) = getbits(b, q, nb) {
                    let old: nat = if rep_len == nl { rep } else { 0 };
                    let r: nat = (if old > 0 { ((old - 2) * p2(nb)) as nat } else { 0nat }) + e + 3;
                    let delta = r - old;
                    if !(s > 17 || delta <= 0 || sym + delta > asize) {
                        let acc2 = Seq::new(asize, |j: int| if sym <= j < sym + delta { nl as u8 } else { acc[j] });
                        let sp2 = if nl == 0 { space } else { space - delta * (32768nat / p2(nl)) as int };
                        lemma_read_lens_pos(cl, b, q + nb, asize, acc2, (sym + delta) as nat, sp2, prev, r, nl);
                    }
                }
            }
        }
    }
}

pub proof fn lemma_read_lens_mv(cl: Seq<u8>, b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int,
                                asize: nat, acc: Seq<u8>, sym: nat, space: int, prev: nat, rep: nat, rep_len: nat)
    requires
        read_lens(cl, b1, pa, asize, acc, sym, space, prev, rep, rep_len) is Some,
        pos2(read_lens(cl, b1, pa, asize, acc, sym, space, prev, rep, rep_len)) - pa <= nn,
        same(b1, pa, b2, pb, nn),
    ensures read_lens(cl, b2, pb, asize, acc, sym, space, prev, rep, rep_len)
        == sh2(read_lens(cl, b1, pa, asize, acc, sym, space, prev, rep, rep_len), pb - pa),
    decreases asize - sym,
{
    if !(sym >= asize || space <= 0) {
        let (s, q) = dsym(cl, b1, pa).unwrap();
        lemma_dsym_pos(cl, b1, pa);
        if s == 0 {
            lemma_read_lens_pos(cl, b1, q, asize, acc, sym + 1, space, prev, 0, rep_len);
            lemma_dsym_mv(cl, b1, pa, b2, pb, nn);
            lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
            lemma_read_lens_mv(cl, b1, q, b2, mv(q, pa, pb), nn - (q - pa), asize, acc, sym + 1, space, prev, 0, rep_len);
        } else if s < 16 {
            let acc2 = acc.update(sym as int, s as u8);
            let sp = space - (32768nat / p2(s)) as int;
            lemma_read_lens_pos(cl, b1, q, asize, acc2, sym + 1, sp, s, 0, rep_len);
            lemma_dsym_mv(cl, b1, pa, b2, pb, nn);
            lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
            lemma_read_lens_mv(cl, b1, q, b2, mv(q, pa, pb), nn - (q - pa), asize, acc2, sym + 1, sp, s, 0, rep_len);
        } else {
            let nb: nat = if s == 16 { 2 } else { 3 };
            let nl: nat = if s == 16 { prev } else { 0 };
            let e = getbits(b1, q, nb).unwrap();
            let old: nat = if rep_len == nl { rep } else { 0 };
            let r: nat = (if old > 0 { ((old - 2) * p2(nb)) as nat } else { 0nat }) + e + 3;
            let delta = r - old;
            let acc2 = Seq::new(asize, |j: int| if sym <= j < sym + delta { nl as u8 } else { acc[j] });
            let sp2 = if nl == 0 { space } else { space - delta * (32768nat / p2(nl)) as int };
            lemma_read_lens_pos(cl, b1, q + nb, asize, acc2, (sym + delta) as nat, sp2, prev, r, nl);
            lemma_dsym_mv(cl, b1, pa, b2, pb, nn);
            lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
            lemma_getbits_mv(b1, q, b2, mv(q, pa, pb), nn - (q - pa), nb);
            lemma_same_sub(b1, pa, b2, pb, nn, q + nb - pa, nn - (q + nb - pa));
            lemma_read_lens_mv(cl, b1, q + nb, b2, mv(q + nb, pa, pb), nn - (q + nb - pa), asize, acc2,
                               (sym + delta) as nat, sp2, prev, r, nl);
        }
    }
}

/// The most bits a prefix code over `asize` symbols takes.
pub open spec fn code_bits(asize: nat) -> nat { 74 + 18 * asize }

pub proof fn lemma_read_code_pos(b: Seq<bool>, p: int, asize: nat)
    ensures read_code(b, p, asize) matches Some((v, q)) ==> p + 2 <= q <= p + code_bits(asize),
{
    if let Some(h) = getbits(b, p, 2) {
        lemma_getbits_bound_(b, p, 2);
        assert(p2(2) == 4) by { reveal_with_fuel(p2, 3); }
        if h == 1 {
            lemma_simple_code_pos(b, p + 2, asize);
        } else {
            lemma_read_cl_pos(b, p + 2, h, Seq::new(18, |_i: int| 0u8), 32, 0);
            if let Some((cl, q)) = read_cl(b, p + 2, h, Seq::new(18, |_i: int| 0u8), 32, 0) {
                lemma_read_lens_pos(cl, b, q, asize, Seq::new(asize, |_i: int| 0u8), 0, 32768, 8, 0, 0);
            }
        }
    }
}

pub proof fn lemma_read_code_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int, asize: nat)
    requires read_code(b1, pa, asize) is Some, pos2(read_code(b1, pa, asize)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures read_code(b2, pb, asize) == sh2(read_code(b1, pa, asize), pb - pa),
{
    let h = getbits(b1, pa, 2).unwrap();
    lemma_read_code_pos(b1, pa, asize);
    lemma_getbits_mv(b1, pa, b2, pb, nn, 2);
    lemma_same_sub(b1, pa, b2, pb, nn, 2, nn - 2);
    if h == 1 {
        lemma_simple_code_mv(b1, pa + 2, b2, pb + 2, nn - 2, asize);
    } else {
        let (cl, q) = read_cl(b1, pa + 2, h, Seq::new(18, |_i: int| 0u8), 32, 0).unwrap();
        lemma_read_cl_pos(b1, pa + 2, h, Seq::new(18, |_i: int| 0u8), 32, 0);
        lemma_read_lens_pos(cl, b1, q, asize, Seq::new(asize, |_i: int| 0u8), 0, 32768, 8, 0, 0);
        lemma_read_cl_mv(b1, pa + 2, b2, pb + 2, nn - 2, h, Seq::new(18, |_i: int| 0u8), 32, 0);
        lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
        lemma_read_lens_mv(cl, b1, q, b2, mv(q, pa, pb), nn - (q - pa), asize, Seq::new(asize, |_i: int| 0u8),
                           0, 32768, 8, 0, 0);
    }
}

// ------------------------------------------------------------ the header

pub proof fn lemma_varlen8_pos(b: Seq<bool>, p: int)
    ensures varlen8(b, p) matches Some((v, q)) ==> p + 1 <= q <= p + 11 && v <= 255,
{
    if let Some(x) = getbits(b, p, 1) {
        if x != 0 {
            if let Some(n) = getbits(b, p + 1, 3) {
                lemma_getbits_bound_(b, p + 1, 3);
                assert(p2(3) == 8) by { reveal_with_fuel(p2, 4); }
                if n != 0 {
                    if let Some(e) = getbits(b, p + 4, n) {
                        lemma_getbits_bound_(b, p + 4, n);
                        vbits::prim_read::lemma_p2_mono(n, 7);
                        assert(p2(7) == 128 && p2(8) == 256) by { reveal_with_fuel(p2, 9); }
                        assert(p2(n) + e < 256) by {
                            assert(e < p2(n));
                            assert(p2(n) <= 128);
                        }
                    }
                }
            }
        }
    }
}

pub proof fn lemma_varlen8_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int)
    requires varlen8(b1, pa) is Some, pos2(varlen8(b1, pa)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures varlen8(b2, pb) == sh2(varlen8(b1, pa), pb - pa),
{
    lemma_varlen8_pos(b1, pa);
    lemma_getbits_mv(b1, pa, b2, pb, nn, 1);
    if getbits(b1, pa, 1).unwrap() != 0 {
        lemma_same_sub(b1, pa, b2, pb, nn, 1, nn - 1);
        lemma_getbits_mv(b1, pa + 1, b2, pb + 1, nn - 1, 3);
        let n = getbits(b1, pa + 1, 3).unwrap();
        if n != 0 {
            lemma_same_sub(b1, pa, b2, pb, nn, 4, nn - 4);
            lemma_getbits_mv(b1, pa + 4, b2, pb + 4, nn - 4, n);
        }
    }
}

pub proof fn lemma_bc_extra()
    ensures forall|i: int| 0 <= i < 26 ==> 2 <= #[trigger] bc_extra()[i] <= 24,
{
    assert(forall|i: int| 0 <= i < 26 ==> 2 <= #[trigger] bc_extra()[i] <= 24) by (compute);
}

pub proof fn lemma_read_count_pos(code: Seq<u8>, b: Seq<bool>, p: int)
    ensures read_count(code, b, p) matches Some((v, q)) ==> p + 2 <= q <= p + 39,
{
    lemma_dsym_pos(code, b, p);
    lemma_bc_extra();
}

pub proof fn lemma_read_count_mv(code: Seq<u8>, b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int)
    requires read_count(code, b1, pa) is Some, pos2(read_count(code, b1, pa)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures read_count(code, b2, pb) == sh2(read_count(code, b1, pa), pb - pa),
{
    lemma_dsym_pos(code, b1, pa);
    let (s, q) = dsym(code, b1, pa).unwrap();
    assert(pos2(read_count(code, b1, pa)) == q + bc_extra()[s as int]);
    lemma_dsym_mv(code, b1, pa, b2, pb, nn);
    lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
    lemma_getbits_mv(b1, q, b2, mv(q, pa, pb), nn - (q - pa), bc_extra()[s as int]);
}

pub proof fn lemma_read_cmap_vals_pos(code: Seq<u8>, rlemax: nat, b: Seq<bool>, p: int, size: nat, acc: Seq<nat>)
    requires rlemax <= 16,
    ensures read_cmap_vals(code, rlemax, b, p, size, acc) matches Some((v, q)) ==>
        p <= q && (acc.len() <= size ==> q <= p + 31 * (size - acc.len())),
    decreases size - acc.len(),
{
    if acc.len() < size {
        lemma_dsym_pos(code, b, p);
        if let Some((s, q)) = dsym(code, b, p) {
            if s == 0 {
                lemma_read_cmap_vals_pos(code, rlemax, b, q, size, acc.push(0));
            } else if s <= rlemax {
                if let Some(e) = getbits(b, q, s) {
                    if acc.len() + p2(s) + e <= size {
                        vbits::bitspec::lemma_p2_pos(s);
                        lemma_read_cmap_vals_pos(code, rlemax, b, q + s, size, acc + Seq::new(p2(s) + e, |_i: int| 0nat));
                    }
                }
            } else {
                lemma_read_cmap_vals_pos(code, rlemax, b, q, size, acc.push((s - rlemax) as nat));
            }
        }
    }
}

pub proof fn lemma_read_cmap_vals_mv(code: Seq<u8>, rlemax: nat, b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int,
                                     nn: int, size: nat, acc: Seq<nat>)
    requires rlemax <= 16, read_cmap_vals(code, rlemax, b1, pa, size, acc) is Some,
        pos2(read_cmap_vals(code, rlemax, b1, pa, size, acc)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures read_cmap_vals(code, rlemax, b2, pb, size, acc) == sh2(read_cmap_vals(code, rlemax, b1, pa, size, acc), pb - pa),
    decreases size - acc.len(),
{
    if acc.len() < size {
        lemma_dsym_pos(code, b1, pa);
        let (s, q) = dsym(code, b1, pa).unwrap();
        if s == 0 {
            lemma_read_cmap_vals_pos(code, rlemax, b1, q, size, acc.push(0));
            lemma_dsym_mv(code, b1, pa, b2, pb, nn);
            lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
            lemma_read_cmap_vals_mv(code, rlemax, b1, q, b2, mv(q, pa, pb), nn - (q - pa), size, acc.push(0));
        } else if s <= rlemax {
            let e = getbits(b1, q, s).unwrap();
            let acc2 = acc + Seq::new(p2(s) + e, |_i: int| 0nat);
            vbits::bitspec::lemma_p2_pos(s);
            lemma_read_cmap_vals_pos(code, rlemax, b1, q + s, size, acc2);
            lemma_dsym_mv(code, b1, pa, b2, pb, nn);
            lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
            lemma_getbits_mv(b1, q, b2, mv(q, pa, pb), nn - (q - pa), s);
            lemma_same_sub(b1, pa, b2, pb, nn, q + s - pa, nn - (q + s - pa));
            lemma_read_cmap_vals_mv(code, rlemax, b1, q + s, b2, mv(q + s, pa, pb), nn - (q + s - pa), size, acc2);
        } else {
            lemma_read_cmap_vals_pos(code, rlemax, b1, q, size, acc.push((s - rlemax) as nat));
            lemma_dsym_mv(code, b1, pa, b2, pb, nn);
            lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
            lemma_read_cmap_vals_mv(code, rlemax, b1, q, b2, mv(q, pa, pb), nn - (q - pa), size, acc.push((s - rlemax) as nat));
        }
    }
}

/// The most bits a context map of `size` entries takes, with its NTREES.
pub open spec fn cmap_bits(size: nat) -> nat { 4987 + 31 * size }

pub proof fn lemma_read_cmap_pos(b: Seq<bool>, p: int, size: nat)
    ensures read_cmap(b, p, size) matches Some((v, nt, q)) ==> p + 1 <= q <= p + cmap_bits(size) && 1 <= nt <= 256,
{
    lemma_varlen8_pos(b, p);
    if let Some((t, q)) = varlen8(b, p) {
        if t != 0 {
            let ntrees = t + 1;
            let rle = match getbits(b, q, 1) {
                None => None,
                Some(x) => if x == 0 { Some((0nat, q + 1)) } else {
                    match getbits(b, q + 1, 4) { None => None, Some(r) => Some((r + 1, q + 5)) }
                },
            };
            if let Some(x) = getbits(b, q, 1) {
                if x != 0 {
                    if let Some(r) = getbits(b, q + 1, 4) {
                        lemma_getbits_bound_(b, q + 1, 4);
                        assert(p2(4) == 16) by { reveal_with_fuel(p2, 5); }
                    }
                }
            }
            if let Some((rlemax, q2)) = rle {
                lemma_read_code_pos(b, q2, ntrees + rlemax);
                if let Some((code, q3)) = read_code(b, q2, ntrees + rlemax) {
                    lemma_read_cmap_vals_pos(code, rlemax, b, q3, size, Seq::empty());
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_read_cmap_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int, size: nat)
    requires read_cmap(b1, pa, size) is Some, pos3(read_cmap(b1, pa, size)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures read_cmap(b2, pb, size) == sh3(read_cmap(b1, pa, size), pb - pa),
{
    hide(read_code);
    hide(read_cmap_vals);
    hide(varlen8);
    let fq = pos3(read_cmap(b1, pa, size));
    lemma_varlen8_pos(b1, pa);
    let (t, q) = varlen8(b1, pa).unwrap();
    if t == 0 {
        assert(fq == q);
        lemma_varlen8_mv(b1, pa, b2, pb, nn);
    } else {
        let ntrees = t + 1;
        let x = getbits(b1, q, 1).unwrap();
        let (rlemax, q2): (nat, int) = if x == 0 { (0nat, q + 1) } else {
            let r = getbits(b1, q + 1, 4).unwrap();
            (r + 1, q + 5)
        };
        if x != 0 {
            lemma_getbits_bound_(b1, q + 1, 4);
            assert(p2(4) == 16) by { reveal_with_fuel(p2, 5); }
        }
        lemma_read_code_pos(b1, q2, ntrees + rlemax);
        let (code, q3) = read_code(b1, q2, ntrees + rlemax).unwrap();
        lemma_read_cmap_vals_pos(code, rlemax, b1, q3, size, Seq::empty());
        let (v, q4) = read_cmap_vals(code, rlemax, b1, q3, size, Seq::empty()).unwrap();
        assert(fq == q4 + 1);
        lemma_varlen8_mv(b1, pa, b2, pb, nn);
        lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
        lemma_getbits_mv(b1, q, b2, mv(q, pa, pb), nn - (q - pa), 1);
        if x != 0 {
            lemma_same_sub(b1, pa, b2, pb, nn, q + 1 - pa, nn - (q + 1 - pa));
            lemma_getbits_mv(b1, q + 1, b2, mv(q + 1, pa, pb), nn - (q + 1 - pa), 4);
        }
        lemma_same_sub(b1, pa, b2, pb, nn, q2 - pa, nn - (q2 - pa));
        lemma_read_code_mv(b1, q2, b2, mv(q2, pa, pb), nn - (q2 - pa), ntrees + rlemax);
        lemma_same_sub(b1, pa, b2, pb, nn, q3 - pa, nn - (q3 - pa));
        lemma_read_cmap_vals_mv(code, rlemax, b1, q3, b2, mv(q3, pa, pb), nn - (q3 - pa), size, Seq::empty());
        lemma_same_sub(b1, pa, b2, pb, nn, q4 - pa, nn - (q4 - pa));
        lemma_getbits_mv(b1, q4, b2, mv(q4, pa, pb), nn - (q4 - pa), 1);
    }
}

pub proof fn lemma_read_cat_pos(b: Seq<bool>, p: int)
    ensures read_cat(b, p) matches Some((c, q)) ==> p + 1 <= q <= p + 5310 && 1 <= c.n <= 256,
{
    lemma_varlen8_pos(b, p);
    if let Some((v, q)) = varlen8(b, p) {
        if v != 0 {
            lemma_read_code_pos(b, q, v + 3);
            if let Some((tcode, q2)) = read_code(b, q, v + 3) {
                lemma_read_code_pos(b, q2, 26);
                if let Some((ccode, q3)) = read_code(b, q2, 26) {
                    lemma_read_count_pos(ccode, b, q3);
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_read_cat_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int)
    requires read_cat(b1, pa) is Some, pos2(read_cat(b1, pa)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures read_cat(b2, pb) == sh2(read_cat(b1, pa), pb - pa),
{
    hide(read_code);
    hide(read_count);
    hide(varlen8);
    lemma_read_cat_pos(b1, pa);
    lemma_varlen8_pos(b1, pa);
    let (v, q) = varlen8(b1, pa).unwrap();
    let fq = pos2(read_cat(b1, pa));
    if v == 0 {
        assert(fq == q);
        lemma_varlen8_mv(b1, pa, b2, pb, nn);
    } else {
        lemma_read_code_pos(b1, q, v + 3);
        let (tcode, q2) = read_code(b1, q, v + 3).unwrap();
        lemma_read_code_pos(b1, q2, 26);
        let (ccode, q3) = read_code(b1, q2, 26).unwrap();
        lemma_read_count_pos(ccode, b1, q3);
        assert(fq == pos2(read_count(ccode, b1, q3)));
        lemma_varlen8_mv(b1, pa, b2, pb, nn);
        lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
        lemma_read_code_mv(b1, q, b2, mv(q, pa, pb), nn - (q - pa), v + 3);
        lemma_same_sub(b1, pa, b2, pb, nn, q2 - pa, nn - (q2 - pa));
        lemma_read_code_mv(b1, q2, b2, mv(q2, pa, pb), nn - (q2 - pa), 26);
        lemma_same_sub(b1, pa, b2, pb, nn, q3 - pa, nn - (q3 - pa));
        lemma_read_count_mv(ccode, b1, q3, b2, mv(q3, pa, pb), nn - (q3 - pa));
    }
}

pub proof fn lemma_read_modes_pos(b: Seq<bool>, p: int, n: nat, acc: Seq<nat>)
    ensures read_modes(b, p, n, acc) matches Some((v, q)) ==> p <= q && (acc.len() <= n ==> q <= p + 2 * (n - acc.len())),
    decreases n - acc.len(),
{
    if acc.len() < n {
        if let Some(m) = getbits(b, p, 2) {
            lemma_read_modes_pos(b, p + 2, n, acc.push(m));
        }
    }
}

pub proof fn lemma_read_modes_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int, n: nat, acc: Seq<nat>)
    requires read_modes(b1, pa, n, acc) is Some, pos2(read_modes(b1, pa, n, acc)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures read_modes(b2, pb, n, acc) == sh2(read_modes(b1, pa, n, acc), pb - pa),
    decreases n - acc.len(),
{
    if acc.len() < n {
        let m = getbits(b1, pa, 2).unwrap();
        lemma_read_modes_pos(b1, pa + 2, n, acc.push(m));
        lemma_getbits_mv(b1, pa, b2, pb, nn, 2);
        lemma_same_sub(b1, pa, b2, pb, nn, 2, nn - 2);
        lemma_read_modes_mv(b1, pa + 2, b2, pb + 2, nn - 2, n, acc.push(m));
    }
}

pub proof fn lemma_read_codes_pos(b: Seq<bool>, p: int, asize: nat, n: nat, acc: Seq<Seq<u8>>)
    ensures read_codes(b, p, asize, n, acc) matches Some((v, q)) ==>
        p <= q && (acc.len() <= n ==> q <= p + (n - acc.len()) * code_bits(asize)),
    decreases n - acc.len(),
{
    if acc.len() < n {
        lemma_read_code_pos(b, p, asize);
        if let Some((c, q)) = read_code(b, p, asize) {
            lemma_read_codes_pos(b, q, asize, n, acc.push(c));
            if let Some((v, r)) = read_codes(b, q, asize, n, acc.push(c)) {
                assert(r <= p + (n - acc.len()) * code_bits(asize)) by (nonlinear_arith)
                    requires r <= q + (n - (acc.len() + 1)) * code_bits(asize), q <= p + code_bits(asize), acc.len() < n;
            }
        }
    }
}

pub proof fn lemma_read_codes_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int, asize: nat, n: nat,
                                 acc: Seq<Seq<u8>>)
    requires read_codes(b1, pa, asize, n, acc) is Some, pos2(read_codes(b1, pa, asize, n, acc)) - pa <= nn,
        same(b1, pa, b2, pb, nn),
    ensures read_codes(b2, pb, asize, n, acc) == sh2(read_codes(b1, pa, asize, n, acc), pb - pa),
    decreases n - acc.len(),
{
    if acc.len() < n {
        lemma_read_code_pos(b1, pa, asize);
        let (c, q) = read_code(b1, pa, asize).unwrap();
        lemma_read_codes_pos(b1, q, asize, n, acc.push(c));
        lemma_read_code_mv(b1, pa, b2, pb, nn, asize);
        lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
        lemma_read_codes_mv(b1, q, b2, mv(q, pa, pb), nn - (q - pa), asize, n, acc.push(c));
    }
}

/// The most bits a compressed meta-block's header takes.
pub open spec fn hdr_bits() -> nat { 7_500_000 }

#[verifier::spinoff_prover]
pub proof fn lemma_read_hdr_pos(b: Seq<bool>, p: int)
    ensures read_hdr(b, p) matches Some((h, q)) ==> p + 3 <= q <= p + hdr_bits(),
{
    hide(read_cat);
    hide(read_modes);
    hide(read_cmap);
    hide(read_codes);
    lemma_read_cat_pos(b, p);
    if let Some((cl, p1)) = read_cat(b, p) {
        lemma_read_cat_pos(b, p1);
        if let Some((ci, p2_)) = read_cat(b, p1) {
            lemma_read_cat_pos(b, p2_);
            if let Some((cd, p3)) = read_cat(b, p2_) {
                if let (Some(npostfix), Some(nd4)) = (getbits(b, p3, 2), getbits(b, p3 + 2, 4)) {
                    lemma_getbits_bound_(b, p3, 2);
                    lemma_getbits_bound_(b, p3 + 2, 4);
                    reveal_with_fuel(p2, 5);
                    vbits::prim_read::lemma_p2_mono(npostfix, 3);
                    let ndirect = nd4 * p2(npostfix);
                    assert(ndirect <= 120) by (nonlinear_arith) requires ndirect == nd4 * p2(npostfix), nd4 < 16, p2(npostfix) <= 8;
                    assert(dist_asize(npostfix, ndirect) <= 520) by (nonlinear_arith)
                        requires ndirect <= 120, p2(npostfix) <= 8, dist_asize(npostfix, ndirect) == 16 + ndirect + 48 * p2(npostfix);
                    lemma_read_modes_pos(b, p3 + 6, cl.n, Seq::empty());
                    if let Some((modes, p4)) = read_modes(b, p3 + 6, cl.n, Seq::empty()) {
                        lemma_read_cmap_pos(b, p4, 64 * cl.n);
                        if let Some((cmapl, ntl, p5)) = read_cmap(b, p4, 64 * cl.n) {
                            lemma_read_cmap_pos(b, p5, 4 * cd.n);
                            if let Some((cmapd, ntd, p6)) = read_cmap(b, p5, 4 * cd.n) {
                                lemma_read_codes_pos(b, p6, 256, ntl, Seq::empty());
                                if let Some((lit, p7)) = read_codes(b, p6, 256, ntl, Seq::empty()) {
                                    lemma_read_codes_pos(b, p7, 704, ci.n, Seq::empty());
                                    if let Some((cmd, p8)) = read_codes(b, p7, 704, ci.n, Seq::empty()) {
                                        let da = dist_asize(npostfix, ndirect);
                                        lemma_read_codes_pos(b, p8, da, ntd, Seq::empty());
                                        if let Some((dist, p9)) = read_codes(b, p8, da, ntd, Seq::empty()) {
                                            assert(ntl * code_bits(256) <= 256 * 4682) by (nonlinear_arith)
                                                requires ntl <= 256, code_bits(256) == 4682;
                                            assert(ci.n * code_bits(704) <= 256 * 12746) by (nonlinear_arith)
                                                requires ci.n <= 256, code_bits(704) == 12746;
                                            assert(ntd * code_bits(da) <= 256 * 9434) by (nonlinear_arith)
                                                requires ntd <= 256, code_bits(da) == 74 + 18 * da, da <= 520;
                                            assert(cmap_bits(64 * cl.n) <= 4987 + 31 * 16384) by (nonlinear_arith)
                                                requires cl.n <= 256, cmap_bits(64 * cl.n) == 4987 + 31 * (64 * cl.n);
                                            assert(cmap_bits(4 * cd.n) <= 4987 + 31 * 1024) by (nonlinear_arith)
                                                requires cd.n <= 256, cmap_bits(4 * cd.n) == 4987 + 31 * (4 * cd.n);
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

#[verifier::spinoff_prover]
pub proof fn lemma_read_hdr_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int)
    requires read_hdr(b1, pa) is Some, pos2(read_hdr(b1, pa)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures read_hdr(b2, pb) == sh2(read_hdr(b1, pa), pb - pa),
{
    hide(read_cat);
    hide(read_modes);
    hide(read_cmap);
    hide(read_codes);
    let (cl, q1) = read_cat(b1, pa).unwrap();
    let (ci, q2) = read_cat(b1, q1).unwrap();
    let (cd, q3) = read_cat(b1, q2).unwrap();
    lemma_read_cat_pos(b1, pa);
    lemma_read_cat_pos(b1, q1);
    lemma_read_cat_pos(b1, q2);
    let npostfix = getbits(b1, q3, 2).unwrap();
    let nd4 = getbits(b1, q3 + 2, 4).unwrap();
    let ndirect = nd4 * p2(npostfix);
    let (modes, q4) = read_modes(b1, q3 + 6, cl.n, Seq::empty()).unwrap();
    lemma_read_modes_pos(b1, q3 + 6, cl.n, Seq::empty());
    let (cmapl, ntl, q5) = read_cmap(b1, q4, 64 * cl.n).unwrap();
    lemma_read_cmap_pos(b1, q4, 64 * cl.n);
    let (cmapd, ntd, q6) = read_cmap(b1, q5, 4 * cd.n).unwrap();
    lemma_read_cmap_pos(b1, q5, 4 * cd.n);
    let (lit, q7) = read_codes(b1, q6, 256, ntl, Seq::empty()).unwrap();
    lemma_read_codes_pos(b1, q6, 256, ntl, Seq::empty());
    let (cmd, q8) = read_codes(b1, q7, 704, ci.n, Seq::empty()).unwrap();
    lemma_read_codes_pos(b1, q7, 704, ci.n, Seq::empty());
    lemma_read_codes_pos(b1, q8, dist_asize(npostfix, ndirect), ntd, Seq::empty());
    lemma_read_cat_mv(b1, pa, b2, pb, nn);
    lemma_same_sub(b1, pa, b2, pb, nn, q1 - pa, nn - (q1 - pa));
    lemma_read_cat_mv(b1, q1, b2, mv(q1, pa, pb), nn - (q1 - pa));
    lemma_same_sub(b1, pa, b2, pb, nn, q2 - pa, nn - (q2 - pa));
    lemma_read_cat_mv(b1, q2, b2, mv(q2, pa, pb), nn - (q2 - pa));
    lemma_same_sub(b1, pa, b2, pb, nn, q3 - pa, nn - (q3 - pa));
    lemma_getbits_mv(b1, q3, b2, mv(q3, pa, pb), nn - (q3 - pa), 2);
    lemma_same_sub(b1, pa, b2, pb, nn, q3 + 2 - pa, nn - (q3 + 2 - pa));
    lemma_getbits_mv(b1, q3 + 2, b2, mv(q3 + 2, pa, pb), nn - (q3 + 2 - pa), 4);
    lemma_same_sub(b1, pa, b2, pb, nn, q3 + 6 - pa, nn - (q3 + 6 - pa));
    lemma_read_modes_mv(b1, q3 + 6, b2, mv(q3 + 6, pa, pb), nn - (q3 + 6 - pa), cl.n, Seq::empty());
    lemma_same_sub(b1, pa, b2, pb, nn, q4 - pa, nn - (q4 - pa));
    lemma_read_cmap_mv(b1, q4, b2, mv(q4, pa, pb), nn - (q4 - pa), 64 * cl.n);
    lemma_same_sub(b1, pa, b2, pb, nn, q5 - pa, nn - (q5 - pa));
    lemma_read_cmap_mv(b1, q5, b2, mv(q5, pa, pb), nn - (q5 - pa), 4 * cd.n);
    lemma_same_sub(b1, pa, b2, pb, nn, q6 - pa, nn - (q6 - pa));
    lemma_read_codes_mv(b1, q6, b2, mv(q6, pa, pb), nn - (q6 - pa), 256, ntl, Seq::empty());
    lemma_same_sub(b1, pa, b2, pb, nn, q7 - pa, nn - (q7 - pa));
    lemma_read_codes_mv(b1, q7, b2, mv(q7, pa, pb), nn - (q7 - pa), 704, ci.n, Seq::empty());
    lemma_same_sub(b1, pa, b2, pb, nn, q8 - pa, nn - (q8 - pa));
    lemma_read_codes_mv(b1, q8, b2, mv(q8, pa, pb), nn - (q8 - pa), dist_asize(npostfix, ndirect), ntd, Seq::empty());
}

// -------------------------------------------------------------- commands

/// What a header read by `read_hdr` has, as far as the bounds below need.
pub open spec fn cat_ok(c: Cat) -> bool {
    1 <= c.n <= 256 && (c.n >= 2 ==> c.tcode.len() == c.n + 2 && c.ccode.len() == 26)
}

pub open spec fn blk_in(k: Blk, c: Cat) -> bool { k.t < c.n && (c.n >= 2 ==> k.prev < c.n) }

pub open spec fn hdr_ok(h: Hdr) -> bool {
    &&& cat_ok(h.cl) && cat_ok(h.ci) && cat_ok(h.cd) && h.npostfix <= 3 && h.ndirect <= 120
    &&& h.cmd.len() == h.ci.n && forall|i: int| 0 <= i < h.cmd.len() ==> (#[trigger] h.cmd[i]).len() == 704
    &&& h.cmapd.len() == 4 * h.cd.n && forall|i: int| 0 <= i < h.cmapd.len() ==> (#[trigger] h.cmapd[i]) < h.dist.len()
    &&& forall|i: int| 0 <= i < h.dist.len() ==> (#[trigger] h.dist[i]).len() == dist_asize(h.npostfix, h.ndirect)
}

pub open spec fn pos_blk(r: Option<(Blk, int)>) -> int { match r { Some((k, q)) => q, None => 0 } }

pub proof fn lemma_next_blk_pos(c: Cat, k: Blk, b: Seq<bool>, p: int)
    ensures
        next_blk(c, k, b, p) matches Some((k2, q)) ==> p <= q <= p + 54,
        next_blk(c, k, b, p) matches Some((k2, q)) ==> (k.left > 0 ==> k2.left == k.left - 1 && q == p && k2.t == k.t),
        next_blk(c, k, b, p) matches Some((k2, q)) ==> (k.left == 0 ==> q >= p + 2),
        next_blk(c, k, b, p) matches Some((k2, q)) ==> (cat_ok(c) && blk_in(k, c) ==> blk_in(k2, c)),
{
    if k.left == 0 && c.n >= 2 {
        lemma_dsym_pos(c.tcode, b, p);
        if let Some((s, q)) = dsym(c.tcode, b, p) {
            lemma_read_count_pos(c.ccode, b, q);
        }
    }
}

pub proof fn lemma_next_blk_mv(c: Cat, k: Blk, b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int)
    requires next_blk(c, k, b1, pa) is Some, pos_blk(next_blk(c, k, b1, pa)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures next_blk(c, k, b2, pb) == sh2(next_blk(c, k, b1, pa), pb - pa),
{
    if k.left == 0 {
        lemma_dsym_pos(c.tcode, b1, pa);
        let (s, q) = dsym(c.tcode, b1, pa).unwrap();
        lemma_read_count_pos(c.ccode, b1, q);
        lemma_dsym_mv(c.tcode, b1, pa, b2, pb, nn);
        lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
        lemma_read_count_mv(c.ccode, b1, q, b2, mv(q, pa, pb), nn - (q - pa));
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_lits_pos(h: Hdr, b: Seq<bool>, p: int, n: nat, out: Seq<u8>, bl: Blk)
    ensures
        lits(h, b, p, n, out, bl) matches Some((o, k, q)) ==> p <= q <= p + 69 * n && o.len() == out.len() + n,
        lits(h, b, p, n, out, bl) matches Some((o, k, q)) ==> (cat_ok(h.cl) && blk_in(bl, h.cl) ==> blk_in(k, h.cl)),
    decreases n,
{
    if n > 0 {
        lemma_next_blk_pos(h.cl, bl, b, p);
        if let Some((bl2, q)) = next_blk(h.cl, bl, b, p) {
            let ctx = lit_ctx(h.modes[bl2.t as int], p1(out), p2b(out));
            let code = h.lit[h.cmapl[(64 * bl2.t + ctx) as int] as int];
            lemma_dsym_pos(code, b, q);
            if let Some((s, r)) = dsym(code, b, q) {
                lemma_lits_pos(h, b, r, (n - 1) as nat, out.push(s as u8), bl2);
            }
        }
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_lits_mv(h: Hdr, b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int, n: nat, out: Seq<u8>, bl: Blk)
    requires lits(h, b1, pa, n, out, bl) is Some, pos3(lits(h, b1, pa, n, out, bl)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures lits(h, b2, pb, n, out, bl) == sh3(lits(h, b1, pa, n, out, bl), pb - pa),
    decreases n,
{
    if n > 0 {
        lemma_next_blk_pos(h.cl, bl, b1, pa);
        let (bl2, q) = next_blk(h.cl, bl, b1, pa).unwrap();
        let ctx = lit_ctx(h.modes[bl2.t as int], p1(out), p2b(out));
        let code = h.lit[h.cmapl[(64 * bl2.t + ctx) as int] as int];
        lemma_dsym_pos(code, b1, q);
        let (s, r) = dsym(code, b1, q).unwrap();
        lemma_lits_pos(h, b1, r, (n - 1) as nat, out.push(s as u8), bl2);
        lemma_next_blk_mv(h.cl, bl, b1, pa, b2, pb, nn);
        lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
        lemma_dsym_mv(code, b1, q, b2, mv(q, pa, pb), nn - (q - pa));
        lemma_same_sub(b1, pa, b2, pb, nn, r - pa, nn - (r - pa));
        lemma_lits_mv(h, b1, r, b2, mv(r, pa, pb), nn - (r - pa), (n - 1) as nat, out.push(s as u8), bl2);
    }
}

pub proof fn lemma_cmd_tables_bound()
    ensures
        forall|i: int| 0 <= i < 24 ==> (#[trigger] ins_extra()[i]) <= 24 && copy_extra()[i] <= 24,
        forall|i: int| 0 <= i < 11 ==> (#[trigger] cell_ins()[i]) <= 16 && cell_copy()[i] <= 16,
{
    assert(forall|i: int| 0 <= i < 24 ==> (#[trigger] ins_extra()[i]) <= 24 && copy_extra()[i] <= 24) by (compute);
    assert(forall|i: int| 0 <= i < 11 ==> (#[trigger] cell_ins()[i]) <= 16 && cell_copy()[i] <= 16) by (compute);
}

pub open spec fn pos5(r: Option<(Blk, nat, nat, nat, int)>) -> int { match r { Some((k, c, i, l, q)) => q, None => 0 } }

pub proof fn lemma_cmd_head_pos(h: Hdr, b: Seq<bool>, p: int, bi: Blk)
    ensures
        cmd_head(h, b, p, bi) matches Some((k, c, il, cl, q)) ==> p <= q,
        cmd_head(h, b, p, bi) matches Some((k, c, il, cl, q)) ==> (hdr_ok(h) && blk_in(bi, h.ci) ==>
            q <= p + 117 && blk_in(k, h.ci)),
{
    lemma_next_blk_pos(h.ci, bi, b, p);
    if let Some((bi2, q)) = next_blk(h.ci, bi, b, p) {
        lemma_dsym_pos(h.cmd[bi2.t as int], b, q);
        if let Some((c, q1)) = dsym(h.cmd[bi2.t as int], b, q) {
            lemma_cmd_tables_bound();
            if hdr_ok(h) && blk_in(bi, h.ci) {
                assert(h.cmd[bi2.t as int].len() == 704);
                assert(c / 64 < 11);
            }
        }
    }
}

pub proof fn lemma_cmd_head_mv(h: Hdr, b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int, bi: Blk)
    requires cmd_head(h, b1, pa, bi) is Some, pos5(cmd_head(h, b1, pa, bi)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures cmd_head(h, b2, pb, bi) == (match cmd_head(h, b1, pa, bi) {
        Some((k, c, il, cl, q)) => Some((k, c, il, cl, mv(q, pa, pb))), None => None }),
{
    lemma_next_blk_pos(h.ci, bi, b1, pa);
    let (bi2, q) = next_blk(h.ci, bi, b1, pa).unwrap();
    lemma_dsym_pos(h.cmd[bi2.t as int], b1, q);
    let (c, q1) = dsym(h.cmd[bi2.t as int], b1, q).unwrap();
    let ic = ins_code(c);
    let cc = copy_code(c);
    let q2 = q1 + ins_extra()[ic as int];
    lemma_next_blk_mv(h.ci, bi, b1, pa, b2, pb, nn);
    lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
    lemma_dsym_mv(h.cmd[bi2.t as int], b1, q, b2, mv(q, pa, pb), nn - (q - pa));
    lemma_same_sub(b1, pa, b2, pb, nn, q1 - pa, nn - (q1 - pa));
    lemma_getbits_mv(b1, q1, b2, mv(q1, pa, pb), nn - (q1 - pa), ins_extra()[ic as int]);
    lemma_same_sub(b1, pa, b2, pb, nn, q2 - pa, nn - (q2 - pa));
    lemma_getbits_mv(b1, q2, b2, mv(q2, pa, pb), nn - (q2 - pa), copy_extra()[cc as int]);
}

pub open spec fn pos_dist(r: Option<(int, bool, Blk, int)>) -> int { match r { Some((d, e, k, q)) => q, None => 0 } }

pub proof fn lemma_read_dist_pos(h: Hdr, ring: Seq<int>, c: nat, clen: nat, b: Seq<bool>, p: int, bd: Blk)
    ensures
        read_dist(h, ring, c, clen, b, p, bd) matches Some((d, e, k, q)) ==> p <= q,
        read_dist(h, ring, c, clen, b, p, bd) matches Some((d, e, k, q)) ==> (hdr_ok(h) && blk_in(bd, h.cd)
            && clen >= 2 ==> q <= p + 93 && blk_in(k, h.cd)),
{
    if c >= 128 {
        lemma_next_blk_pos(h.cd, bd, b, p);
        if let Some((bd2, q)) = next_blk(h.cd, bd, b, p) {
            let tree = h.cmapd[(4 * bd2.t + dist_ctx(clen)) as int];
            lemma_dsym_pos(h.dist[tree as int], b, q);
            if let Some((dc, q2)) = dsym(h.dist[tree as int], b, q) {
                if hdr_ok(h) && blk_in(bd, h.cd) && clen >= 2 && dc >= 16 + h.ndirect {
                    assert(dist_ctx(clen) < 4);
                    assert(h.dist[tree as int].len() == dist_asize(h.npostfix, h.ndirect));
                    reveal_with_fuel(p2, 5);
                    vbits::prim_read::lemma_p2_mono(h.npostfix, 3);
                    vbits::bitspec::lemma_p2_pos(h.npostfix);
                    assert(p2(h.npostfix + 1) == 2 * p2(h.npostfix));
                    let x = (dc - h.ndirect - 16) as nat;
                    assert(x < 48 * p2(h.npostfix));
                    assert(x / p2(h.npostfix + 1) < 24) by {
                        let (xi, pi) = (x as int, p2(h.npostfix) as int);
                        assert(xi / (2 * pi) < 24) by (nonlinear_arith) requires xi < 48 * pi, pi >= 1, xi >= 0;
                    }
                }
            }
        }
    }
}

pub proof fn lemma_read_dist_mv(h: Hdr, ring: Seq<int>, c: nat, clen: nat, b1: Seq<bool>, pa: int, b2: Seq<bool>,
                                pb: int, nn: int, bd: Blk)
    requires read_dist(h, ring, c, clen, b1, pa, bd) is Some, pos_dist(read_dist(h, ring, c, clen, b1, pa, bd)) - pa <= nn,
        same(b1, pa, b2, pb, nn),
    ensures read_dist(h, ring, c, clen, b2, pb, bd) == (match read_dist(h, ring, c, clen, b1, pa, bd) {
        Some((d, e, k, q)) => Some((d, e, k, mv(q, pa, pb))), None => None }),
{
    if c >= 128 {
        lemma_next_blk_pos(h.cd, bd, b1, pa);
        let (bd2, q) = next_blk(h.cd, bd, b1, pa).unwrap();
        let tree = h.cmapd[(4 * bd2.t + dist_ctx(clen)) as int];
        lemma_dsym_pos(h.dist[tree as int], b1, q);
        let (dc, q2) = dsym(h.dist[tree as int], b1, q).unwrap();
        lemma_next_blk_mv(h.cd, bd, b1, pa, b2, pb, nn);
        lemma_same_sub(b1, pa, b2, pb, nn, q - pa, nn - (q - pa));
        lemma_dsym_mv(h.dist[tree as int], b1, q, b2, mv(q, pa, pb), nn - (q - pa));
        if dc >= 16 + h.ndirect {
            let nb = dist_nbits(h.npostfix, h.ndirect, dc);
            lemma_same_sub(b1, pa, b2, pb, nn, q2 - pa, nn - (q2 - pa));
            lemma_getbits_mv(b1, q2, b2, mv(q2, pa, pb), nn - (q2 - pa), nb);
        }
    }
}

pub proof fn lemma_cmd_tail_mv(dict: Seq<u8>, window: nat, h: Hdr, b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int,
                               nn: int, end: nat, st: St, c: nat, clen: nat, bd: Blk)
    requires cmd_tail(dict, window, h, b1, pa, end, st, c, clen, bd) is Some,
        pos3(cmd_tail(dict, window, h, b1, pa, end, st, c, clen, bd)) - pa <= nn, same(b1, pa, b2, pb, nn),
    ensures cmd_tail(dict, window, h, b2, pb, end, st, c, clen, bd)
        == sh3(cmd_tail(dict, window, h, b1, pa, end, st, c, clen, bd), pb - pa),
{
    lemma_read_dist_mv(h, st.ring, c, clen, b1, pa, b2, pb, nn, bd);
}

/// A command's head uses up one of its block's commands, or reads a block
/// switch.
pub proof fn lemma_cmd_head_blk(h: Hdr, b: Seq<bool>, p: int, bi: Blk)
    ensures cmd_head(h, b, p, bi) matches Some((bi2, c, il, cl, q3)) ==>
        (bi.left > 0 ==> bi2.left == bi.left - 1) && (bi.left == 0 ==> q3 >= p + 2) && q3 >= p,
{
    lemma_next_blk_pos(h.ci, bi, b, p);
    if let Some((bi2, q)) = next_blk(h.ci, bi, b, p) {
        lemma_dsym_pos(h.cmd[bi2.t as int], b, q);
    }
}

} // verus!
