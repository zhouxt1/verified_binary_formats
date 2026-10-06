//! The spec decoder in steps, for decoding a stream that arrives in pieces.
//!
//! A step is a symbol of a compressed block (with a length's extra bits,
//! its distance and their extra bits), a block header, a dynamic header, or
//! a stored block's header. Two facts about each make streaming work:
//!
//! * a step's result depends only on the bits it reads (`*_agree`): so a
//!   step decoded from the input so far is the step of every stream that
//!   starts with that input;
//! * a step reads a bounded number of bits (`*_bound`): so a step that fails
//!   with that many bits available fails for every such stream, and a
//!   decoder can say the input is bad without seeing more of it.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
use crate::spec::*;
use crate::huff::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::inflate::len_dist;

verus! {

/// `b1` and `b2` both have bits `lo..hi`, and they are the same.
pub open spec fn agree(b1: Seq<bool>, b2: Seq<bool>, lo: int, hi: int) -> bool {
    &&& 0 <= lo <= hi
    &&& hi <= b1.len() && hi <= b2.len()
    &&& forall|i: int| lo <= i < hi ==> #[trigger] b1[i] == b2[i]
}

/// `b1` is a prefix of `b2`.
pub open spec fn is_prefix(b1: Seq<bool>, b2: Seq<bool>) -> bool {
    b1.len() <= b2.len() && forall|i: int| 0 <= i < b1.len() ==> #[trigger] b1[i] == b2[i]
}

pub proof fn lemma_prefix_agree(b1: Seq<bool>, b2: Seq<bool>, lo: int, hi: int)
    requires is_prefix(b1, b2), 0 <= lo <= hi <= b1.len(),
    ensures agree(b1, b2, lo, hi), agree(b2, b1, lo, hi),
{
}

pub proof fn lemma_agree_sub(b1: Seq<bool>, b2: Seq<bool>, lo: int, hi: int, lo2: int, hi2: int)
    requires agree(b1, b2, lo, hi), lo <= lo2 <= hi2 <= hi,
    ensures agree(b1, b2, lo2, hi2),
{
}

// ---------------------------------------------------------------- fields

pub proof fn lemma_getbits_agree(b1: Seq<bool>, b2: Seq<bool>, p: int, n: nat)
    requires getbits(b2, p, n) is Some, agree(b1, b2, p, p + n),
    ensures getbits(b1, p, n) == getbits(b2, p, n),
{
    assert(b1.subrange(p, p + n) =~= b2.subrange(p, p + n)) by {
        assert forall|i: int| 0 <= i < n implies #[trigger] b1.subrange(p, p + n)[i] == b2.subrange(p, p + n)[i] by {
            assert(b1[p + i] == b2[p + i]);
        }
    }
}

pub proof fn lemma_decode_sym_agree(lens: Seq<u8>, b1: Seq<bool>, b2: Seq<bool>, p: int)
    requires decode_sym(lens, b2, p) is Some, agree(b1, b2, p, decode_sym(lens, b2, p).unwrap().1),
    ensures decode_sym(lens, b1, p) == decode_sym(lens, b2, p),
{
    let (s, q) = decode_sym(lens, b2, p).unwrap();
    lemma_find_sym_adv(lens, b2, p, 1);
    assert forall|j: int| 0 <= j < q - p implies #[trigger] b1[p + j] == b2[p + j] by {
        assert(b1[p + j] == b2[p + j]);
    }
    lemma_find_sym_agree(lens, b1, p, b2, p, 1, s, (q - p) as nat);
}

/// What follows a length symbol reads at most 5 + 15 + 13 bits.
pub proof fn lemma_len_dist_agree(dl: Seq<u8>, b1: Seq<bool>, b2: Seq<bool>, p1: int, s: nat)
    requires
        257 <= s <= 285, 0 <= p1,
        len_dist(dl, b2, p1, s) is Some,
        agree(b1, b2, p1, len_dist(dl, b2, p1, s).unwrap().2),
    ensures
        len_dist(dl, b1, p1, s) == len_dist(dl, b2, p1, s),
        p1 < len_dist(dl, b2, p1, s).unwrap().2 <= p1 + 33,
{
    let lx = len_extra(s);
    let q2 = p1 + lx;
    let (ds, p3) = decode_sym(dl, b2, q2).unwrap();
    let p4 = len_dist(dl, b2, p1, s).unwrap().2;
    lemma_len_dist_pos(dl, b2, p1, s);
    lemma_find_sym_adv(dl, b2, q2, 1);
    assert(lx <= 5);
    assert(p3 <= q2 + 15) by { lemma_find_sym_len(dl, b2, q2, 1); }
    assert(dist_extra(ds) <= 13);
    lemma_agree_sub(b1, b2, p1, p4, p1, p1 + lx);
    lemma_getbits_agree(b1, b2, p1, lx);
    lemma_agree_sub(b1, b2, p1, p4, q2, p3);
    lemma_decode_sym_agree(dl, b1, b2, q2);
    lemma_agree_sub(b1, b2, p1, p4, p3, p4);
    lemma_getbits_agree(b1, b2, p3, dist_extra(ds));
}

/// What follows a length symbol is at least one bit and at most 33.
pub proof fn lemma_len_dist_pos(dl: Seq<u8>, b: Seq<bool>, p1: int, s: nat)
    requires 257 <= s <= 285, 0 <= p1, len_dist(dl, b, p1, s) is Some,
    ensures p1 < len_dist(dl, b, p1, s).unwrap().2 <= p1 + 33,
{
    let q2 = p1 + len_extra(s);
    lemma_find_sym_adv(dl, b, q2, 1);
    lemma_find_sym_len(dl, b, q2, 1);
}

/// A code is at most 15 bits.
pub proof fn lemma_find_sym_len(lens: Seq<u8>, b: Seq<bool>, p: int, l: nat)
    ensures find_sym(lens, b, p, l) matches Some((s, q)) ==> q <= p + 15,
    decreases 16 - l,
{
    if !(l == 0 || l > maxbits() || p < 0 || p + l > b.len()) {
        lemma_find_sym_len(lens, b, p, l + 1);
    }
}

// ------------------------------------------------------ a symbol's step

pub enum Step {
    /// A literal, and the position after it.
    Lit(u8, int),
    /// End of block, and the position after it.
    End(int),
    /// A copy: its length, its distance, and the position after it.
    Copy(nat, nat, int),
}

pub open spec fn step_end(st: Step) -> int {
    match st {
        Step::Lit(_, q) => q,
        Step::End(q) => q,
        Step::Copy(_, _, q) => q,
    }
}

/// One step of a compressed block at `p`.
pub open spec fn sym_step(ll: Seq<u8>, dl: Seq<u8>, b: Seq<bool>, p: int) -> Option<Step> {
    match decode_sym(ll, b, p) {
        None => None,
        Some((s, p1)) =>
            if p1 <= p || p1 > b.len() {
                None
            } else if s < 256 {
                Some(Step::Lit(s as u8, p1))
            } else if s == 256 {
                Some(Step::End(p1))
            } else if s > 285 {
                None
            } else {
                match len_dist(dl, b, p1, s) {
                    None => None,
                    Some((len, d, p4)) =>
                        if p4 <= p || p4 > b.len() { None } else { Some(Step::Copy(len, d, p4)) },
                }
            },
    }
}

/// The symbols of a block, one step at a time.
pub proof fn lemma_syms_unfold(ll: Seq<u8>, dl: Seq<u8>, b: Seq<bool>, p: int, out: Seq<u8>)
    ensures
        inflate_syms(ll, dl, b, p, out) == match sym_step(ll, dl, b, p) {
            None => None,
            Some(Step::Lit(x, p1)) => inflate_syms(ll, dl, b, p1, out.push(x)),
            Some(Step::End(p1)) => Some((out, p1)),
            Some(Step::Copy(len, d, p4)) =>
                if d > out.len() { None } else { inflate_syms(ll, dl, b, p4, lz_copy(out, d, len)) },
        },
{
    match decode_sym(ll, b, p) {
        None => {}
        Some((s, p1)) => {
            if !(p1 <= p || p1 > b.len()) && 257 <= s <= 285 {
                match getbits(b, p1, len_extra(s)) {
                    None => {}
                    Some(e) => {
                        let q2 = p1 + len_extra(s);
                        match decode_sym(dl, b, q2) {
                            None => {}
                            Some((ds, p3)) => {}
                        }
                    }
                }
            }
        }
    }
}

/// A step depends only on the bits it reads, and reads at most 48.
pub proof fn lemma_sym_step_agree(ll: Seq<u8>, dl: Seq<u8>, b1: Seq<bool>, b2: Seq<bool>, p: int)
    requires 0 <= p, sym_step(ll, dl, b2, p) is Some, agree(b1, b2, p, step_end(sym_step(ll, dl, b2, p).unwrap())),
    ensures
        sym_step(ll, dl, b1, p) == sym_step(ll, dl, b2, p),
        p < step_end(sym_step(ll, dl, b2, p).unwrap()) <= p + 48,
{
    let (s, p1) = decode_sym(ll, b2, p).unwrap();
    let e = step_end(sym_step(ll, dl, b2, p).unwrap());
    lemma_find_sym_adv(ll, b2, p, 1);
    lemma_find_sym_len(ll, b2, p, 1);
    if 257 <= s <= 285 {
        lemma_len_dist_pos(dl, b2, p1, s);
        assert(e == len_dist(dl, b2, p1, s).unwrap().2);
    }
    assert(p1 <= e);
    lemma_agree_sub(b1, b2, p, e, p, p1);
    lemma_decode_sym_agree(ll, b1, b2, p);
    if 257 <= s <= 285 {
        lemma_agree_sub(b1, b2, p, e, p1, e);
        lemma_len_dist_agree(dl, b1, b2, p1, s);
    }
}

pub proof fn lemma_sym_step_bound(ll: Seq<u8>, dl: Seq<u8>, b: Seq<bool>, p: int)
    requires 0 <= p, sym_step(ll, dl, b, p) is Some,
    ensures p < step_end(sym_step(ll, dl, b, p).unwrap()) <= p + 48,
{
    lemma_sym_step_agree(ll, dl, b, b, p);
}

// ------------------------------------------------------- stored blocks

/// Where a stored block's LEN is: `p` rounded up to a byte.
pub open spec fn align8(p: int) -> int {
    if p % 8 == 0 { p } else { p + (8 - p % 8) }
}

/// A stored block's header from `p`: LEN, and where its bytes start.
pub open spec fn stored_hdr(b: Seq<bool>, p: int) -> Option<(nat, int)> {
    let q = align8(p);
    match (getbits(b, q, 16), getbits(b, q + 16, 16)) {
        (Some(len), Some(nlen)) => if len + nlen != 65535 { None } else { Some((len, q + 32)) },
        _ => None,
    }
}

/// `m` bytes from bit `a`.
pub open spec fn bytes_at(b: Seq<bool>, a: int, m: nat) -> Seq<u8> {
    Seq::new(m, |j: int| vbits::lsb::lval(b.subrange(a + 8 * j, a + 8 * j + 8)) as u8)
}

pub proof fn lemma_stored_unfold(b: Seq<bool>, p: int)
    ensures stored(b, p) == match stored_hdr(b, p) {
        None => None,
        Some((len, q0)) => if q0 + 8 * len > b.len() { None } else { Some((bytes_at(b, q0, len), q0 + 8 * len)) },
    },
{
    match stored_hdr(b, p) {
        None => {}
        Some((len, q0)) => {
            if q0 + 8 * len <= b.len() {
                assert(bytes_at(b, q0, len) =~= Seq::new(len, |j: int|
                    vbits::lsb::lval(b.subrange(align8(p) + 32 + 8 * j, align8(p) + 40 + 8 * j)) as u8));
            }
        }
    }
}

pub proof fn lemma_stored_hdr_agree(b1: Seq<bool>, b2: Seq<bool>, p: int)
    requires 0 <= p, stored_hdr(b2, p) is Some, agree(b1, b2, p, stored_hdr(b2, p).unwrap().1),
    ensures
        stored_hdr(b1, p) == stored_hdr(b2, p),
        p < stored_hdr(b2, p).unwrap().1 <= p + 39,
{
    let q = align8(p);
    lemma_agree_sub(b1, b2, p, q + 32, q, q + 16);
    lemma_getbits_agree(b1, b2, q, 16);
    lemma_agree_sub(b1, b2, p, q + 32, q + 16, q + 32);
    lemma_getbits_agree(b1, b2, q + 16, 16);
}

/// A stored block's header ends at most 39 bits on.
pub proof fn lemma_stored_hdr_bound(b: Seq<bool>, p: int)
    requires 0 <= p, stored_hdr(b, p) is Some,
    ensures p < stored_hdr(b, p).unwrap().1 <= p + 39,
{
}

pub proof fn lemma_bytes_agree(b1: Seq<bool>, b2: Seq<bool>, a: int, m: nat)
    requires agree(b1, b2, a, a + 8 * m),
    ensures bytes_at(b1, a, m) == bytes_at(b2, a, m),
{
    assert forall|j: int| 0 <= j < m implies #[trigger] bytes_at(b1, a, m)[j] == bytes_at(b2, a, m)[j] by {
        assert(b1.subrange(a + 8 * j, a + 8 * j + 8) =~= b2.subrange(a + 8 * j, a + 8 * j + 8)) by {
            assert forall|i: int| 0 <= i < 8 implies
                #[trigger] b1.subrange(a + 8 * j, a + 8 * j + 8)[i] == b2.subrange(a + 8 * j, a + 8 * j + 8)[i] by {
                assert(a + 8 * j + i < a + 8 * m) by (nonlinear_arith) requires 0 <= j < m, 0 <= i < 8;
                assert(b1[a + 8 * j + i] == b2[a + 8 * j + i]);
            }
        }
    }
    assert(bytes_at(b1, a, m) =~= bytes_at(b2, a, m));
}

pub proof fn lemma_bytes_split(b: Seq<bool>, a: int, m: nat, k: nat)
    requires k <= m,
    ensures bytes_at(b, a, m) == bytes_at(b, a, k) + bytes_at(b, a + 8 * k, (m - k) as nat),
{
    assert forall|j: int| 0 <= j < m implies #[trigger] bytes_at(b, a, m)[j]
        == (bytes_at(b, a, k) + bytes_at(b, a + 8 * k, (m - k) as nat))[j] by {
        if j >= k {
            assert(a + 8 * k + 8 * (j - k) == a + 8 * j);
        }
    }
    assert(bytes_at(b, a, m) =~= bytes_at(b, a, k) + bytes_at(b, a + 8 * k, (m - k) as nat));
}

// ------------------------------------------------------ dynamic headers

pub proof fn lemma_read_cl_pos(b: Seq<bool>, p: int, hclen: nat, i: nat, acc: Seq<u8>)
    requires 0 <= p, read_cl(b, p, hclen, i, acc) is Some,
    ensures
        read_cl(b, p, hclen, i, acc).unwrap().1 == p + 3 * (if i < hclen { hclen - i } else { 0 }),
        read_cl(b, p, hclen, i, acc).unwrap().1 <= b.len() || i >= hclen,
    decreases hclen - i,
{
    if i < hclen {
        let v = getbits(b, p, 3).unwrap();
        let acc2 = acc.update(cl_order(i) as int, v as u8);
        lemma_read_cl_pos(b, p + 3, hclen, i + 1, acc2);
    }
}

pub proof fn lemma_read_cl_agree(b1: Seq<bool>, b2: Seq<bool>, p: int, hclen: nat, i: nat, acc: Seq<u8>)
    requires 0 <= p, read_cl(b2, p, hclen, i, acc) is Some,
        agree(b1, b2, p, read_cl(b2, p, hclen, i, acc).unwrap().1),
    ensures read_cl(b1, p, hclen, i, acc) == read_cl(b2, p, hclen, i, acc),
    decreases hclen - i,
{
    if i < hclen {
        let r = read_cl(b2, p, hclen, i, acc).unwrap().1;
        let v = getbits(b2, p, 3).unwrap();
        let acc2 = acc.update(cl_order(i) as int, v as u8);
        lemma_read_cl_pos(b2, p + 3, hclen, i + 1, acc2);
        lemma_agree_sub(b1, b2, p, r, p, p + 3);
        lemma_getbits_agree(b1, b2, p, 3);
        lemma_agree_sub(b1, b2, p, r, p + 3, r);
        lemma_read_cl_agree(b1, b2, p + 3, hclen, i + 1, acc2);
    }
}

pub proof fn lemma_read_lens_pos(cl: Seq<u8>, b: Seq<bool>, p: int, total: nat, acc: Seq<u8>)
    requires 0 <= p, read_lens(cl, b, p, total, acc) is Some,
    ensures
        p <= read_lens(cl, b, p, total, acc).unwrap().1
            <= p + 22 * (if acc.len() < total { total - acc.len() } else { 0 }),
        acc.len() < total ==> read_lens(cl, b, p, total, acc).unwrap().1 <= b.len(),
    decreases total - acc.len(),
{
    if acc.len() < total {
        let (s, p1) = decode_sym(cl, b, p).unwrap();
        lemma_find_sym_adv(cl, b, p, 1);
        lemma_find_sym_len(cl, b, p, 1);
        if s < 16 {
            lemma_read_lens_pos(cl, b, p1, total, acc.push(s as u8));
        } else {
            let (nb, base) = if s == 16 { (2nat, 3nat) } else if s == 17 { (3nat, 3nat) } else { (7nat, 11nat) };
            let e = getbits(b, p1, nb).unwrap();
            let rep = base + e;
            let v: u8 = if s == 16 { acc.last() } else { 0u8 };
            let acc2 = acc + Seq::new(rep, |_i: int| v);
            lemma_read_lens_pos(cl, b, p1 + nb, total, acc2);
            assert(acc2.len() >= acc.len() + 1);
        }
    }
}

pub proof fn lemma_read_lens_agree(cl: Seq<u8>, b1: Seq<bool>, b2: Seq<bool>, p: int, total: nat, acc: Seq<u8>)
    requires 0 <= p, read_lens(cl, b2, p, total, acc) is Some,
        agree(b1, b2, p, read_lens(cl, b2, p, total, acc).unwrap().1),
    ensures read_lens(cl, b1, p, total, acc) == read_lens(cl, b2, p, total, acc),
    decreases total - acc.len(),
{
    let r = read_lens(cl, b2, p, total, acc).unwrap().1;
    if acc.len() < total {
        let (s, p1) = decode_sym(cl, b2, p).unwrap();
        lemma_find_sym_adv(cl, b2, p, 1);
        if s < 16 {
            let acc2 = acc.push(s as u8);
            lemma_read_lens_pos(cl, b2, p1, total, acc2);
            lemma_agree_sub(b1, b2, p, r, p, p1);
            lemma_decode_sym_agree(cl, b1, b2, p);
            lemma_agree_sub(b1, b2, p, r, p1, r);
            lemma_read_lens_agree(cl, b1, b2, p1, total, acc2);
        } else {
            let (nb, base) = if s == 16 { (2nat, 3nat) } else if s == 17 { (3nat, 3nat) } else { (7nat, 11nat) };
            let e = getbits(b2, p1, nb).unwrap();
            let rep = base + e;
            let v: u8 = if s == 16 { acc.last() } else { 0u8 };
            let acc2 = acc + Seq::new(rep, |_i: int| v);
            lemma_read_lens_pos(cl, b2, p1 + nb, total, acc2);
            lemma_agree_sub(b1, b2, p, r, p, p1);
            lemma_decode_sym_agree(cl, b1, b2, p);
            lemma_agree_sub(b1, b2, p, r, p1, p1 + nb);
            lemma_getbits_agree(b1, b2, p1, nb);
            lemma_agree_sub(b1, b2, p, r, p1 + nb, r);
            lemma_read_lens_agree(cl, b1, b2, p1 + nb, total, acc2);
        }
    }
}

/// The largest a dynamic block's header can be, in bits: 14 + 19 * 3, and
/// at most 318 code lengths of at most 15 + 7 bits each.
pub open spec fn dyn_bound() -> nat { 7100 }

pub proof fn lemma_dyn_header_pos(b: Seq<bool>, p: int)
    requires 0 <= p, dyn_header(b, p) is Some,
    ensures p < dyn_header(b, p).unwrap().2 <= p + dyn_bound(), dyn_header(b, p).unwrap().2 <= b.len(),
{
    let hlit = getbits(b, p, 5).unwrap();
    let hdist = getbits(b, p + 5, 5).unwrap();
    let hclen = getbits(b, p + 10, 4).unwrap();
    lemma_lval_bits_bound(b, p + 5, 5);
    lemma_lval_bits_bound(b, p + 10, 4);
    assert(p2(5) == 32 && p2(4) == 16) by { reveal_with_fuel(p2, 6); }
    let (cl, q) = read_cl(b, p + 14, hclen + 4, 0, Seq::new(19, |_i: int| 0u8)).unwrap();
    lemma_read_cl_pos(b, p + 14, hclen + 4, 0, Seq::new(19, |_i: int| 0u8));
    lemma_read_lens_pos(cl, b, q, hlit + 257 + hdist + 1, Seq::empty());
}

pub proof fn lemma_dyn_header_agree(b1: Seq<bool>, b2: Seq<bool>, p: int)
    requires 0 <= p, dyn_header(b2, p) is Some, agree(b1, b2, p, dyn_header(b2, p).unwrap().2),
    ensures dyn_header(b1, p) == dyn_header(b2, p),
{
    let r = dyn_header(b2, p).unwrap().2;
    let hlit = getbits(b2, p, 5).unwrap();
    let hdist = getbits(b2, p + 5, 5).unwrap();
    let hclen = getbits(b2, p + 10, 4).unwrap();
    let nlit = hlit + 257;
    let ndist = hdist + 1;
    let (cl, q) = read_cl(b2, p + 14, hclen + 4, 0, Seq::new(19, |_i: int| 0u8)).unwrap();
    lemma_read_cl_pos(b2, p + 14, hclen + 4, 0, Seq::new(19, |_i: int| 0u8));
    lemma_read_lens_pos(cl, b2, q, nlit + ndist, Seq::empty());
    lemma_agree_sub(b1, b2, p, r, p, p + 5);
    lemma_getbits_agree(b1, b2, p, 5);
    lemma_agree_sub(b1, b2, p, r, p + 5, p + 10);
    lemma_getbits_agree(b1, b2, p + 5, 5);
    lemma_agree_sub(b1, b2, p, r, p + 10, p + 14);
    lemma_getbits_agree(b1, b2, p + 10, 4);
    lemma_agree_sub(b1, b2, p, r, p + 14, q);
    lemma_read_cl_agree(b1, b2, p + 14, hclen + 4, 0, Seq::new(19, |_i: int| 0u8));
    lemma_agree_sub(b1, b2, p, r, q, r);
    lemma_read_lens_agree(cl, b1, b2, q, nlit + ndist, Seq::empty());
}

proof fn lemma_lval_bits_bound(b: Seq<bool>, p: int, n: nat)
    requires getbits(b, p, n) is Some,
    ensures getbits(b, p, n).unwrap() < p2(n),
{
    vbits::lsb::lemma_lval_bound(b.subrange(p, p + n));
}

} // verus!

verus! {

// ------------------------------------------------ the last 32K of output

/// `w` is the end of `g`, and all of it or at least the 32768 bytes a
/// distance can reach back.
pub open spec fn win_of(w: Seq<u8>, g: Seq<u8>) -> bool {
    &&& w.len() <= g.len()
    &&& g.skip(g.len() - w.len()) == w
    &&& (w.len() >= 32768 || w.len() == g.len())
}

/// A distance is at most 32768.
pub proof fn lemma_len_dist_d(dl: Seq<u8>, b: Seq<bool>, p1: int, s: nat)
    requires 257 <= s <= 285, len_dist(dl, b, p1, s) is Some,
    ensures 1 <= len_dist(dl, b, p1, s).unwrap().1 <= 32768, len_dist(dl, b, p1, s).unwrap().0 <= 258,
{
    let lx = len_extra(s);
    let q2 = p1 + lx;
    let e = getbits(b, p1, lx).unwrap();
    let (ds, p3) = decode_sym(dl, b, q2).unwrap();
    let e2 = getbits(b, p3, dist_extra(ds)).unwrap();
    vbits::lsb::lemma_lval_bound(b.subrange(p1, p1 + lx));
    vbits::lsb::lemma_lval_bound(b.subrange(p3, p3 + dist_extra(ds)));
    reveal_with_fuel(p2, 14);
    assert(p2(13) == 8192 && p2(12) == 4096 && p2(11) == 2048 && p2(10) == 1024 && p2(9) == 512
        && p2(8) == 256 && p2(7) == 128 && p2(6) == 64 && p2(5) == 32 && p2(4) == 16 && p2(3) == 8
        && p2(2) == 4 && p2(1) == 2 && p2(0) == 1);
    assert(ds <= 29);
    assert(dist_base(ds) + e2 <= 32768) by {
        if ds >= 4 {
            let k = ((ds / 2) - 1) as nat;
            assert(k <= 13);
            assert(dist_base(ds) == p2(k) * (2 + ds % 2) + 1);
            assert(e2 < p2(k));
            assert(p2(k) * (2 + ds % 2) + 1 + e2 <= p2(k) * 4) by (nonlinear_arith)
                requires e2 < p2(k), ds % 2 <= 1, p2(k) >= 1;
            vbits::prim_read::lemma_p2_mono(k, 13);
        }
    }
}

/// Appending to a window of the output appends the same to the output.
pub proof fn lemma_lz_copy_win(w: Seq<u8>, g: Seq<u8>, d: nat, len: nat)
    requires win_of(w, g), 1 <= d <= w.len(),
    ensures
        lz_copy(g, d, len) == g.take(g.len() - w.len()) + lz_copy(w, d, len),
        win_of(lz_copy(w, d, len), lz_copy(g, d, len)),
    decreases len,
{
    let k = g.len() - w.len();
    assert(g =~= g.take(k) + w) by { assert(g.skip(k) == w); }
    if len > 0 {
        let x = w[w.len() - d];
        assert(g[g.len() - d] == x) by {
            assert(g.skip(k)[w.len() - d] == g[k + w.len() - d]);
        }
        let g1 = g.push(g[g.len() - d]);
        let w1 = w.push(x);
        assert(g1 =~= g.take(k) + w1);
        assert(win_of(w1, g1)) by {
            assert(g1.skip(g1.len() - w1.len()) =~= w1);
        }
        lemma_lz_copy_win(w1, g1, d, (len - 1) as nat);
        assert(g1.take(g1.len() - w1.len()) =~= g.take(k));
    } else {
        assert(g.take(k) + w =~= g);
    }
}

/// A block decodes the same from a window of the output as from all of it.
pub proof fn lemma_syms_win(ll: Seq<u8>, dl: Seq<u8>, f: Seq<bool>, p: int, w: Seq<u8>, g: Seq<u8>)
    requires win_of(w, g),
    ensures
        inflate_syms(ll, dl, f, p, g) == match inflate_syms(ll, dl, f, p, w) {
            None => None,
            Some((o, q)) => Some((g.take(g.len() - w.len()) + o, q)),
        },
        inflate_syms(ll, dl, f, p, w) matches Some((o, q)) ==> win_of(o, g.take(g.len() - w.len()) + o),
    decreases f.len() - p,
{
    let k = g.len() - w.len();
    lemma_syms_unfold(ll, dl, f, p, g);
    lemma_syms_unfold(ll, dl, f, p, w);
    assert(g =~= g.take(k) + w) by { assert(g.skip(k) == w); }
    match sym_step(ll, dl, f, p) {
        None => {}
        Some(Step::Lit(x, p1)) => {
            let g1 = g.push(x);
            let w1 = w.push(x);
            assert(g1 =~= g.take(k) + w1);
            assert(win_of(w1, g1)) by { assert(g1.skip(g1.len() - w1.len()) =~= w1); }
            lemma_sym_step_bound(ll, dl, f, p);
            lemma_syms_win(ll, dl, f, p1, w1, g1);
            assert(g1.take(g1.len() - w1.len()) =~= g.take(k));
        }
        Some(Step::End(p1)) => {
            assert(g.take(k) + w =~= g);
        }
        Some(Step::Copy(len, d, p4)) => {
            let (s, p1) = decode_sym(ll, f, p).unwrap();
            lemma_len_dist_d(dl, f, p1, s);
            if d <= w.len() {
                lemma_lz_copy_win(w, g, d, len);
                let g1 = lz_copy(g, d, len);
                let w1 = lz_copy(w, d, len);
                crate::inflate::lemma_lz_copy(w, d, len);
                lemma_sym_step_bound(ll, dl, f, p);
                lemma_syms_win(ll, dl, f, p4, w1, g1);
                assert(g1.len() - w1.len() == k);
                assert(g1.take(k) =~= g.take(k)) by {
                    assert(g1 =~= g.take(k) + w1);
                }
            }
        }
    }
}

} // verus!

verus! {

pub open spec fn lift(pre: Seq<u8>, r: Option<(Seq<u8>, int, bool)>) -> Option<(Seq<u8>, int, bool)> {
    match r { None => None, Some((o, q, s)) => Some((pre + o, q, s)) }
}

pub proof fn lemma_win_append(w: Seq<u8>, g: Seq<u8>, x: Seq<u8>)
    requires win_of(w, g),
    ensures win_of(w + x, g + x), (g + x).take((g + x).len() - (w + x).len()) == g.take(g.len() - w.len()),
{
    let k = g.len() - w.len();
    assert(g =~= g.take(k) + w) by { assert(g.skip(k) == w); }
    assert((g + x).skip(k) =~= w + x);
    assert((g + x).take(k) =~= g.take(k));
}

/// The rest of the stream decodes the same from a window of the output.
pub proof fn lemma_blocks_win(f: Seq<bool>, p: int, w: Seq<u8>, g: Seq<u8>, st: bool)
    requires win_of(w, g),
    ensures inflate_blocks(f, p, g, st) == lift(g.take(g.len() - w.len()), inflate_blocks(f, p, w, st)),
    decreases f.len() - p,
{
    let pre = g.take(g.len() - w.len());
    assert(g =~= pre + w) by { assert(g.skip(g.len() - w.len()) == w); }
    match (getbits(f, p, 1), getbits(f, p + 1, 2)) {
        (Some(bfinal), Some(btype)) => {
            // the block, both ways
            if btype == 0 {
                match stored(f, p + 3) {
                    None => {}
                    Some((bytes, q)) => {
                        lemma_win_append(w, g, bytes);
                        assert(g + bytes =~= pre + (w + bytes));
                        if bfinal != 1 && !(q <= p || q > f.len()) {
                            lemma_blocks_win(f, q, w + bytes, g + bytes, st && true);
                        }
                    }
                }
            } else if btype == 1 {
                lemma_syms_win(fixed_lit(), fixed_dist(), f, p + 3, w, g);
                match inflate_syms(fixed_lit(), fixed_dist(), f, p + 3, w) {
                    None => {}
                    Some((o, q)) => {
                        assert((pre + o).take((pre + o).len() - o.len()) =~= pre);
                        if bfinal != 1 && !(q <= p || q > f.len()) {
                            lemma_blocks_win(f, q, o, pre + o, st && true);
                        }
                    }
                }
            } else if btype == 2 {
                match dyn_header(f, p + 3) {
                    None => {}
                    Some((lit, dist, q, bst)) => {
                        lemma_syms_win(lit, dist, f, q, w, g);
                        match inflate_syms(lit, dist, f, q, w) {
                            None => {}
                            Some((o, r)) => {
                                assert((pre + o).take((pre + o).len() - o.len()) =~= pre);
                                if bfinal != 1 && !(r <= p || r > f.len()) {
                                    lemma_blocks_win(f, r, o, pre + o, st && bst);
                                }
                            }
                        }
                    }
                }
            }
        }
        _ => {}
    }
}

} // verus!
