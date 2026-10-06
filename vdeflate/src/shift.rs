//! Dropping input that has been decoded: decoding from bit `p` of `b` is
//! decoding from bit `p - k` of `b.skip(k)`, positions moved by `k`, for `k`
//! a whole number of bytes (a stored block aligns to the stream's bytes).
use vstd::prelude::*;
use crate::spec::*;
use crate::step::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::inflate::len_dist;

verus! {

pub open spec fn shift_ok(b: Seq<bool>, k: int, p: int) -> bool {
    0 <= k <= p && k <= b.len() && k % 8 == 0
}

pub proof fn lemma_getbits_shift(b: Seq<bool>, k: int, p: int, n: nat)
    requires shift_ok(b, k, p),
    ensures getbits(b, p, n) == getbits(b.skip(k), p - k, n),
{
    if p + n <= b.len() {
        assert(b.subrange(p, p + n) =~= b.skip(k).subrange(p - k, p - k + n));
    }
}

proof fn lemma_find_n_shift(lens: Seq<u8>, b: Seq<bool>, k: int, p: int, l: nat, n: int)
    requires shift_ok(b, k, p), p + l <= b.len(),
    ensures find_n(lens, b, p, l, n) == find_n(lens, b.skip(k), p - k, l, n),
    decreases lens.len() - n,
{
    assert(b.subrange(p, p + l) =~= b.skip(k).subrange(p - k, p - k + l));
    if 0 <= n < lens.len() { lemma_find_n_shift(lens, b, k, p, l, n + 1); }
}

pub proof fn lemma_find_sym_shift(lens: Seq<u8>, b: Seq<bool>, k: int, p: int, l: nat)
    requires shift_ok(b, k, p),
    ensures find_sym(lens, b, p, l) == match find_sym(lens, b.skip(k), p - k, l) {
        None => None,
        Some((s, q)) => Some((s, q + k)),
    },
    decreases 16 - l,
{
    if !(l == 0 || l > maxbits() || p < 0 || p + l > b.len()) {
        lemma_find_n_shift(lens, b, k, p, l, 0);
        lemma_find_sym_shift(lens, b, k, p, l + 1);
    }
}

pub proof fn lemma_decode_sym_shift(lens: Seq<u8>, b: Seq<bool>, k: int, p: int)
    requires shift_ok(b, k, p),
    ensures decode_sym(lens, b, p) == match decode_sym(lens, b.skip(k), p - k) {
        None => None,
        Some((s, q)) => Some((s, q + k)),
    },
{
    lemma_find_sym_shift(lens, b, k, p, 1);
}

pub proof fn lemma_len_dist_shift(dl: Seq<u8>, b: Seq<bool>, k: int, p1: int, s: nat)
    requires shift_ok(b, k, p1),
    ensures len_dist(dl, b, p1, s) == match len_dist(dl, b.skip(k), p1 - k, s) {
        None => None,
        Some((len, d, p4)) => Some((len, d, p4 + k)),
    },
{
    lemma_getbits_shift(b, k, p1, len_extra(s));
    let q2 = p1 + len_extra(s);
    lemma_decode_sym_shift(dl, b, k, q2);
    match decode_sym(dl, b, q2) {
        None => {}
        Some((ds, p3)) => {
            lemma_find_sym_adv(dl, b, q2, 1);
            lemma_getbits_shift(b, k, p3, dist_extra(ds));
        }
    }
}

pub open spec fn step_shift(st: Option<Step>, k: int) -> Option<Step> {
    match st {
        None => None,
        Some(Step::Lit(x, q)) => Some(Step::Lit(x, q + k)),
        Some(Step::End(q)) => Some(Step::End(q + k)),
        Some(Step::Copy(len, d, q)) => Some(Step::Copy(len, d, q + k)),
    }
}

pub proof fn lemma_sym_step_shift(ll: Seq<u8>, dl: Seq<u8>, b: Seq<bool>, k: int, p: int)
    requires shift_ok(b, k, p),
    ensures sym_step(ll, dl, b, p) == step_shift(sym_step(ll, dl, b.skip(k), p - k), k),
{
    lemma_decode_sym_shift(ll, b, k, p);
    match decode_sym(ll, b, p) {
        None => {}
        Some((s, p1)) => {
            lemma_find_sym_adv(ll, b, p, 1);
            if 257 <= s <= 285 {
                lemma_len_dist_shift(dl, b, k, p1, s);
            }
        }
    }
}

pub proof fn lemma_syms_shift(ll: Seq<u8>, dl: Seq<u8>, b: Seq<bool>, k: int, p: int, out: Seq<u8>)
    requires shift_ok(b, k, p),
    ensures inflate_syms(ll, dl, b, p, out) == match inflate_syms(ll, dl, b.skip(k), p - k, out) {
        None => None,
        Some((o, q)) => Some((o, q + k)),
    },
    decreases b.len() - p,
{
    lemma_syms_unfold(ll, dl, b, p, out);
    lemma_syms_unfold(ll, dl, b.skip(k), p - k, out);
    lemma_sym_step_shift(ll, dl, b, k, p);
    match sym_step(ll, dl, b, p) {
        None => {}
        Some(Step::Lit(x, p1)) => {
            lemma_sym_step_bound(ll, dl, b, p);
            lemma_syms_shift(ll, dl, b, k, p1, out.push(x));
        }
        Some(Step::End(p1)) => {}
        Some(Step::Copy(len, d, p4)) => {
            lemma_sym_step_bound(ll, dl, b, p);
            if d <= out.len() { lemma_syms_shift(ll, dl, b, k, p4, lz_copy(out, d, len)); }
        }
    }
}

proof fn lemma_read_cl_shift(b: Seq<bool>, k: int, p: int, hclen: nat, i: nat, acc: Seq<u8>)
    requires shift_ok(b, k, p),
    ensures read_cl(b, p, hclen, i, acc) == match read_cl(b.skip(k), p - k, hclen, i, acc) {
        None => None,
        Some((cl, q)) => Some((cl, q + k)),
    },
    decreases hclen - i,
{
    if i < hclen {
        lemma_getbits_shift(b, k, p, 3);
        match getbits(b, p, 3) {
            None => {}
            Some(v) => {
                assert(p + 3 <= b.len());
                lemma_read_cl_shift(b, k, p + 3, hclen, i + 1, acc.update(cl_order(i) as int, v as u8));
            }
        }
    }
}

proof fn lemma_read_lens_shift(cl: Seq<u8>, b: Seq<bool>, k: int, p: int, total: nat, acc: Seq<u8>)
    requires shift_ok(b, k, p),
    ensures read_lens(cl, b, p, total, acc) == match read_lens(cl, b.skip(k), p - k, total, acc) {
        None => None,
        Some((v, q)) => Some((v, q + k)),
    },
    decreases total - acc.len(),
{
    if acc.len() < total {
        lemma_decode_sym_shift(cl, b, k, p);
        match decode_sym(cl, b, p) {
            None => {}
            Some((s, p1)) => {
                lemma_find_sym_adv(cl, b, p, 1);
                if s < 16 {
                    lemma_read_lens_shift(cl, b, k, p1, total, acc.push(s as u8));
                } else {
                    let (nb, base) = if s == 16 { (2nat, 3nat) } else if s == 17 { (3nat, 3nat) } else { (7nat, 11nat) };
                    lemma_getbits_shift(b, k, p1, nb);
                    match getbits(b, p1, nb) {
                        None => {}
                        Some(e) => {
                            let rep = base + e;
                            let v: u8 = if s == 16 { acc.last() } else { 0u8 };
                            if !(s > 18 || (s == 16 && acc.len() == 0) || acc.len() + rep > total) {
                                assert(p1 + nb <= b.len());
                                lemma_read_lens_shift(cl, b, k, p1 + nb, total, acc + Seq::new(rep, |_i: int| v));
                            }
                        }
                    }
                }
            }
        }
    }
}

pub proof fn lemma_dyn_header_shift(b: Seq<bool>, k: int, p: int)
    requires shift_ok(b, k, p),
    ensures dyn_header(b, p) == match dyn_header(b.skip(k), p - k) {
        None => None,
        Some((lit, dist, q, st)) => Some((lit, dist, q + k, st)),
    },
{
    lemma_getbits_shift(b, k, p, 5);
    lemma_getbits_shift(b, k, p + 5, 5);
    lemma_getbits_shift(b, k, p + 10, 4);
    match (getbits(b, p, 5), getbits(b, p + 5, 5), getbits(b, p + 10, 4)) {
        (Some(hlit), Some(hdist), Some(hclen)) => {
            lemma_read_cl_shift(b, k, p + 14, hclen + 4, 0, Seq::new(19, |_i: int| 0u8));
            match read_cl(b, p + 14, hclen + 4, 0, Seq::new(19, |_i: int| 0u8)) {
                None => {}
                Some((cl, q)) => {
                    lemma_read_cl_pos(b, p + 14, hclen + 4, 0, Seq::new(19, |_i: int| 0u8));
                    lemma_read_lens_shift(cl, b, k, q, hlit + 257 + hdist + 1, Seq::empty());
                }
            }
        }
        _ => {}
    }
}

pub proof fn lemma_stored_shift(b: Seq<bool>, k: int, p: int)
    requires shift_ok(b, k, p),
    ensures stored(b, p) == match stored(b.skip(k), p - k) {
        None => None,
        Some((bytes, q)) => Some((bytes, q + k)),
    },
{
    lemma_stored_unfold(b, p);
    lemma_stored_unfold(b.skip(k), p - k);
    assert(align8(p - k) == align8(p) - k) by {
        assert((p - k) % 8 == p % 8) by (nonlinear_arith) requires k % 8 == 0, 0 <= k <= p;
    }
    let q = align8(p);
    lemma_getbits_shift(b, k, q, 16);
    lemma_getbits_shift(b, k, q + 16, 16);
    match stored_hdr(b, p) {
        None => {}
        Some((len, q0)) => {
            if q0 + 8 * len <= b.len() {
                assert(bytes_at(b, q0, len) =~= bytes_at(b.skip(k), q0 - k, len)) by {
                    assert forall|j: int| 0 <= j < len implies
                        #[trigger] bytes_at(b, q0, len)[j] == bytes_at(b.skip(k), q0 - k, len)[j] by {
                        assert(q0 + 8 * j + 8 <= b.len()) by (nonlinear_arith)
                            requires 0 <= j < len, q0 + 8 * len <= b.len();
                        assert(b.subrange(q0 + 8 * j, q0 + 8 * j + 8)
                            =~= b.skip(k).subrange(q0 - k + 8 * j, q0 - k + 8 * j + 8));
                    }
                }
            }
        }
    }
}

pub proof fn lemma_block_shift(b: Seq<bool>, k: int, p: int, btype: nat, out: Seq<u8>)
    requires shift_ok(b, k, p),
    ensures block(b, p, btype, out) == match block(b.skip(k), p - k, btype, out) {
        None => None,
        Some((o, q, s)) => Some((o, q + k, s)),
    },
{
    if btype == 0 {
        lemma_stored_shift(b, k, p);
    } else if btype == 1 {
        lemma_syms_shift(fixed_lit(), fixed_dist(), b, k, p, out);
    } else if btype == 2 {
        lemma_dyn_header_shift(b, k, p);
        match dyn_header(b, p) {
            None => {}
            Some((lit, dist, q, st)) => {
                lemma_dyn_header_pos(b, p);
                lemma_syms_shift(lit, dist, b, k, q, out);
            }
        }
    }
}

pub proof fn lemma_blocks_shift(b: Seq<bool>, k: int, p: int, out: Seq<u8>, st: bool)
    requires shift_ok(b, k, p),
    ensures inflate_blocks(b, p, out, st) == match inflate_blocks(b.skip(k), p - k, out, st) {
        None => None,
        Some((o, q, s)) => Some((o, q + k, s)),
    },
    decreases b.len() - p,
{
    lemma_getbits_shift(b, k, p, 1);
    lemma_getbits_shift(b, k, p + 1, 2);
    match (getbits(b, p, 1), getbits(b, p + 1, 2)) {
        (Some(bfinal), Some(btype)) => {
            lemma_block_shift(b, k, p + 3, btype, out);
            match block(b, p + 3, btype, out) {
                None => {}
                Some((o, q, s)) => {
                    if bfinal != 1 && !(q <= p || q > b.len()) {
                        lemma_blocks_shift(b, k, q, o, st && s);
                    }
                }
            }
        }
        _ => {}
    }
}

} // verus!

verus! {

pub proof fn lemma_bytes_shift(b: Seq<bool>, k: int, a: int, m: nat)
    requires 0 <= k <= a, a + 8 * m <= b.len(),
    ensures bytes_at(b, a, m) == bytes_at(b.skip(k), a - k, m),
{
    assert forall|j: int| 0 <= j < m implies #[trigger] bytes_at(b, a, m)[j] == bytes_at(b.skip(k), a - k, m)[j] by {
        assert(a + 8 * j + 8 <= b.len()) by (nonlinear_arith) requires 0 <= j < m, a + 8 * m <= b.len();
        assert(b.subrange(a + 8 * j, a + 8 * j + 8) =~= b.skip(k).subrange(a - k + 8 * j, a - k + 8 * j + 8));
    }
    assert(bytes_at(b, a, m) =~= bytes_at(b.skip(k), a - k, m));
}

} // verus!
