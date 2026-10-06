//! The descriptors of AV1 (§4.10) beyond `f(n)`, which is `u(n)`: `su(n)`,
//! `ns(n)`, `le(n)`, `uvlc()` and `leb128()`, as spec-level codes. As in
//! `eg`, each lemma pair says a descriptor is a prefix code: a value's code
//! reads back as that value whatever follows it (`_rt`), and whatever reads
//! as a value is that value's code (`_inv`).
//!
//! Two of them have several codes for one value. `leb128()` may spend more
//! bytes than its value needs (§4.10.5: "There is no requirement that this
//! syntax descriptor uses the most compressed representation"), and
//! `uvlc()` returns 2^32 − 1 for any number of leading zeros from 32 up.
//! For these the code is indexed by a *choice*: the extra bytes, the extra
//! zeros. Choice 0 is the canonical code, and the pair of value and choice
//! determines the code.
use vstd::prelude::*;
use vbits::bitspec::*;
use crate::eg::*;

verus! {

// ------------------------------------------------------------------ su(n)

/// `su(n)`: the bottom `n` bits of a two's-complement integer.
pub open spec fn su_parse(s: Seq<bool>, n: nat) -> Option<(int, nat)> {
    match u_parse(s, n) {
        Some((u, k)) => Some((if n >= 1 && u >= p2((n - 1) as nat) { u - p2(n) } else { u as int }, k)),
        None => None,
    }
}

pub open spec fn su_in(v: int, n: nat) -> bool {
    n >= 1 && -(p2((n - 1) as nat) as int) <= v < p2((n - 1) as nat)
}

pub open spec fn su_code(v: int, n: nat) -> Seq<bool> {
    u_code(if v < 0 { (v + p2(n)) as nat } else { v as nat }, n)
}

proof fn lemma_p2_half(n: nat)
    requires n >= 1,
    ensures p2(n) == 2 * p2((n - 1) as nat),
{
    assert(p2(n) == 2 * p2((n - 1) as nat)) by { reveal_with_fuel(p2, 2); }
}

pub proof fn lemma_su_rt(v: int, n: nat, rest: Seq<bool>)
    requires 1 <= n <= 48, su_in(v, n),
    ensures su_parse(su_code(v, n) + rest, n) == Some((v, n)), su_code(v, n).len() == n,
{
    lemma_p2_half(n);
    let u: nat = if v < 0 { (v + p2(n)) as nat } else { v as nat };
    assert(u < p2(n));
    lemma_u_rt(u, n, rest);
}

pub proof fn lemma_su_inv(s: Seq<bool>, n: nat)
    requires 1 <= n <= 48, su_parse(s, n) is Some,
    ensures ({
        let (v, k) = su_parse(s, n).unwrap();
        &&& k == n && k <= s.len() && su_in(v, n)
        &&& su_code(v, n) == s.take(k as int)
    }),
{
    lemma_p2_half(n);
    lemma_u_inv(s, n);
    let (u, k) = u_parse(s, n).unwrap();
    let (v, _) = su_parse(s, n).unwrap();
    if u >= p2((n - 1) as nat) {
        assert(v < 0);
        assert((v + p2(n)) as nat == u);
    } else {
        assert(v >= 0);
        assert(v as nat == u);
    }
}

// ------------------------------------------------------------------ ns(n)

/// `w` and `m` of §4.10.7: values below `m` take `w − 1` bits, the rest `w`.
pub open spec fn ns_w(n: nat) -> nat { ilog2(n) + 1 }

pub open spec fn ns_m(n: nat) -> nat { (p2(ns_w(n)) - n) as nat }

/// `ns(n)`: `v` in `w − 1` bits; if `v ≥ m`, one more bit, and the value is
/// the `w` bits read, less `m` (`(v << 1) − m + extra_bit`).
pub open spec fn ns_parse(s: Seq<bool>, n: nat) -> Option<(nat, nat)> {
    let w = ns_w(n);
    let m = ns_m(n);
    match u_parse(s, (w - 1) as nat) {
        Some((v, _)) => if v < m {
            Some((v, (w - 1) as nat))
        } else {
            match u_parse(s, w) {
                Some((y, _)) => Some(((y - m) as nat, w)),
                None => None,
            }
        },
        None => None,
    }
}

pub open spec fn ns_code(x: nat, n: nat) -> Seq<bool> {
    let w = ns_w(n);
    let m = ns_m(n);
    if x < m { u_code(x, (w - 1) as nat) } else { u_code(x + m, w) }
}

proof fn lemma_ns_wm(n: nat)
    requires n >= 1,
    ensures
        p2((ns_w(n) - 1) as nat) <= n < p2(ns_w(n)),
        p2(ns_w(n)) == 2 * p2((ns_w(n) - 1) as nat),
        1 <= ns_m(n) <= p2((ns_w(n) - 1) as nat),
        ns_m(n) + n == p2(ns_w(n)),
{
    lemma_ilog2(n);
    lemma_p2_half(ns_w(n));
    assert((ns_w(n) - 1) as nat == ilog2(n));
}

/// Splitting `w` bits into the first `w − 1` and the last.
proof fn lemma_split_last(t: Seq<bool>)
    requires t.len() >= 1,
    ensures
        bits_val(t) == 2 * bits_val(t.take(t.len() - 1)) + bits_val(t.skip(t.len() - 1)),
        bits_val(t.skip(t.len() - 1)) < 2,
{
    lemma_bits_val_split(t, t.len() - 1);
    assert(((t.len() - (t.len() - 1)) as nat) == 1nat);
    assert(p2(1) == 2) by { reveal_with_fuel(p2, 2); }
    lemma_bits_val_bound(t.skip(t.len() - 1));
}

pub proof fn lemma_ns_rt(x: nat, n: nat, rest: Seq<bool>)
    requires 1 <= n, ns_w(n) <= 48, x < n,
    ensures ns_parse(ns_code(x, n) + rest, n) == Some((x, ns_code(x, n).len())),
{
    lemma_ns_wm(n);
    let w = ns_w(n);
    let m = ns_m(n);
    let c = ns_code(x, n);
    let s = c + rest;
    if x < m {
        vbits::prim_read::lemma_p2_mono((w - 1) as nat, w);
        lemma_u_rt(x, (w - 1) as nat, rest);
    } else {
        lemma_u_rt(x + m, w, rest);
        assert(s.take(w as int) =~= c);
        assert(s.take((w - 1) as int) =~= c.take((w - 1) as int));
        lemma_split_last(c);
        let v = bits_val(c.take((w - 1) as int));
        assert(bits_val(c) == x + m);
        assert(v >= m);
    }
}

pub proof fn lemma_ns_inv(s: Seq<bool>, n: nat)
    requires 1 <= n, ns_w(n) <= 48, ns_parse(s, n) is Some,
    ensures ({
        let (x, k) = ns_parse(s, n).unwrap();
        &&& x < n && k <= s.len()
        &&& ns_code(x, n) == s.take(k as int)
    }),
{
    lemma_ns_wm(n);
    let w = ns_w(n);
    let m = ns_m(n);
    lemma_u_inv(s, (w - 1) as nat);
    let (v, _) = u_parse(s, (w - 1) as nat).unwrap();
    if v >= m {
        lemma_u_inv(s, w);
        let (y, _) = u_parse(s, w).unwrap();
        let t = s.take(w as int);
        lemma_split_last(t);
        assert(t.take((w - 1) as int) =~= s.take((w - 1) as int));
        assert(y >= 2 * m);
        assert(((y - m) as nat) + m == y);
    }
}

// ------------------------------------------------------------------ le(n)

/// `le(n)`: `n` bytes, least significant first.
pub open spec fn le_parse(s: Seq<bool>, n: nat) -> Option<(nat, nat)>
    decreases n,
{
    if n == 0 {
        Some((0, 0))
    } else if s.len() < 8 {
        None
    } else {
        match le_parse(s.skip(8), (n - 1) as nat) {
            Some((r, k)) => Some((bits_val(s.take(8)) + 256 * r, k + 8)),
            None => None,
        }
    }
}

pub open spec fn le_code(v: nat, n: nat) -> Seq<bool>
    decreases n,
{
    if n == 0 { Seq::empty() } else { u_code(v % 256, 8) + le_code(v / 256, (n - 1) as nat) }
}

proof fn lemma_p2_8n(n: nat)
    requires n >= 1,
    ensures p2(8 * n) == 256 * p2(8 * (n - 1) as nat), p2(8) == 256,
{
    reveal_with_fuel(p2, 9);
    lemma_p2_adds(8 * (n - 1) as nat, 8);
    assert(8 * (n - 1) as nat + 8 == 8 * n);
}

pub proof fn lemma_le_rt(v: nat, n: nat, rest: Seq<bool>)
    requires v < p2(8 * n),
    ensures le_parse(le_code(v, n) + rest, n) == Some((v, 8 * n)), le_code(v, n).len() == 8 * n,
    decreases n,
{
    if n == 0 {
        assert(p2(0) == 1);
    } else {
        lemma_p2_8n(n);
        assert(v / 256 < p2(8 * (n - 1) as nat)) by (nonlinear_arith)
            requires v < 256 * p2(8 * (n - 1) as nat);
        lemma_le_rt(v / 256, (n - 1) as nat, rest);
        lemma_u_rt(v % 256, 8, le_code(v / 256, (n - 1) as nat) + rest);
        let s = le_code(v, n) + rest;
        assert(s =~= u_code(v % 256, 8) + (le_code(v / 256, (n - 1) as nat) + rest));
        assert(s.skip(8) =~= le_code(v / 256, (n - 1) as nat) + rest);
        assert(s.take(8) =~= u_code(v % 256, 8));
        vbits::prim_write::lemma_bits_seq_val((v % 256) as u64, 8);
        vbits::prim_read::lemma_p2_mono(8, 64);
        vbits::prim_read::lemma_p2_64();
    }
}

pub proof fn lemma_le_inv(s: Seq<bool>, n: nat)
    requires le_parse(s, n) is Some,
    ensures ({
        let (v, k) = le_parse(s, n).unwrap();
        &&& k == 8 * n && k <= s.len() && v < p2(8 * n)
        &&& le_code(v, n) == s.take(k as int)
    }),
    decreases n,
{
    if n == 0 {
        assert(p2(0) == 1);
        assert(s.take(0) =~= Seq::<bool>::empty());
    } else {
        lemma_p2_8n(n);
        lemma_le_inv(s.skip(8), (n - 1) as nat);
        let (r, k) = le_parse(s.skip(8), (n - 1) as nat).unwrap();
        let b = bits_val(s.take(8));
        lemma_bits_val_bound(s.take(8));
        lemma_u_inv(s, 8);
        let v = b + 256 * r;
        assert(v % 256 == b && v / 256 == r) by (nonlinear_arith) requires v == b + 256 * r, b < 256;
        assert(v < p2(8 * n)) by (nonlinear_arith)
            requires v == b + 256 * r, b < 256, r < p2(8 * (n - 1) as nat), p2(8 * n) == 256 * p2(8 * (n - 1) as nat);
        assert(s.take((8 + k) as int) =~= s.take(8) + s.skip(8).take(k as int));
    }
}

// ------------------------------------------------------------------ uvlc()

/// The value `uvlc()` returns for 32 or more leading zeros.
pub open spec fn uvlc_max() -> nat { 4294967295nat }

/// `uvlc()` (§4.10.3): below 32 leading zeros it is `ue(v)`'s code; from 32
/// up, 2^32 − 1, with the zeros past 32 as the choice. The value, the
/// choice, and the length.
pub open spec fn uvlc_parse(s: Seq<bool>) -> Option<(nat, nat, nat)> {
    match first_one(s, 0, 32) {
        Some(_) => match ue_parse(s) {
            Some((v, k)) => Some((v, 0, k)),
            None => None,
        },
        None => match first_one(s, 32, s.len()) {
            Some(l) => Some((uvlc_max(), (l - 32) as nat, l + 1)),
            None => None,
        },
    }
}

pub open spec fn uvlc_code(v: nat, w: nat) -> Option<Seq<bool>> {
    if v <= ue_max() && w == 0 {
        Some(ue_code(v))
    } else if v == uvlc_max() {
        Some(zeros(32 + w) + seq![true])
    } else {
        None
    }
}

pub proof fn lemma_first_one_none_inv(s: Seq<bool>, i: nat, lim: nat)
    requires first_one(s, i, lim) is None,
    ensures forall|j: int| i <= j < lim && j < s.len() ==> !s[j],
    decreases lim - i,
{
    if i < lim && i < s.len() {
        lemma_first_one_none_inv(s, i + 1, lim);
    }
}

pub proof fn lemma_uvlc_rt(v: nat, w: nat, rest: Seq<bool>)
    requires uvlc_code(v, w) is Some,
    ensures ({
        let c = uvlc_code(v, w).unwrap();
        uvlc_parse(c + rest) == Some((v, w, c.len()))
    }),
{
    let c = uvlc_code(v, w).unwrap();
    let s = c + rest;
    if v <= ue_max() && w == 0 {
        lemma_ue_rt(v, rest);
    } else {
        assert forall|j: int| 0 <= j < 32 && j < s.len() implies !s[j] by {
            assert(s[j] == zeros(32 + w)[j]);
        }
        vsyn_first_one_none(s, 0, 32);
        assert forall|j: int| 32 <= j < 32 + w implies !s[j] by {
            assert(s[j] == zeros(32 + w)[j]);
        }
        assert(s[(32 + w) as int] == true);
        lemma_first_one_at(s, 32, s.len(), 32 + w);
    }
}

proof fn vsyn_first_one_none(s: Seq<bool>, i: nat, lim: nat)
    requires forall|j: int| i <= j < lim && j < s.len() ==> !s[j],
    ensures first_one(s, i, lim) is None,
    decreases lim - i,
{
    if i < lim && i < s.len() {
        vsyn_first_one_none(s, i + 1, lim);
    }
}

pub proof fn lemma_uvlc_inv(s: Seq<bool>)
    requires uvlc_parse(s) is Some,
    ensures ({
        let (v, w, k) = uvlc_parse(s).unwrap();
        &&& k <= s.len() && v <= uvlc_max()
        &&& uvlc_code(v, w) == Some(s.take(k as int))
    }),
{
    match first_one(s, 0, 32) {
        Some(_) => {
            lemma_ue_inv(s);
        }
        None => {
            let l = first_one(s, 32, s.len()).unwrap();
            lemma_first_one_props(s, 32, s.len());
            lemma_first_one_none_inv(s, 0, 32);
            let w = (l - 32) as nat;
            assert(s.take((l + 1) as int) =~= zeros(32 + w) + seq![true]);
        }
    }
}

// ---------------------------------------------------------------- leb128()

/// `leb128()` (§4.10.5), from its `i`-th byte: 7 bits of value in each
/// byte, least significant first, and a top bit that says whether more
/// follow. The 8th byte must end it. The value, and the bytes read.
pub open spec fn leb_parse(s: Seq<bool>, i: nat) -> Option<(nat, nat)>
    decreases 8 - i,
{
    if i >= 8 || s.len() < 8 {
        None
    } else {
        let b = bits_val(s.take(8));
        if b < 128 {
            Some((b, 1))
        } else {
            match leb_parse(s.skip(8), i + 1) {
                Some((r, k)) => Some((((b - 128) + 128 * r) as nat, k + 1)),
                None => None,
            }
        }
    }
}

/// `v` in `k` bytes.
pub open spec fn leb_code(v: nat, k: nat) -> Seq<bool>
    decreases k,
{
    if k <= 1 { u_code(v, 8) } else { u_code(128 + v % 128, 8) + leb_code(v / 128, (k - 1) as nat) }
}

/// The fewest bytes `v` fits in.
pub open spec fn leb_min(v: nat) -> nat
    decreases v,
{
    if v < 128 { 1 } else { 1 + leb_min(v / 128) }
}

proof fn lemma_p2_7k(k: nat)
    requires k >= 1,
    ensures p2(7 * k) == 128 * p2(7 * (k - 1) as nat), p2(7) == 128, p2(8) == 256,
{
    reveal_with_fuel(p2, 9);
    lemma_p2_adds(7 * (k - 1) as nat, 7);
    assert(7 * (k - 1) as nat + 7 == 7 * k);
}

/// `v` fits in `k ≥ 1` bytes exactly when `leb_min(v) ≤ k`.
pub proof fn lemma_leb_min(v: nat, k: nat)
    requires k >= 1,
    ensures (v < p2(7 * k)) == (leb_min(v) <= k), leb_min(v) >= 1,
    decreases k,
{
    lemma_p2_7k(k);
    if k == 1 {
        assert(p2(0) == 1);
        if v >= 128 {
            lemma_leb_min_pos(v / 128);
        }
    } else {
        if v >= 128 {
            lemma_leb_min(v / 128, (k - 1) as nat);
            assert((v < p2(7 * k)) == (v / 128 < p2(7 * (k - 1) as nat))) by (nonlinear_arith)
                requires p2(7 * k) == 128 * p2(7 * (k - 1) as nat), v >= 0;
        } else {
            lemma_p2_pos(7 * (k - 1) as nat);
            assert(v < p2(7 * k)) by (nonlinear_arith)
                requires p2(7 * k) == 128 * p2(7 * (k - 1) as nat), v < 128, p2(7 * (k - 1) as nat) >= 1;
        }
    }
}

proof fn lemma_leb_min_pos(v: nat)
    ensures leb_min(v) >= 1,
    decreases v,
{
    if v >= 128 { lemma_leb_min_pos(v / 128); }
}

pub proof fn lemma_leb_rt(v: nat, k: nat, i: nat, rest: Seq<bool>)
    requires 1 <= k, i + k <= 8, v < p2(7 * k),
    ensures leb_parse(leb_code(v, k) + rest, i) == Some((v, k)), leb_code(v, k).len() == 8 * k,
    decreases k,
{
    lemma_p2_7k(k);
    let s = leb_code(v, k) + rest;
    vbits::prim_read::lemma_p2_mono(8, 64);
    vbits::prim_read::lemma_p2_64();
    if k == 1 {
        assert(p2(0) == 1);
        lemma_u_rt(v, 8, rest);
        assert(s.take(8) =~= u_code(v, 8));
        vbits::prim_write::lemma_bits_seq_val(v as u64, 8);
    } else {
        let hi = v / 128;
        assert(hi < p2(7 * (k - 1) as nat)) by (nonlinear_arith)
            requires v < 128 * p2(7 * (k - 1) as nat), hi == v / 128;
        lemma_leb_rt(hi, (k - 1) as nat, i + 1, rest);
        let b = 128 + v % 128;
        lemma_u_rt(b, 8, leb_code(hi, (k - 1) as nat) + rest);
        assert(s =~= u_code(b, 8) + (leb_code(hi, (k - 1) as nat) + rest));
        assert(s.take(8) =~= u_code(b, 8));
        assert(s.skip(8) =~= leb_code(hi, (k - 1) as nat) + rest);
        vbits::prim_write::lemma_bits_seq_val(b as u64, 8);
        assert((b - 128) + 128 * hi == v) by (nonlinear_arith) requires b == 128 + v % 128, hi == v / 128;
    }
}

pub proof fn lemma_leb_inv(s: Seq<bool>, i: nat)
    requires leb_parse(s, i) is Some,
    ensures ({
        let (v, k) = leb_parse(s, i).unwrap();
        &&& 1 <= k && i + k <= 8 && 8 * k <= s.len() && v < p2(7 * k)
        &&& leb_code(v, k) == s.take(8 * k as int)
    }),
    decreases 8 - i,
{
    let b = bits_val(s.take(8));
    lemma_bits_val_bound(s.take(8));
    lemma_u_inv(s, 8);
    lemma_p2_7k(1);
    if b < 128 {
        assert(p2(7 * 1) == 128) by { assert(7 * 1 == 7); }
    } else {
        lemma_leb_inv(s.skip(8), i + 1);
        let (r, k1) = leb_parse(s.skip(8), i + 1).unwrap();
        let k = k1 + 1;
        lemma_p2_7k(k);
        let v = (b - 128) + 128 * r;
        assert(v % 128 == b - 128 && v / 128 == r) by (nonlinear_arith) requires v == (b - 128) + 128 * r, 128 <= b < 256;
        assert(v < p2(7 * k)) by (nonlinear_arith)
            requires v == (b - 128) + 128 * r, b < 256, r < p2(7 * (k - 1) as nat), p2(7 * k) == 128 * p2(7 * (k - 1) as nat);
        assert((k - 1) as nat == k1);
        assert(s.take((8 * k) as int) =~= s.take(8) + s.skip(8).take((8 * k1) as int));
    }
}

} // verus!
