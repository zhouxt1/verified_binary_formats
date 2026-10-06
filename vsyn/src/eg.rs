//! The descriptors of the syntax tables (H.264 §7.2, H.265 §7.2), as
//! spec-level codes: `u(n)`, `ue(v)` and `se(v)` (H.264 §9.1, H.265 §9.2),
//! and the 0xFF-byte coding of an SEI message's type and size (H.264
//! §7.3.2.3.1, H.265 §7.3.5). Each is a prefix code, and each lemma pair
//! says so: the code of a value reads back as that value whatever follows
//! it (`_rt`), and whatever reads as a value is that value's code (`_inv`).
use vstd::prelude::*;
use vbits::bitspec::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::prim_write::{bits_seq, lemma_bits_seq_val, lemma_bits_seq_of_val};

verus! {

pub open spec fn zeros(n: nat) -> Seq<bool> {
    Seq::new(n, |i: int| false)
}

/// The largest `ue(v)` value: the code with 31 leading zeros. A code with
/// 32 or more has a value no syntax element's range admits (every range
/// ends at 2^32 − 2 or below), so reading one is an error.
pub open spec fn ue_max() -> nat { 4294967294nat }

/// The largest magnitude of an `se(v)` value, the image of `ue_max()`.
pub open spec fn se_max() -> int { 2147483647int }

/// ⌊log2 m⌋, for m ≥ 1.
pub open spec fn ilog2(m: nat) -> nat
    decreases m,
{
    if m <= 1 { 0 } else { 1 + ilog2(m / 2) }
}

pub proof fn lemma_ilog2(m: nat)
    requires m >= 1,
    ensures p2(ilog2(m)) <= m < p2(ilog2(m) + 1),
    decreases m,
{
    if m > 1 {
        lemma_ilog2(m / 2);
        let l = ilog2(m / 2);
        assert(p2(l + 1) == 2 * p2(l));
        assert(p2(l + 2) == 2 * p2(l + 1));
        assert(ilog2(m) == l + 1);
    }
}

pub proof fn lemma_ilog2_unique(m: nat, l: nat)
    requires p2(l) <= m < p2(l + 1),
    ensures ilog2(m) == l,
    decreases l,
{
    if l == 0 {
        assert(p2(1) == 2);
    } else {
        let l1 = (l - 1) as nat;
        assert(p2(l) == 2 * p2(l1));
        assert(p2(l + 1) == 2 * p2(l));
        lemma_p2_pos(l1);
        assert(p2(l1) <= m / 2 < p2(l1 + 1));
        lemma_ilog2_unique(m / 2, l1);
        assert(m > 1);
    }
}

pub proof fn lemma_p2_mono_strict(a: nat, b: nat)
    requires a < b,
    ensures p2(a) < p2(b),
    decreases b,
{
    lemma_p2_pos(a);
    if b == a + 1 {
    } else {
        lemma_p2_mono_strict(a, (b - 1) as nat);
    }
}

pub proof fn lemma_p2_32()
    ensures p2(32) == 4294967296nat, p2(31) == 2147483648nat,
{
    reveal_with_fuel(p2, 9);
    assert(p2(8) == 256);
    lemma_p2_adds(8, 8);
    lemma_p2_adds(16, 8);
    lemma_p2_adds(24, 7);
    assert(p2(7) == 128);
    lemma_p2_adds(16, 16);
}

// ------------------------------------------------------------------ u(n)

pub open spec fn u_parse(s: Seq<bool>, n: nat) -> Option<(nat, nat)> {
    if n <= s.len() { Some((bits_val(s.take(n as int)), n)) } else { None }
}

pub open spec fn u_code(v: nat, n: nat) -> Seq<bool> {
    bits_seq(v as u64, n)
}

pub proof fn lemma_u_rt(v: nat, n: nat, rest: Seq<bool>)
    requires n <= 64, v < p2(n),
    ensures u_parse(u_code(v, n) + rest, n) == Some((v, n)), u_code(v, n).len() == n,
{
    vbits::prim_read::lemma_p2_mono(n, 64);
    vbits::prim_read::lemma_p2_64();
    lemma_bits_seq_val(v as u64, n);
    assert((u_code(v, n) + rest).take(n as int) =~= u_code(v, n));
}

pub proof fn lemma_u_inv(s: Seq<bool>, n: nat)
    requires n <= 64, u_parse(s, n) is Some,
    ensures ({
        let (v, k) = u_parse(s, n).unwrap();
        &&& k == n && k <= s.len() && v < p2(n)
        &&& u_code(v, n) == s.take(k as int)
    }),
{
    lemma_bits_seq_of_val(s.take(n as int));
}

// ----------------------------------------------------------------- ue(v)

/// The index of the first 1 in `s` at or after `i`, if it is before `lim`.
pub open spec fn first_one(s: Seq<bool>, i: nat, lim: nat) -> Option<nat>
    decreases lim - i,
{
    if i >= lim || i >= s.len() {
        None
    } else if s[i as int] {
        Some(i)
    } else {
        first_one(s, i + 1, lim)
    }
}

pub proof fn lemma_first_one_at(s: Seq<bool>, i: nat, lim: nat, l: nat)
    requires
        i <= l < lim, l < s.len(), s[l as int],
        forall|j: int| i <= j < l ==> !s[j],
    ensures first_one(s, i, lim) == Some(l),
    decreases l - i,
{
    if i < l {
        lemma_first_one_at(s, i + 1, lim, l);
    }
}

pub proof fn lemma_first_one_props(s: Seq<bool>, i: nat, lim: nat)
    requires first_one(s, i, lim) is Some,
    ensures ({
        let l = first_one(s, i, lim).unwrap();
        &&& i <= l < lim && l < s.len() && s[l as int]
        &&& forall|j: int| i <= j < l ==> !s[j]
    }),
    decreases lim - i,
{
    if i < lim && i < s.len() && !s[i as int] {
        lemma_first_one_props(s, i + 1, lim);
    }
}

/// §9.1 (9-1), (9-2): leading zeros, a 1, then as many bits again.
pub open spec fn ue_parse(s: Seq<bool>) -> Option<(nat, nat)> {
    match first_one(s, 0, 32) {
        Some(l) => if 2 * l + 1 <= s.len() {
            Some(((bits_val(s.subrange(l as int, (2 * l + 1) as int)) - 1) as nat, 2 * l + 1))
        } else {
            None
        },
        None => None,
    }
}

/// `v + 1` in binary, after as many zeros as it has bits after its first.
pub open spec fn ue_code(v: nat) -> Seq<bool> {
    let m = v + 1;
    let l = ilog2(m);
    zeros(l) + bits_seq(m as u64, l + 1)
}

/// The leading bit of `m`'s (l+1)-bit binary is 1 when 2^l ≤ m.
proof fn lemma_top_bit(m: nat, l: nat)
    requires p2(l) <= m < p2(l + 1), l < 64,
    ensures bits_seq(m as u64, l + 1)[0],
{
    lemma_p2_pos(l);
    vbits::prim_read::lemma_p2_mono(l + 1, 64);
    vbits::prim_read::lemma_p2_64();
    assert(p2(l + 1) == 2 * p2(l));
    assert((m as u64) as nat == m);
    assert(((l + 1) - 1 - 0) as nat == l);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(m as int, p2(l) as int, 1, (m - p2(l)) as int);
    assert(m / p2(l) == 1);
}

pub proof fn lemma_ue_rt(v: nat, rest: Seq<bool>)
    requires v <= ue_max(),
    ensures
        ue_parse(ue_code(v) + rest) == Some((v, ue_code(v).len())),
        ue_code(v).len() == 2 * ilog2(v + 1) + 1,
        ilog2(v + 1) < 32,
{
    let m = v + 1;
    let l = ilog2(m);
    lemma_ilog2(m);
    lemma_p2_32();
    if l >= 32 {
        vbits::prim_read::lemma_p2_mono(32, l);
    }
    assert(l < 32);
    let c = ue_code(v);
    let s = c + rest;
    lemma_top_bit(m, l);
    assert(s[l as int] == bits_seq(m as u64, l + 1)[0]);
    assert forall|j: int| 0 <= j < l implies !s[j] by {
        assert(s[j] == zeros(l)[j]);
    }
    lemma_first_one_at(s, 0, 32, l);
    assert(s.subrange(l as int, (2 * l + 1) as int) =~= bits_seq(m as u64, l + 1));
    vbits::prim_read::lemma_p2_mono(l + 1, 64);
    vbits::prim_read::lemma_p2_64();
    lemma_bits_seq_val(m as u64, l + 1);
}

pub proof fn lemma_ue_inv(s: Seq<bool>)
    requires ue_parse(s) is Some,
    ensures ({
        let (v, k) = ue_parse(s).unwrap();
        &&& v <= ue_max() && k <= s.len() && k >= 1
        &&& ue_code(v) == s.take(k as int)
    }),
{
    let l = first_one(s, 0, 32).unwrap();
    lemma_first_one_props(s, 0, 32);
    let t = s.subrange(l as int, (2 * l + 1) as int);
    let m = bits_val(t);
    lemma_bits_val_split(t, 1);
    assert(t.take(1) =~= seq![true]);
    reveal_with_fuel(bits_val, 2);
    assert(seq![true].drop_last() =~= Seq::<bool>::empty());
    assert(bits_val(seq![true]) == 1);
    assert(t.len() == l + 1);
    assert(((t.len() - 1) as nat) == l);
    assert(m == 1 * p2(l) + bits_val(t.skip(1)));
    assert(m >= p2(l));
    lemma_bits_val_bound(t);
    lemma_ilog2_unique(m, l);
    lemma_p2_pos(l);
    lemma_p2_32();
    vbits::prim_read::lemma_p2_mono(l + 1, 32);
    let v = (m - 1) as nat;
    assert(v <= ue_max());
    assert(v + 1 == m);
    lemma_bits_seq_of_val(t);
    assert(s.take((2 * l + 1) as int) =~= zeros(l) + t);
}

// ----------------------------------------------------------------- se(v)

/// §9.1.1 Table 9-3: codeNum k is (−1)^(k+1) Ceil(k ÷ 2).
pub open spec fn se_of_code(k: nat) -> int {
    if k % 2 == 1 { ((k + 1) / 2) as int } else { -((k / 2) as int) }
}

pub open spec fn code_of_se(v: int) -> nat {
    if v > 0 { (2 * v - 1) as nat } else { (-2 * v) as nat }
}

pub open spec fn se_parse(s: Seq<bool>) -> Option<(int, nat)> {
    match ue_parse(s) {
        Some((k, n)) => Some((se_of_code(k), n)),
        None => None,
    }
}

pub open spec fn se_code(v: int) -> Seq<bool> {
    ue_code(code_of_se(v))
}

pub proof fn lemma_se_map(v: int)
    requires -se_max() <= v <= se_max(),
    ensures code_of_se(v) <= ue_max(), se_of_code(code_of_se(v)) == v,
{
}

pub proof fn lemma_se_map_inv(k: nat)
    requires k <= ue_max(),
    ensures -se_max() <= se_of_code(k) <= se_max(), code_of_se(se_of_code(k)) == k,
{
}

pub proof fn lemma_se_rt(v: int, rest: Seq<bool>)
    requires -se_max() <= v <= se_max(),
    ensures se_parse(se_code(v) + rest) == Some((v, se_code(v).len())),
{
    lemma_se_map(v);
    lemma_ue_rt(code_of_se(v), rest);
}

pub proof fn lemma_se_inv(s: Seq<bool>)
    requires se_parse(s) is Some,
    ensures ({
        let (v, k) = se_parse(s).unwrap();
        &&& -se_max() <= v <= se_max() && k <= s.len() && k >= 1
        &&& se_code(v) == s.take(k as int)
    }),
{
    lemma_ue_inv(s);
    lemma_se_map_inv(ue_parse(s).unwrap().0);
}

// ------------------------------------------------------ 0xFF-byte coding

/// `payloadType` and `payloadSize`: a 0xFF byte for each 255, then the
/// remainder as a byte, which is never 0xFF.
pub open spec fn ff_code(v: nat) -> Seq<bool>
    decreases v,
{
    if v < 255 { bits_seq(v as u64, 8) } else { bits_seq(255u64, 8) + ff_code((v - 255) as nat) }
}

pub open spec fn ff_parse(s: Seq<bool>) -> Option<(nat, nat)>
    decreases s.len(),
{
    if s.len() < 8 {
        None
    } else {
        let b = bits_val(s.take(8));
        if b == 255 {
            match ff_parse(s.skip(8)) {
                Some((v, k)) => Some((v + 255, k + 8)),
                None => None,
            }
        } else {
            Some((b, 8))
        }
    }
}

proof fn lemma_p2_8()
    ensures p2(8) == 256,
{
    reveal_with_fuel(p2, 9);
}

pub proof fn lemma_ff_rt(v: nat, rest: Seq<bool>)
    ensures ff_parse(ff_code(v) + rest) == Some((v, ff_code(v).len())), ff_code(v).len() >= 8,
    decreases v,
{
    lemma_p2_8();
    let s = ff_code(v) + rest;
    if v < 255 {
        lemma_bits_seq_val(v as u64, 8);
        assert(s.take(8) =~= bits_seq(v as u64, 8));
    } else {
        lemma_ff_rt((v - 255) as nat, rest);
        lemma_bits_seq_val(255u64, 8);
        assert(s.take(8) =~= bits_seq(255u64, 8));
        assert(s.skip(8) =~= ff_code((v - 255) as nat) + rest);
    }
}

pub proof fn lemma_ff_inv(s: Seq<bool>)
    requires ff_parse(s) is Some,
    ensures ({
        let (v, k) = ff_parse(s).unwrap();
        &&& k <= s.len() && k >= 8
        &&& ff_code(v) == s.take(k as int)
    }),
    decreases s.len(),
{
    lemma_p2_8();
    let b = bits_val(s.take(8));
    lemma_bits_seq_of_val(s.take(8));
    if b == 255 {
        lemma_ff_inv(s.skip(8));
        let (v, k) = ff_parse(s.skip(8)).unwrap();
        assert(s.take((8 + k) as int) =~= s.take(8) + s.skip(8).take(k as int));
    } else {
        lemma_bits_val_bound(s.take(8));
    }
}

} // verus!
