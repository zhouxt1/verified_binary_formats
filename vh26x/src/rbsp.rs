//! RBSP trailing bits (H.264 §7.3.2.11, H.265 §7.3.2.11): an RBSP is its
//! SODB, a 1, and 0s to the next byte boundary. The SODB of an RBSP is
//! everything before its last 1 bit (H.264 §7.4.1 NOTE 6), and an RBSP is
//! well formed when that bit is in its last byte.
//!
//! `theorem_rbsp_rt` and `theorem_rbsp_inv`: this is a bijection between
//! bit strings and well-formed RBSPs.
use vstd::prelude::*;
use vbits::bitspec::*;
use crate::eg::*;
use crate::ir::*;

verus! {

/// How many 0 bits follow the last 1 bit of a nonzero byte.
pub open spec fn tz8(b: u8) -> nat {
    if b & 1 != 0 { 0 }
    else if b & 2 != 0 { 1 }
    else if b & 4 != 0 { 2 }
    else if b & 8 != 0 { 3 }
    else if b & 16 != 0 { 4 }
    else if b & 32 != 0 { 5 }
    else if b & 64 != 0 { 6 }
    else if b & 128 != 0 { 7 }
    else { 8 }
}

/// The length of an RBSP's SODB, when the RBSP is well formed.
pub open spec fn sodb_len(r: Seq<u8>) -> Option<nat> {
    if r.len() == 0 || r.last() == 0 { None } else { Some((8 * r.len() - 1 - tz8(r.last())) as nat) }
}

/// An RBSP: the SODB, then `rbsp_trailing_bits( )`.
pub open spec fn rbsp_of(s: Seq<bool>) -> Seq<bool> {
    s + align_code(s.len())
}

proof fn lemma_tz8_bits(b: u8)
    requires b != 0,
    ensures
        tz8(b) < 8,
        bit_of(b, 7 - tz8(b) as int),
        forall|j: int| 7 - tz8(b) < j < 8 ==> !bit_of(b, j),
{
    if b & 1 != 0 {
        assert(b & 1 != 0 ==> (b >> 0u8) & 1u8 == 1u8) by (bit_vector);
    } else if b & 2 != 0 {
        assert(b & 1 == 0 && b & 2 != 0 ==> (b >> 1u8) & 1u8 == 1u8 && (b >> 0u8) & 1u8 != 1u8) by (bit_vector);
    } else if b & 4 != 0 {
        assert(b & 1 == 0 && b & 2 == 0 && b & 4 != 0 ==> (b >> 2u8) & 1u8 == 1u8
            && (b >> 0u8) & 1u8 != 1u8 && (b >> 1u8) & 1u8 != 1u8) by (bit_vector);
    } else if b & 8 != 0 {
        assert(b & 1 == 0 && b & 2 == 0 && b & 4 == 0 && b & 8 != 0 ==> (b >> 3u8) & 1u8 == 1u8
            && (b >> 0u8) & 1u8 != 1u8 && (b >> 1u8) & 1u8 != 1u8 && (b >> 2u8) & 1u8 != 1u8) by (bit_vector);
    } else if b & 16 != 0 {
        assert(b & 1 == 0 && b & 2 == 0 && b & 4 == 0 && b & 8 == 0 && b & 16 != 0 ==> (b >> 4u8) & 1u8 == 1u8
            && (b >> 0u8) & 1u8 != 1u8 && (b >> 1u8) & 1u8 != 1u8 && (b >> 2u8) & 1u8 != 1u8
            && (b >> 3u8) & 1u8 != 1u8) by (bit_vector);
    } else if b & 32 != 0 {
        assert(b & 1 == 0 && b & 2 == 0 && b & 4 == 0 && b & 8 == 0 && b & 16 == 0 && b & 32 != 0
            ==> (b >> 5u8) & 1u8 == 1u8
            && (b >> 0u8) & 1u8 != 1u8 && (b >> 1u8) & 1u8 != 1u8 && (b >> 2u8) & 1u8 != 1u8
            && (b >> 3u8) & 1u8 != 1u8 && (b >> 4u8) & 1u8 != 1u8) by (bit_vector);
    } else if b & 64 != 0 {
        assert(b & 1 == 0 && b & 2 == 0 && b & 4 == 0 && b & 8 == 0 && b & 16 == 0 && b & 32 == 0 && b & 64 != 0
            ==> (b >> 6u8) & 1u8 == 1u8
            && (b >> 0u8) & 1u8 != 1u8 && (b >> 1u8) & 1u8 != 1u8 && (b >> 2u8) & 1u8 != 1u8
            && (b >> 3u8) & 1u8 != 1u8 && (b >> 4u8) & 1u8 != 1u8 && (b >> 5u8) & 1u8 != 1u8) by (bit_vector);
    } else {
        assert(b != 0 && b & 1 == 0 && b & 2 == 0 && b & 4 == 0 && b & 8 == 0 && b & 16 == 0 && b & 32 == 0 && b & 64 == 0
            ==> b & 128 != 0 && (b >> 7u8) & 1u8 == 1u8
            && (b >> 0u8) & 1u8 != 1u8 && (b >> 1u8) & 1u8 != 1u8 && (b >> 2u8) & 1u8 != 1u8
            && (b >> 3u8) & 1u8 != 1u8 && (b >> 4u8) & 1u8 != 1u8 && (b >> 5u8) & 1u8 != 1u8
            && (b >> 6u8) & 1u8 != 1u8) by (bit_vector);
    }
}

/// A byte whose last 1 bit is followed by `z` zeros has `tz8` z.
proof fn lemma_tz8_unique(b: u8, z: nat)
    requires z < 8, bit_of(b, 7 - z as int), forall|j: int| 7 - z < j < 8 ==> !bit_of(b, j),
    ensures b != 0, tz8(b) == z,
{
    assert(bit_of(0u8, 7 - z as int) == false) by {
        let k = z as u8;
        assert((0u8 >> k) & 1u8 != 1u8) by (bit_vector);
    }
    lemma_tz8_bits(b);
    let t = tz8(b);
    if t < z {
        assert(!bit_of(b, 7 - t as int));
    } else if t > z {
        assert(!bit_of(b, 7 - z as int));
    }
}

proof fn lemma_align_len(k: nat)
    ensures (k + align_code(k).len()) % 8 == 0, align_code(k).len() <= 8,
{
}

/// The trailing bits of an RBSP whose last byte is `b`.
proof fn lemma_last_byte(r: Seq<u8>)
    requires r.len() >= 1,
    ensures forall|j: int| 0 <= j < 8 ==> bits_of(r)[8 * (r.len() - 1) + j] == bit_of(r.last(), j),
{
    assert forall|j: int| 0 <= j < 8 implies bits_of(r)[8 * (r.len() - 1) + j] == bit_of(r.last(), j) by {
        let i = 8 * (r.len() - 1) + j;
        assert(i / 8 == r.len() - 1 && i % 8 == j) by (nonlinear_arith)
            requires i == 8 * (r.len() - 1) + j, 0 <= j < 8;
    }
}

/// A well-formed RBSP is its SODB and trailing bits.
pub proof fn theorem_rbsp_inv(r: Seq<u8>)
    requires sodb_len(r) is Some,
    ensures ({
        let k = sodb_len(r).unwrap();
        &&& k <= 8 * r.len()
        &&& bits_of(r) =~= rbsp_of(bits_of(r).take(k as int))
    }),
{
    let b = r.last();
    lemma_tz8_bits(b);
    let t = tz8(b);
    let k = (8 * r.len() - 1 - t) as nat;
    lemma_last_byte(r);
    let s = bits_of(r);
    let a = align_code(k);
    assert((k + 1) % 8 == (8 - t) % 8) by (nonlinear_arith) requires k == 8 * r.len() - 1 - t, t < 8, r.len() >= 1;
    assert(a.len() == 1 + t);
    assert forall|i: int| 0 <= i < s.len() implies s[i] == rbsp_of(s.take(k as int))[i] by {
        if i >= k {
            let j = i - 8 * (r.len() - 1);
            assert(s[i] == bit_of(b, j));
            if i == k {
                assert(j == 7 - t);
            } else {
                assert(7 - t < j < 8);
            }
        }
    }
}

/// Any bit string, with trailing bits, is a well-formed RBSP of it.
pub proof fn theorem_rbsp_rt(s: Seq<bool>, r: Seq<u8>)
    requires bits_of(r) =~= rbsp_of(s),
    ensures sodb_len(r) == Some(s.len()),
{
    let a = align_code(s.len());
    let z = (a.len() - 1) as nat;
    lemma_align_len(s.len());
    assert(bits_of(r).len() == 8 * r.len());
    assert(rbsp_of(s).len() == s.len() + a.len());
    assert(a.len() >= 1);
    assert(r.len() >= 1) by (nonlinear_arith) requires 8 * r.len() == s.len() + a.len(), a.len() >= 1;
    lemma_last_byte(r);
    let base = 8 * (r.len() - 1);
    assert(s.len() + 1 + z == 8 * r.len());
    assert forall|j: int| 7 - z < j < 8 implies !bit_of(r.last(), j) by {
        assert(bits_of(r)[base + j] == a[base + j - s.len()]);
    }
    assert(bit_of(r.last(), 7 - z as int)) by {
        assert(bits_of(r)[base + 7 - z] == a[0]);
    }
    lemma_tz8_unique(r.last(), z);
}

// ------------------------------------------------------------------- exec

pub fn tz8_x(b: u8) -> (t: usize)
    ensures t as nat == tz8(b),
{
    if b & 1 != 0 { 0 }
    else if b & 2 != 0 { 1 }
    else if b & 4 != 0 { 2 }
    else if b & 8 != 0 { 3 }
    else if b & 16 != 0 { 4 }
    else if b & 32 != 0 { 5 }
    else if b & 64 != 0 { 6 }
    else if b & 128 != 0 { 7 }
    else { 8 }
}

pub fn sodb_len_x(r: &[u8]) -> (res: Option<usize>)
    requires 8 * r@.len() <= usize::MAX,
    ensures res matches Some(k) ==> sodb_len(r@) == Some(k as nat), res is None ==> sodb_len(r@) is None,
{
    if r.len() == 0 || r[r.len() - 1] == 0 {
        return None;
    }
    let t = tz8_x(r[r.len() - 1]);
    proof { lemma_tz8_bits(r@.last()); }
    Some(8 * r.len() - 1 - t)
}


/// An RBSP without the cabac_zero_words at its end (H.264 7.3.2.10,
/// H.265 7.3.2.11): each is 0x0000, after rbsp_trailing_bits( ).
pub open spec fn strip_czw(r: Seq<u8>) -> Seq<u8>
    decreases r.len(),
{
    if r.len() >= 2 && r.last() == 0 && r[r.len() - 2] == 0 { strip_czw(r.subrange(0, r.len() - 2)) } else { r }
}

/// A slice's RBSP after a header of `k` bits: slice data, then
/// rbsp_slice_trailing_bits( ) (H.264) or rbsp_slice_segment_trailing_bits( )
/// (H.265), cabac_zero_words included when `cabac`. So the RBSP, less those,
/// ends in rbsp_trailing_bits( ), and its SODB ends after the header: strictly
/// when the slice data is `nonempty` (at least one macroblock or CTU).
pub open spec fn slice_tail_ok(r: Seq<u8>, k: nat, cabac: bool, nonempty: bool) -> bool {
    let r2 = if cabac { strip_czw(r) } else { r };
    match sodb_len(r2) {
        Some(s) => if nonempty { s > k } else { s >= k },
        None => false,
    }
}

pub fn slice_tail_ok_x(r: &[u8], k: usize, cabac: bool, nonempty: bool) -> (ok: bool)
    requires 8 * r@.len() <= usize::MAX,
    ensures ok == slice_tail_ok(r@, k as nat, cabac, nonempty),
{
    let mut n = r.len();
    proof { assert(r@.subrange(0, n as int) =~= r@); }
    if cabac {
        while n >= 2 && r[n - 1] == 0 && r[n - 2] == 0
            invariant
                n <= r.len(),
                strip_czw(r@) == strip_czw(r@.subrange(0, n as int)),
            decreases n,
        {
            proof {
                let t = r@.subrange(0, n as int);
                assert(t.last() == 0 && t[t.len() - 2] == 0);
                assert(t.subrange(0, t.len() - 2) =~= r@.subrange(0, n - 2));
            }
            n -= 2;
        }
    }
    let r2 = &r[..n];
    proof {
        assert(r2@ =~= r@.subrange(0, n as int));
        if cabac {
            let t = r@.subrange(0, n as int);
            assert(!(t.len() >= 2 && t.last() == 0 && t[t.len() - 2] == 0));
            assert(strip_czw(t) == t);
        }
    }
    match sodb_len_x(r2) {
        Some(s) => if nonempty { s > k } else { s >= k },
        None => false,
    }
}

} // verus!
