//! The boolean entropy decoder (RFC 6386 20.2), proved to follow
//! `spec::b_get` and its derived readers.
use vstd::prelude::*;
use super::spec::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{pow2, lemma_pow2_adds, lemma_pow2_pos, lemma2_to64};

verus! {

/// Byte `k` of the partition as dixie reads it: 0 at and past `end`.
pub open spec fn sbyte(buf: Seq<u8>, end: nat, k: int) -> int {
    if 0 <= k < end && k < buf.len() { buf[k] as int } else { 0 }
}

/// Bytes `lo..hi` of the partition (`sbyte`), as a big-endian number.
pub open spec fn bytes(buf: Seq<u8>, end: nat, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { bytes(buf, end, lo, hi - 1) * 256 + sbyte(buf, end, hi - 1) }
}

proof fn lemma_bytes_bound(buf: Seq<u8>, end: nat, lo: int, hi: int)
    requires lo <= hi,
    ensures 0 <= bytes(buf, end, lo, hi) < pow2((8 * (hi - lo)) as nat),
    decreases hi - lo,
{
    lemma2_to64();
    if hi > lo {
        lemma_bytes_bound(buf, end, lo, hi - 1);
        let p = pow2((8 * (hi - 1 - lo)) as nat);
        lemma_pow2_adds((8 * (hi - 1 - lo)) as nat, 8);
        assert((8 * (hi - 1 - lo)) as nat + 8 == (8 * (hi - lo)) as nat);
        let b = bytes(buf, end, lo, hi - 1);
        let s = sbyte(buf, end, hi - 1);
        assert(b * 256 + s < p * 256) by (nonlinear_arith) requires 0 <= b < p, 0 <= s < 256;
        assert(b * 256 + s >= 0) by (nonlinear_arith) requires 0 <= b, 0 <= s;
    }
}

/// Bytes `lo..hi` are bytes `lo..mid` followed by bytes `mid..hi`.
proof fn lemma_bytes_concat(buf: Seq<u8>, end: nat, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures bytes(buf, end, lo, hi) == bytes(buf, end, lo, mid) * pow2((8 * (hi - mid)) as nat) + bytes(buf, end, mid, hi),
    decreases hi - mid,
{
    lemma2_to64();
    if hi > mid {
        lemma_bytes_concat(buf, end, lo, mid, hi - 1);
        lemma_pow2_adds((8 * (hi - 1 - mid)) as nat, 8);
        assert((8 * (hi - 1 - mid)) as nat + 8 == (8 * (hi - mid)) as nat);
        let a = bytes(buf, end, lo, mid);
        let p = pow2((8 * (hi - 1 - mid)) as nat);
        let c = bytes(buf, end, mid, hi - 1);
        let s = sbyte(buf, end, hi - 1);
        assert(bytes(buf, end, lo, hi) == bytes(buf, end, lo, hi - 1) * 256 + s);
        assert(bytes(buf, end, mid, hi) == c * 256 + s);
        assert((a * p + c) * 256 + s == a * (p * 256) + (c * 256 + s)) by (nonlinear_arith);
    } else {
        assert(pow2(0) == 1);
        assert(bytes(buf, end, mid, hi) == 0);
        assert(bytes(buf, end, lo, mid) * 1 == bytes(buf, end, lo, mid));
    }
}

/// The first of bytes `lo..hi`, and the rest.
proof fn lemma_bytes_head(buf: Seq<u8>, end: nat, lo: int, hi: int)
    requires lo < hi,
    ensures
        bytes(buf, end, lo, hi) == sbyte(buf, end, lo) * pow2((8 * (hi - lo - 1)) as nat) + bytes(buf, end, lo + 1, hi),
        bytes(buf, end, lo, lo + 1) == sbyte(buf, end, lo),
{
    lemma_bytes_concat(buf, end, lo, lo + 1, hi);
    assert(bytes(buf, end, lo, lo + 1) == bytes(buf, end, lo, lo) * 256 + sbyte(buf, end, lo));
}

/// Past `end`, all bytes are 0.
proof fn lemma_bytes_zero(buf: Seq<u8>, end: nat, lo: int, hi: int)
    requires lo >= end,
    ensures bytes(buf, end, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo { lemma_bytes_zero(buf, end, lo, hi - 1); }
}

/// The spec's `value` in the window: the 32 bits above `bits` lookahead
/// bits, with the low `bc` bits cleared (dixie's zeros there, where the
/// window already holds the next byte's bits).
pub open spec fn vwin(v: u64, bits: u64, bc: u32) -> u32 {
    (((v >> bits) as u32) >> bc) << bc
}

/// `x & (2^m - 1)` is `x % 2^m`.
proof fn lemma_mod_mask(v: u64, m: u64)
    requires m < 64,
    ensures
        (v & (((1u64 << m) - 1) as u64)) as int == (v as int) % (pow2(m as nat) as int),
        (1u64 << m) as int == pow2(m as nat),
{
    vstd::bits::lemma_u64_pow2_no_overflow(m as nat);
    vstd::bits::lemma_u64_shl_is_mul(1u64, m);
    vstd::bits::lemma_u64_low_bits_mask_is_mod(v, m as nat);
    assert(1u64 << m >= 1) by (bit_vector) requires m < 64;
    assert((((1u64 << m) - 1) as u64) as nat == vstd::bits::low_bits_mask(m as nat));
}

/// The top byte of `v`'s low `m` bits, and the bits below it.
proof fn lemma_top(v: u64, m: u64, s: int, r: int)
    requires
        8 <= m < 64, 0 <= s < 256, 0 <= r < pow2((m - 8) as nat),
        (v as int) % (pow2(m as nat) as int) == s * pow2((m - 8) as nat) + r,
    ensures
        ((v >> (m - 8) as u64) & 255u64) as int == s,
        (v as int) % (pow2((m - 8) as nat) as int) == r,
{
    let d = pow2((m - 8) as nat) as int;
    let p = pow2(m as nat) as int;
    lemma2_to64();
    lemma_pow2_pos((m - 8) as nat);
    lemma_pow2_adds((m - 8) as nat, 8);
    assert(((m - 8) as nat + 8) == m as nat);
    assert(p == d * 256);
    let x = v as int;
    let q = x / p;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, p);
    assert(x == (q * 256 + s) * d + r) by (nonlinear_arith) requires x == p * q + (s * d + r), p == d * 256;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, d, q * 256 + s, r);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(q * 256 + s, 256, q, s);
    vstd::bits::lemma_u64_pow2_no_overflow((m - 8) as nat);
    vstd::bits::lemma_u64_shr_is_div(v, (m - 8) as u64);
    let t = v >> (m - 8) as u64;
    assert(t & 255u64 == t % 256) by (bit_vector);
}

/// n shifts that take in no byte.
proof fn lemma_win_shift(v: u64, bits: u64, n: u64, bc: u64)
    requires n <= bits <= 32, bc + n < 8,
    ensures vwin(v, (bits - n) as u64, (bc + n) as u32) == vwin(v, bits, bc as u32) << (n as u32),
{
    assert((((v >> (bits - n) as u64) as u32) >> ((bc + n) as u32)) << ((bc + n) as u32)
        == ((((v >> bits) as u32) >> (bc as u32)) << (bc as u32)) << (n as u32)) by (bit_vector)
        requires n <= bits <= 32, bc + n < 8;
}

/// n shifts that take in the byte `s`.
proof fn lemma_win_cross(v: u64, bits: u64, n: u64, bc: u64)
    requires n <= bits <= 32, bc < 8, n <= 7, bc + n >= 8,
    ensures
        vwin(v, (bits - n) as u64, (bc + n - 8) as u32)
            == (vwin(v, bits, bc as u32) << (n as u32)) | ((((v >> (bits + bc - 8) as u64) & 255u64) as u32) << ((bc + n - 8) as u32)),
{
    assert((((v >> (bits - n) as u64) as u32) >> ((bc + n - 8) as u32)) << ((bc + n - 8) as u32)
        == (((((v >> bits) as u32) >> (bc as u32)) << (bc as u32)) << (n as u32))
            | ((((v >> (bits + bc - 8) as u64) & 255u64) as u32) << ((bc + n - 8) as u32))) by (bit_vector)
        requires n <= bits <= 32, bc < 8, n <= 7, bc + n >= 8;
}

/// The comparison against `split * 256` does not see the low bits.
proof fn lemma_win_cmp(w: u32, big: u32, bc: u32)
    requires bc < 8, big & 255u32 == 0,
    ensures (((w >> bc) << bc) >= big) == (w >= big),
{
    assert((((w >> bc) << bc) >= big) == (w >= big)) by (bit_vector) requires bc < 8, big & 255u32 == 0;
}

/// Taking `big` from the window: the low `bits + bc` bits stay.
proof fn lemma_win_sub(v: u64, bits: u64, big: u32, bc: u32)
    requires bits <= 32, bc < 8, big & 255u32 == 0, big < 65536, (v >> bits) as u32 >= big,
    ensures
        v >= (big as u64) << bits,
        vwin((v - ((big as u64) << bits)) as u64, bits, bc) == vwin(v, bits, bc) - big,
        vwin(v, bits, bc) >= big,
        ((v - ((big as u64) << bits)) as u64) & (((1u64 << (bits + bc as u64) as u64) - 1) as u64) == v & (((1u64 << (bits + bc as u64) as u64) - 1) as u64),
{
    lemma_win_cmp((v >> bits) as u32, big, bc);
    assert(v >= (big as u64) << bits) by (bit_vector) requires bits <= 32, (v >> bits) as u32 >= big;
    assert((((((v - ((big as u64) << bits)) as u64) >> bits) as u32) >> bc) << bc == ((((v >> bits) as u32) >> bc) << bc) - big)
        by (bit_vector) requires bits <= 32, bc < 8, big & 255u32 == 0, (v >> bits) as u32 >= big;
    assert(((v - ((big as u64) << bits)) as u64) & (((1u64 << (bits + bc as u64) as u64) - 1) as u64) == v & (((1u64 << (bits + bc as u64) as u64) - 1) as u64))
        by (bit_vector) requires bits <= 32, bc < 8, big & 255u32 == 0, big < 65536, v >= (big as u64) << bits;
}

/// Three more bytes `x` below the window.
proof fn lemma_win_refill(v: u64, bits: u64, bc: u64, x: u64)
    requires bits < 8, bc < 8, x < 0x100_0000,
    ensures
        vwin((v << 24u64) | x, (bits + 24) as u64, bc as u32) == vwin(v, bits, bc as u32),
        (((v << 24u64) | x) & (((1u64 << (bits + bc + 24) as u64) - 1) as u64)) as int
            == ((v & (((1u64 << (bits + bc) as u64) - 1) as u64)) as int) * 0x100_0000 + x as int,
{
    assert((((v << 24u64) | x) >> (bits + 24) as u64) as u32 == (v >> bits) as u32) by (bit_vector)
        requires bits < 8, x < 0x100_0000;
    let t = v & (((1u64 << (bits + bc) as u64) - 1) as u64);
    assert(((v << 24u64) | x) & (((1u64 << (bits + bc + 24) as u64) - 1) as u64) == (t << 24u64) | x) by (bit_vector)
        requires bits < 8, bc < 8, x < 0x100_0000, t == v & (((1u64 << (bits + bc) as u64) - 1) as u64);
    assert(t < 0x1_0000) by (bit_vector) requires bits < 8, bc < 8, t == v & (((1u64 << (bits + bc) as u64) - 1) as u64);
    assert((t << 24u64) | x == (t * 0x100_0000 + x) as u64) by (bit_vector) requires t < 0x1_0000, x < 0x100_0000;
}

/// One of `b_norm`'s shifts, without its test.
pub open spec fn b_step(buf: Seq<u8>, s: BState) -> BState {
    let v = s.value << 1u32;
    let r = (s.range * 2) as u32;
    let bc = s.bit_count + 1;
    if bc == 8 {
        if s.pos < s.end && s.pos < buf.len() {
            BState { pos: s.pos + 1, end: s.end, range: r, value: v | (buf[s.pos as int] as u32), bit_count: 0 }
        } else {
            BState { pos: s.pos, end: s.end, range: r, value: v, bit_count: 0 }
        }
    } else {
        BState { pos: s.pos, end: s.end, range: r, value: v, bit_count: bc as u32 }
    }
}

/// `n` shifts.
pub open spec fn b_steps(buf: Seq<u8>, s: BState, n: nat) -> BState
    decreases n,
{
    if n == 0 { s } else { b_steps(buf, b_step(buf, s), (n - 1) as nat) }
}

/// `n` shifts (1 <= n <= 7) at once: at most one byte comes in.
pub open spec fn b_shift(buf: Seq<u8>, s: BState, n: u32) -> BState {
    let bc = s.bit_count + n;
    if bc >= 8 {
        let k2 = (bc - 8) as u32;
        if s.pos < s.end && s.pos < buf.len() {
            BState { pos: s.pos + 1, end: s.end, range: s.range << n, value: (s.value << n) | ((buf[s.pos as int] as u32) << k2), bit_count: k2 }
        } else {
            BState { pos: s.pos, end: s.end, range: s.range << n, value: s.value << n, bit_count: k2 }
        }
    } else {
        BState { pos: s.pos, end: s.end, range: s.range << n, value: s.value << n, bit_count: bc as u32 }
    }
}

proof fn lemma_bits(v: u32, r: u32, b: u32, n: u32, k2: u32)
    requires 1 <= n <= 7, b < 256, k2 < 8,
    ensures
        (v << 1u32) << (n - 1) as u32 == v << n,
        ((r * 2) as u32) << (n - 1) as u32 == r << n,
        ((r * 2) as u32) == r << 1u32,
        ((v << 1u32) | b) << (n - 1) as u32 == (v << n) | (b << (n - 1) as u32),
        b << 0u32 == b,
{
    assert((v << 1u32) << (n - 1) as u32 == v << n) by (bit_vector) requires 1 <= n <= 7;
    assert(((r * 2) as u32) == r << 1u32) by (bit_vector);
    assert((r << 1u32) << (n - 1) as u32 == r << n) by (bit_vector) requires 1 <= n <= 7;
    assert(((v << 1u32) | b) << (n - 1) as u32 == (v << n) | (b << (n - 1) as u32)) by (bit_vector) requires 1 <= n <= 7;
    assert(b << 0u32 == b) by (bit_vector);
}

/// n shifts one at a time are one shift by n.
proof fn lemma_steps_shift(buf: Seq<u8>, s: BState, n: u32)
    requires 1 <= n <= 7, s.bit_count < 8,
    ensures b_steps(buf, s, n as nat) == b_shift(buf, s, n),
    decreases n,
{
    let s1 = b_step(buf, s);
    let has = s.pos < s.end && s.pos < buf.len();
    let b: u32 = if has { buf[s.pos as int] as u32 } else { 0 };
    let k2: u32 = if s.bit_count + n >= 8 { (s.bit_count + n - 8) as u32 } else { 0 };
    lemma_bits(s.value, s.range, b, n, k2);
    assert(b_steps(buf, s, n as nat) == b_steps(buf, s1, (n - 1) as nat));
    if n == 1 {
        assert(b_steps(buf, s1, 0) == s1);
    } else {
        lemma_steps_shift(buf, s1, (n - 1) as u32);
    }
}

/// 2^n.
pub open spec fn twos(n: int) -> int
    decreases n,
{
    if n <= 0 { 1 } else { 2 * twos(n - 1) }
}

proof fn lemma_twos_pos(n: int)
    ensures twos(n) >= 1,
    decreases n,
{
    if n > 0 { lemma_twos_pos(n - 1); }
}

/// The ranges `b_norm` doubles through: n doublings take r from below 128
/// to 128 and up.
pub open spec fn norm_n(r: int, n: int) -> bool {
    n >= 1 && r >= 1 && r * twos(n - 1) < 128 && r * twos(n) >= 128
}

/// `b_norm` is n shifts, n the doublings the range needs.
proof fn lemma_norm_steps(buf: Seq<u8>, s: BState, n: u32)
    requires 1 <= n <= 7, norm_n(s.range as int, n as int),
    ensures b_norm(buf, s) == b_steps(buf, s, n as nat),
    decreases n,
{
    let r = s.range as int;
    let s1 = b_step(buf, s);
    lemma_twos_pos(n - 1);
    assert(r < 128) by (nonlinear_arith) requires r * twos(n - 1) < 128, twos(n - 1) >= 1, r >= 1;
    assert(b_norm(buf, s) == b_norm(buf, s1));
    assert(s1.range == 2 * s.range);
    if n == 1 {
        assert(twos(1) == 2 * twos(0));
        assert(s1.range >= 128);
        assert(b_steps(buf, s1, 0) == s1);
    } else {
        assert(twos(n - 1) == 2 * twos(n - 2));
        assert(twos(n as int) == 2 * twos(n - 1));
        assert((2 * r) * twos(n - 2) == r * twos(n - 1)) by (nonlinear_arith) requires twos(n - 1) == 2 * twos(n - 2);
        assert((2 * r) * twos(n - 1) == r * twos(n as int)) by (nonlinear_arith) requires twos(n as int) == 2 * twos(n - 1);
        assert(norm_n(s1.range as int, (n - 1) as int));
        lemma_norm_steps(buf, s1, (n - 1) as u32);
    }
    assert(b_steps(buf, s, n as nat) == b_steps(buf, s1, (n - 1) as nat));
}

/// A range of 128 and up has no leading zeros.
proof fn lemma_lz0(r: u8)
    requires 128 <= r,
    ensures r.leading_zeros() == 0,
{
    vstd::std_specs::bits::axiom_u8_leading_zeros(r);
    let n = r.leading_zeros();
    if n != 0 {
        assert(n <= 8);
        if n == 8 { assert(r == 0); }
        else {
            assert(sub(8u8, n as u8) <= 7u8);
            assert(r >> sub(8u8, n as u8) == 0u8);
            let k = sub(8u8, n as u8);
            assert(k <= 7u8 && r >> k == 0u8 ==> r < 128u8) by (bit_vector);
        }
    }
}

/// The leading zeros of a range below 128 are its doublings.
proof fn lemma_lz(r: u8)
    requires 1 <= r < 128,
    ensures 1 <= r.leading_zeros() <= 7, norm_n(r as int, r.leading_zeros() as int),
        128 <= (r as u32) << r.leading_zeros() <= 255,
{
    reveal_with_fuel(twos, 8);
    vstd::std_specs::bits::axiom_u8_leading_zeros(r);
    let n = r.leading_zeros();
    let x = r as u32;
    assert(r != 0);
    assert(n < 8);
    assert((r >> 7u8) & 1u8 == 0u8) by (bit_vector) requires r < 128u8;
    if n == 0 {
        assert(sub(7u8, 0u8) == 7u8);
    } else if n == 1 {
        assert(sub(7u8, 1u8) == 6u8);
        assert(64 <= r) by (bit_vector) requires (r >> 6u8) & 1u8 != 0u8;
        assert(128 <= x << 1u32 <= 255) by (bit_vector) requires 64 <= x < 128;
        assert(twos(0) == 1 && twos(1) == 2);
        assert((r as int) * twos(0) < 128 && (r as int) * twos(1) >= 128) by (nonlinear_arith)
            requires twos(0) == 1, twos(1) == 2, 64 <= r as int, r as int <= 127;
        assert(norm_n(r as int, 1));
    } else if n == 2 {
        assert(sub(7u8, 2u8) == 5u8 && sub(8u8, 2u8) == 6u8);
        assert(32 <= r < 64) by (bit_vector) requires (r >> 5u8) & 1u8 != 0u8, r >> 6u8 == 0u8;
        assert(128 <= x << 2u32 <= 255) by (bit_vector) requires 32 <= x < 64;
        assert(twos(1) == 2 && twos(2) == 4);
        assert((r as int) * twos(1) < 128 && (r as int) * twos(2) >= 128) by (nonlinear_arith)
            requires twos(1) == 2, twos(2) == 4, 32 <= r as int, r as int <= 63;
        assert(norm_n(r as int, 2));
    } else if n == 3 {
        assert(sub(7u8, 3u8) == 4u8 && sub(8u8, 3u8) == 5u8);
        assert(16 <= r < 32) by (bit_vector) requires (r >> 4u8) & 1u8 != 0u8, r >> 5u8 == 0u8;
        assert(128 <= x << 3u32 <= 255) by (bit_vector) requires 16 <= x < 32;
        assert(twos(2) == 4 && twos(3) == 8);
        assert((r as int) * twos(2) < 128 && (r as int) * twos(3) >= 128) by (nonlinear_arith)
            requires twos(2) == 4, twos(3) == 8, 16 <= r as int, r as int <= 31;
        assert(norm_n(r as int, 3));
    } else if n == 4 {
        assert(sub(7u8, 4u8) == 3u8 && sub(8u8, 4u8) == 4u8);
        assert(8 <= r < 16) by (bit_vector) requires (r >> 3u8) & 1u8 != 0u8, r >> 4u8 == 0u8;
        assert(128 <= x << 4u32 <= 255) by (bit_vector) requires 8 <= x < 16;
        assert(twos(3) == 8 && twos(4) == 16);
        assert((r as int) * twos(3) < 128 && (r as int) * twos(4) >= 128) by (nonlinear_arith)
            requires twos(3) == 8, twos(4) == 16, 8 <= r as int, r as int <= 15;
        assert(norm_n(r as int, 4));
    } else if n == 5 {
        assert(sub(7u8, 5u8) == 2u8 && sub(8u8, 5u8) == 3u8);
        assert(4 <= r < 8) by (bit_vector) requires (r >> 2u8) & 1u8 != 0u8, r >> 3u8 == 0u8;
        assert(128 <= x << 5u32 <= 255) by (bit_vector) requires 4 <= x < 8;
        assert(twos(4) == 16 && twos(5) == 32);
        assert((r as int) * twos(4) < 128 && (r as int) * twos(5) >= 128) by (nonlinear_arith)
            requires twos(4) == 16, twos(5) == 32, 4 <= r as int, r as int <= 7;
        assert(norm_n(r as int, 5));
    } else if n == 6 {
        assert(sub(7u8, 6u8) == 1u8 && sub(8u8, 6u8) == 2u8);
        assert(2 <= r < 4) by (bit_vector) requires (r >> 1u8) & 1u8 != 0u8, r >> 2u8 == 0u8;
        assert(128 <= x << 6u32 <= 255) by (bit_vector) requires 2 <= x < 4;
        assert(twos(5) == 32 && twos(6) == 64);
        assert((r as int) * twos(5) < 128 && (r as int) * twos(6) >= 128) by (nonlinear_arith)
            requires twos(5) == 32, twos(6) == 64, 2 <= r as int, r as int <= 3;
        assert(norm_n(r as int, 6));
    } else {
        assert(sub(8u8, 7u8) == 1u8);
        assert(r < 2) by (bit_vector) requires r >> 1u8 == 0u8;
        assert(128 <= x << 7u32 <= 255) by (bit_vector) requires 1 <= x < 2;
        assert(twos(6) == 64 && twos(7) == 128);
        assert((r as int) * twos(6) < 128 && (r as int) * twos(7) >= 128) by (nonlinear_arith)
            requires twos(6) == 64, twos(7) == 128, 1 <= r as int, r as int <= 1;
        assert(norm_n(r as int, 7));
    }
}

/// The bool decoder, reading ahead through a 64-bit window, as libwebp's
/// VP8GetBit does. Above the low `bits` bits of `v` is dixie's `value`
/// (its low 32 bits); the `bits` below are the stream read ahead.
pub struct Bd<'a> {
    pub buf: &'a [u8],
    pub end: usize,
    /// Bytes of `buf` taken into `v`.
    pub ld: usize,
    /// Zero bytes taken into `v` past `end` (less those dropped again).
    pub vz: usize,
    pub v: u64,
    pub bits: u64,
    pub range: u32,
}

impl<'a> Bd<'a> {
    /// The stream bits consumed: those taken in, less those read ahead.
    pub closed spec fn cb(&self) -> int { 8 * (self.ld + self.vz) - self.bits }

    pub closed spec fn vpos(&self) -> int { self.cb() / 8 }

    pub closed spec fn bc(&self) -> int { self.cb() % 8 }

    pub closed spec fn view(&self) -> BState {
        BState {
            pos: if self.vpos() < self.end { self.vpos() as nat } else { self.end as nat },
            end: self.end as nat,
            range: self.range,
            value: vwin(self.v, self.bits, self.bc() as u32),
            bit_count: self.bc() as u32,
        }
    }

    /// All but the range's bounds: the window's low `bits + bc` bits are
    /// the bytes from `vpos` on that it has taken in.
    pub closed spec fn inv(&self) -> bool {
        &&& self.end <= self.buf@.len()
        &&& self.ld <= self.end
        &&& self.vz > 0 ==> self.ld == self.end
        &&& self.vz <= 6
        &&& self.bits <= 32
        &&& 8 * (self.ld + self.vz) >= self.bits
        &&& (self.v as int) % (pow2((self.bits + self.bc()) as nat) as int)
            == bytes(self.buf@, self.end as nat, self.vpos(), self.ld + self.vz)
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.inv()
        &&& 128 <= self.range <= 255
    }

    /// `bc` and `vpos` from the bits consumed.
    proof fn lemma_cb(&self, q: int, b: int)
        requires self.cb() == 8 * q + b, 0 <= b < 8,
        ensures self.vpos() == q, self.bc() == b,
    {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(self.cb(), 8, q, b);
    }

    /// init_bool_decoder.
    pub fn new(buf: &'a [u8]) -> (r: Self)
        ensures r.view() == b_init(buf@), r.wf(), r.buf@ == buf@,
    {
        proof { lemma2_to64(); }
        if buf.len() >= 2 {
            let b0 = buf[0];
            let b1 = buf[1];
            let v = ((b0 as u64) << 8u64) | (b1 as u64);
            let r = Bd { buf, end: buf.len(), ld: 2, vz: 0, v, bits: 0, range: 255 };
            proof {
                r.lemma_cb(2, 0);
                assert(vwin(v, 0, 0) == ((b0 as u32) << 8u32) | (b1 as u32)) by (bit_vector)
                    requires v == ((b0 as u64) << 8u64) | (b1 as u64);
            }
            r
        } else {
            let r = Bd { buf, end: 0, ld: 0, vz: 0, v: 0, bits: 0, range: 255 };
            proof {
                r.lemma_cb(0, 0);
                assert(vwin(0, 0, 0) == 0) by (bit_vector);
            }
            r
        }
    }

    /// The reader of a spec state saved without its buffer.
    pub fn from_st(buf: &'a [u8], st: (usize, usize, u32, u32, u32)) -> (r: Self)
        requires st.0 <= st.1 <= buf@.len(), 128 <= st.2 <= 255, st.4 < 8, (st.3 >> st.4) << st.4 == st.3,
        ensures
            r.wf(), r.buf@ == buf@,
            r.view() == (BState { pos: st.0 as nat, end: st.1 as nat, range: st.2, value: st.3, bit_count: st.4 }),
    {
        let (pos, end, range, value, bc) = st;
        let has = pos < end;
        let x: u64 = if has { buf[pos] as u64 } else { 0 };
        let ld = if has { pos + 1 } else { end };
        let vz: usize = if has { 0 } else { 1 };
        let v = (((value >> bc) as u64) << 8u64) | x;
        let bits = (8 - bc) as u64;
        let r = Bd { buf, end, ld, vz, v, bits, range };
        proof {
            lemma2_to64();
            r.lemma_cb(pos as int, bc as int);
            assert(vwin(v, bits, bc) == value) by (bit_vector)
                requires v == (((value >> bc) as u64) << 8u64) | x, x < 256, bc < 8, bits == (8 - bc) as u64, (value >> bc) << bc == value;
            assert(v & 255u64 == x) by (bit_vector) requires v == (((value >> bc) as u64) << 8u64) | x, x < 256;
            lemma_mod_mask(v, 8);
            assert((1u64 << 8u64) - 1 == 255) by (bit_vector);
            lemma_bytes_head(buf@, end as nat, pos as int, pos + 1);
        }
        r
    }

    /// The spec state, saved without its buffer.
    pub fn to_st(&self) -> (r: (usize, usize, u32, u32, u32))
        requires self.wf(),
        ensures
            r.0 as nat == self.view().pos, r.1 as nat == self.view().end, r.2 == self.view().range,
            r.3 == self.view().value, r.4 == self.view().bit_count,
            r.0 <= r.1 <= self.buf@.len(), 128 <= r.2 <= 255, r.4 < 8, (r.3 >> r.4) << r.4 == r.3,
    {
        let q = (self.bits + 7) / 8;
        let bc = (8 * q - self.bits) as u32;
        let qq = q as usize;
        proof { self.lemma_cb(self.ld + self.vz - q, bc as int); }
        let pos = if self.vz > 0 && self.vz >= qq { self.end } else { self.ld - (qq - self.vz) };
        let w = (self.v >> self.bits) as u32;
        let value = (w >> bc) << bc;
        proof { assert(((value >> bc) << bc) == value) by (bit_vector) requires value == (w >> bc) << bc, bc < 8; }
        (pos, self.end, self.range, value, bc)
    }

    /// Three more bytes into the window, when fewer than 8 bits are ahead.
    #[inline(always)]
    fn refill(&mut self)
        requires old(self).inv(), old(self).bits < 8,
        ensures
            final(self).inv(), final(self).view() == old(self).view(), final(self).buf@ == old(self).buf@,
            final(self).range == old(self).range, 8 <= final(self).bits,
    {
        let ghost buf = self.buf@;
        let ghost s0 = self.view();
        let ghost vpos = self.vpos();
        let ghost bc = self.bc();
        let ghost ll = self.ld + self.vz;
        let ghost e = self.end as nat;
        let v0 = self.v;
        let bits = self.bits;
        let ld = self.ld;
        let end = self.end;
        proof {
            lemma2_to64();
            lemma_mod_mask(v0, (bits + bc) as u64);
        }
        if end - ld >= 3 || self.vz < 4 {
            let r = end - ld;
            let x: u64 = if r >= 3 {
                ((vsimd::mem::get(self.buf, ld) as u64) << 16u64) | ((vsimd::mem::get(self.buf, ld + 1) as u64) << 8u64) | (vsimd::mem::get(self.buf, ld + 2) as u64)
            } else {
                let b0: u64 = if r > 0 { vsimd::mem::get(self.buf, ld) as u64 } else { 0 };
                let b1: u64 = if r > 1 { vsimd::mem::get(self.buf, ld + 1) as u64 } else { 0 };
                (b0 << 16u64) | (b1 << 8u64)
            };
            proof {
                let s0b = sbyte(buf, e, ll);
                let s1b = sbyte(buf, e, ll + 1);
                let s2b = sbyte(buf, e, ll + 2);
                assert(bytes(buf, e, ll, ll + 1) == bytes(buf, e, ll, ll) * 256 + s0b);
                assert(bytes(buf, e, ll, ll + 2) == bytes(buf, e, ll, ll + 1) * 256 + s1b);
                assert(bytes(buf, e, ll, ll + 3) == bytes(buf, e, ll, ll + 2) * 256 + s2b);
                let c0 = s0b as u64;
                let c1 = s1b as u64;
                let c2 = s2b as u64;
                if r >= 3 {
                    assert(ll == ld);
                    assert(c0 == buf[ld as int] as u64 && c1 == buf[ld + 1] as u64 && c2 == buf[ld + 2] as u64);
                } else {
                    assert(c2 == 0);
                    if r > 1 { assert(ll == ld && c1 == buf[ld + 1] as u64); } else { assert(c1 == 0); }
                    if r > 0 { assert(ll == ld && c0 == buf[ld as int] as u64); } else { assert(c0 == 0); }
                    assert(c2 << 0u64 == c2 && (c0 << 16u64) | (c1 << 8u64) == (c0 << 16u64) | (c1 << 8u64) | 0u64) by (bit_vector);
                }
                assert(x == (c0 << 16u64) | (c1 << 8u64) | c2);
                assert((c0 << 16u64) | (c1 << 8u64) | c2 == c0 * 65536 + c1 * 256 + c2 && (c0 * 65536 + c1 * 256 + c2) < 0x100_0000)
                    by (bit_vector) requires c0 < 256, c1 < 256, c2 < 256;
                lemma_win_refill(v0, bits, bc as u64, x);
                lemma_mod_mask((v0 << 24u64) | x, (bits + bc + 24) as u64);
                lemma_bytes_concat(buf, e, vpos, ll, ll + 3);
            }
            self.v = (v0 << 24u64) | x;
            if r >= 3 {
                self.ld = ld + 3;
            } else {
                self.ld = end;
                self.vz = self.vz + 3 - r;
            }
            self.bits = bits + 24;
            proof { self.lemma_cb(vpos, bc); }
        } else {
            // Four zero bytes and more past `end` are ahead: the window takes
            // in three more, and the same three drop from the count.
            proof {
                lemma_win_refill(v0, bits, bc as u64, 0);
                assert((v0 << 24u64) | 0u64 == v0 << 24u64) by (bit_vector);
                lemma_mod_mask(v0 << 24u64, (bits + bc + 24) as u64);
                lemma_bytes_zero(buf, e, vpos, ll);
                lemma_bytes_zero(buf, e, vpos - 3, ll);
            }
            self.v = v0 << 24u64;
            self.bits = bits + 24;
            proof { self.lemma_cb(vpos - 3, bc); }
        }
    }

    /// The shifts at the end of bool_get (`b_norm`): by the range's leading
    /// zeros, with no branch; bytes come in through `refill` only.
    #[inline(always)]
    fn norm(&mut self)
        requires old(self).inv(), 1 <= old(self).range <= 255, 7 <= old(self).bits,
        ensures final(self).view() == b_norm(old(self).buf@, old(self).view()), final(self).wf(), final(self).buf@ == old(self).buf@,
    {
        let ghost s0 = self.view();
        let ghost buf = self.buf@;
        let ghost vpos = self.vpos();
        let ghost bc = self.bc();
        let ghost ll = self.ld + self.vz;
        let ghost e = self.end as nat;
        let r0 = self.range;
        let n = (r0 as u8).leading_zeros();
        let bits = self.bits;
        let v = self.v;
        proof {
            if r0 >= 128 {
                lemma_lz0(r0 as u8);
            } else {
                lemma_lz(r0 as u8);
                lemma_norm_steps(buf, s0, n);
                lemma_steps_shift(buf, s0, n);
            }
            assert(r0 << 0u32 == r0) by (bit_vector);
        }
        self.range = r0 << n;
        self.bits = bits - n as u64;
        proof {
            let n64 = n as u64;
            if bc + n < 8 {
                self.lemma_cb(vpos, bc + n);
                lemma_win_shift(v, bits, n64, bc as u64);
            } else {
                let m = (bits + bc) as u64;
                self.lemma_cb(vpos + 1, bc + n - 8);
                lemma_win_cross(v, bits, n64, bc as u64);
                lemma_bytes_head(buf, e, vpos, ll);
                lemma_bytes_bound(buf, e, vpos + 1, ll);
                assert((8 * (ll - vpos - 1)) as nat == (m - 8) as nat);
                lemma_top(v, m, sbyte(buf, e, vpos), bytes(buf, e, vpos + 1, ll));
                let k2 = (bc + n - 8) as u32;
                let a = vwin(v, bits, bc as u32);
                assert((a << n) | (0u32 << k2) == a << n) by (bit_vector);
            }
        }
    }

    /// bool_get.
    #[inline(always)]
    pub fn get(&mut self, prob: u8) -> (b: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@ == old(self).buf@,
            (b, final(self).view()) == b_get(old(self).buf@, old(self).view(), prob),
    {
        if self.bits < 8 {
            self.refill();
        }
        let ghost s0 = self.view();
        let ghost bc = self.bc() as u32;
        let ghost m64 = (self.bits + bc) as u64;
        proof {
            reveal(b_get);
            assert((self.range - 1) * (prob as u32) <= 65025) by (nonlinear_arith)
                requires 128 <= self.range <= 255, prob <= 255;
        }
        // libwebp's order: split - 1, and the window's top 24 bits against it.
        let prod: u32 = (self.range - 1) * (prob as u32);
        let s1: u32 = prod >> 8u32;
        proof { assert(prod >> 8u32 == prod / 256u32) by (bit_vector); }
        let split: u32 = s1 + 1;
        proof {
            let r = self.range as int;
            assert(((r - 1) * prob) / 256 < r - 1) by (nonlinear_arith) requires 128 <= r <= 255, 0 <= prob <= 255;
            assert(((r - 1) * prob) / 256 >= 0) by (nonlinear_arith) requires 128 <= r <= 255, 0 <= prob <= 255;
        }
        let big: u32 = split * 256;
        let v = self.v;
        let bits = self.bits;
        let w = (v >> bits) as u32;
        proof {
            assert(big & 255u32 == 0 && big < 65536) by (bit_vector) requires big == split * 256, split < 256;
            lemma_win_cmp(w, big, bc);
            assert(((w >> 8u32) > s1) == (w >= big)) by (bit_vector) requires big == split * 256, split == s1 + 1, s1 < 255;
        }
        if (w >> 8u32) > s1 {
            proof {
                lemma_win_sub(v, bits, big, bc);
                lemma_mod_mask(v, m64);
                lemma_mod_mask((v - ((big as u64) << bits)) as u64, m64);
            }
            proof {
                assert((big as u64) << bits == (split as u64) << add(bits, 8u64)) by (bit_vector)
                    requires big == split * 256, split < 256, bits <= 32;
            }
            self.range = self.range - split;
            self.v = v - ((split as u64) << (bits + 8));
            self.norm();
            true
        } else {
            self.range = split;
            self.norm();
            false
        }
    }

    #[inline(always)]
    pub fn bit(&mut self) -> (b: bool)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).buf@ == old(self).buf@,
            (b, final(self).view()) == b_bit(old(self).buf@, old(self).view()),
    {
        self.get(128)
    }

    /// A bool at probability 128, as a sign: -v if it is 1, else v (libwebp's
    /// VP8GetSigned), with no branch on the bool.
    #[inline(always)]
    pub fn signed(&mut self, v: i32) -> (r: i32)
        requires old(self).wf(), 0 <= v <= 1100000,
        ensures
            final(self).wf(), final(self).buf@ == old(self).buf@,
            ({ let (b, s) = b_bit(old(self).buf@, old(self).view()); r as int == (if b { -(v as int) } else { v as int }) && final(self).view() == s }),
    {
        if self.bits < 8 {
            self.refill();
        }
        let ghost bc = self.bc() as u32;
        let ghost mm = (self.bits + bc) as u64;
        proof { reveal(b_get); }
        let r0 = self.range;
        let r1 = r0 + 1;
        let split: u32 = r1 >> 1u32;
        proof {
            assert(split as int == (r1 as int) / 2) by (bit_vector) requires split == r1 >> 1u32;
            assert((r1 as int) / 2 == 1 + ((r0 as int - 1) * 128) / 256);
        }
        let big: u32 = split * 256;
        let v0 = self.v;
        let bits = self.bits;
        let w = (v0 >> bits) as u32;
        let m: u32 = if w >= big { 0xffff_ffffu32 } else { 0 };
        let d = r0 - split;
        let nr = (d & m) | (split & !m);
        let bm = big & m;
        proof {
            assert(m == 0xffff_ffffu32 ==> nr == d && bm == big) by (bit_vector) requires nr == (d & m) | (split & !m), bm == big & m;
            assert(m == 0u32 ==> nr == split && bm == 0u32) by (bit_vector) requires nr == (d & m) | (split & !m), bm == big & m;
            assert(big & 255u32 == 0 && big < 65536) by (bit_vector) requires big == split * 256, split < 256;
            assert(bm & 255u32 == 0 && bm < 65536) by (bit_vector) requires bm == big & m, big & 255u32 == 0, big < 65536;
            lemma_win_cmp(w, big, bc);
            lemma_win_sub(v0, bits, bm, bc);
            lemma_mod_mask(v0, mm);
            lemma_mod_mask((v0 - ((bm as u64) << bits)) as u64, mm);
        }
        self.range = nr;
        self.v = v0 - ((bm as u64) << bits);
        self.norm();
        let sm = m as i32;
        let x = v ^ sm;
        proof {
            assert(m == 0xffff_ffffu32 ==> sm == -1i32) by (bit_vector) requires sm == m as i32;
            assert(m == 0u32 ==> sm == 0i32) by (bit_vector) requires sm == m as i32;
            assert(sm == -1i32 ==> x == !v) by (bit_vector) requires x == v ^ sm;
            assert(sm == 0i32 ==> x == v) by (bit_vector) requires x == v ^ sm;
            assert(0 <= v <= 1100000 ==> (!v) as int == -(v as int) - 1) by (bit_vector);
        }
        x - sm
    }

    /// bool_get_uint, `n` <= 16 bits.
    pub fn uint(&mut self, n: u32) -> (r: u32)
        requires old(self).wf(), n <= 16,
        ensures
            final(self).wf(), final(self).buf@ == old(self).buf@,
            (r as int, final(self).view()) == b_uint(old(self).buf@, old(self).view(), n as nat),
            r < 65536,
    {
        let ghost buf = self.buf@;
        let ghost s0 = self.view();
        let mut v: u32 = 0;
        let mut i: u32 = 0;
        proof { assert((1u32 << 0u32) == 1) by (bit_vector); }
        while i < n
            invariant
                self.wf(), self.buf@ == buf, i <= n, n <= 16,
                (v as int, self.view()) == b_uint(buf, s0, i as nat),
                v < (1u32 << i),
            decreases n - i,
        {
            let b = self.bit();
            proof {
                assert((1u32 << (i + 1) as u32) == 2 * (1u32 << i)) by (bit_vector) requires i < 16;
                assert(b_uint(buf, s0, (i + 1) as nat) == ({
                    let (vv, s1) = b_uint(buf, s0, i as nat);
                    let (bb, s2) = b_bit(buf, s1);
                    (2 * vv + if bb { 1int } else { 0 }, s2)
                }));
            }
            v = 2 * v + if b { 1 } else { 0 };
            i = i + 1;
        }
        proof { assert((1u32 << n) <= 65536) by (bit_vector) requires n <= 16; }
        v
    }

    /// bool_get_int.
    pub fn int(&mut self, n: u32) -> (r: i32)
        requires old(self).wf(), n <= 16,
        ensures
            final(self).wf(), final(self).buf@ == old(self).buf@,
            (r as int, final(self).view()) == b_int(old(self).buf@, old(self).view(), n as nat),
            -65536 < r < 65536,
    {
        let v = self.uint(n) as i32;
        if self.bit() { -v } else { v }
    }

    /// bool_maybe_get_int.
    pub fn maybe(&mut self, n: u32) -> (r: i32)
        requires old(self).wf(), n <= 16,
        ensures
            final(self).wf(), final(self).buf@ == old(self).buf@,
            (r as int, final(self).view()) == b_maybe(old(self).buf@, old(self).view(), n as nat),
            -65536 < r < 65536,
    {
        if self.bit() { self.int(n) } else { 0 }
    }
}

} // verus!
