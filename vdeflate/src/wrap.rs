//! The zlib (RFC 1950) and gzip (RFC 1952) formats around a DEFLATE stream,
//! and their checksums, Adler-32 and CRC-32.
//!
//! Both are specified over the bytes. The DEFLATE stream is the spec's
//! `inflate` of the bytes after the header; the trailer starts at the next
//! byte boundary after it.
//!
//! zlib: CMF, FLG with CM = 8, CINFO <= 7 and CMF * 256 + FLG a multiple of
//! 31; FDICT (a preset dictionary) is refused, as zlib does without one.
//! The trailer is the data's Adler-32, most significant byte first.
//!
//! gzip: one member. ID1 ID2 = 1f 8b, CM = 8, FLG with bits 5 to 7 clear,
//! MTIME, XFL, OS; then FEXTRA's XLEN and bytes, FNAME and FCOMMENT up to a
//! zero byte, and FHCRC (the low 16 bits of the header's CRC-32), if their
//! flags are set. The trailer is the data's CRC-32 and its length modulo
//! 2^32, least significant byte first.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::lsb::lbits;
use crate::spec::*;
use crate::inflate::*;
#[cfg(all(target_arch = "x86_64", verus_keep_ghost))] // spec-only: erased from a plain build
use vsimd::x86::v8;
#[cfg(target_arch = "x86_64")]
use vsimd::x86::{__m128i, setzero, from_bytes, to_bytes, loadu, add_epi32, sad_epu8, madd_epi16, unpacklo_epi8, unpackhi_epi8};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::huff::max_input;

verus! {

// ------------------------------------------------------------ Adler-32

pub open spec fn adler_mod() -> nat { 65521 }

/// Adler-32's sums, unreduced: A is 1 plus the bytes, B the sum of each A.
pub open spec fn adler_a(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 1 } else { adler_a(s.drop_last()) + s.last() as nat }
}

pub open spec fn adler_b(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { adler_b(s.drop_last()) + adler_a(s) }
}

/// RFC 1950 8.2.
pub open spec fn adler32(s: Seq<u8>) -> nat {
    (adler_b(s) % adler_mod()) * 65536 + adler_a(s) % adler_mod()
}

pub fn adler32_x(s: &[u8]) -> (r: u32)
    ensures r as nat == adler32(s@),
{
    proof {
        assert(adler_a(Seq::<u8>::empty()) == 1);
        assert(adler_b(Seq::<u8>::empty()) == 0);
        assert(Seq::<u8>::empty() + s@ =~= s@);
    }
    let (a, b) = adler_run_x(1, 0, s, Ghost(Seq::empty()));
    proof { assert(a < 65521 && b < 65521); }
    ((b as u64) * 65536 + (a as u64)) as u32
}

// -------------------------------------------------------------- CRC-32

/// One bit of CRC-32 (reflected, polynomial 0xEDB88320).
pub open spec fn crc_bit(c: u32) -> u32 {
    if c & 1 == 1 { (c >> 1) ^ 0xEDB8_8320 } else { c >> 1 }
}

/// One byte: its eight bits, least significant first.
pub open spec fn crc_byte(c: u32, x: u8) -> u32 {
    let c0 = c ^ (x as u32);
    crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(c0))))))))
}

pub open spec fn crc_run(c: u32, s: Seq<u8>) -> u32
    decreases s.len(),
{
    if s.len() == 0 { c } else { crc_byte(crc_run(c, s.drop_last()), s.last()) }
}

/// RFC 1952 8: CRC-32, starting from all ones and inverted at the end.
pub open spec fn crc32(s: Seq<u8>) -> u32 {
    crc_run(0xFFFF_FFFF, s) ^ 0xFFFF_FFFF
}

proof fn lemma_crc_table_step(c: u32, x: u8, t: u32)
    requires t == crc_byte(0, ((c ^ (x as u32)) & 0xff) as u8),
    ensures crc_byte(c, x) == t ^ (c >> 8),
{
    let x32 = x as u32;
    let v = ((c ^ x32) & 0xff) as u8;
    assert(v as u32 == (c ^ x32) & 0xff) by (bit_vector) requires v == ((c ^ x32) & 0xff) as u8;
    let c0 = c ^ x32;
    let d0 = 0u32 ^ (v as u32);
    assert(d0 == c0 & 0xff) by (bit_vector) requires d0 == 0u32 ^ (v as u32), v as u32 == c0 & 0xff;
    assert(c0 >> 8 == c >> 8) by (bit_vector) requires c0 == c ^ x32, x32 < 256;
    lemma_crc8_linear(c0, d0, c >> 8);
}

/// Eight CRC bits are linear: shifting in `c0` is shifting in its low byte
/// and xoring the high bytes, shifted.
proof fn lemma_crc8_linear(c0: u32, d0: u32, h: u32)
    requires d0 == c0 & 0xff, h == (c0 >> 8),
    ensures crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(c0))))))))
        == crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(d0)))))))) ^ h,
{
    let c1 = crc_bit(c0); let c2 = crc_bit(c1); let c3 = crc_bit(c2); let c4 = crc_bit(c3);
    let c5 = crc_bit(c4); let c6 = crc_bit(c5); let c7 = crc_bit(c6); let c8 = crc_bit(c7);
    let d1 = crc_bit(d0); let d2 = crc_bit(d1); let d3 = crc_bit(d2); let d4 = crc_bit(d3);
    let d5 = crc_bit(d4); let d6 = crc_bit(d5); let d7 = crc_bit(d6); let d8 = crc_bit(d7);
    assert(c8 == d8 ^ h) by (bit_vector)
        requires
            d0 == c0 & 0xff, h == (c0 >> 8),
            c1 == (if c0 & 1 == 1 { (c0 >> 1) ^ 0xEDB8_8320u32 } else { c0 >> 1 }),
            c2 == (if c1 & 1 == 1 { (c1 >> 1) ^ 0xEDB8_8320u32 } else { c1 >> 1 }),
            c3 == (if c2 & 1 == 1 { (c2 >> 1) ^ 0xEDB8_8320u32 } else { c2 >> 1 }),
            c4 == (if c3 & 1 == 1 { (c3 >> 1) ^ 0xEDB8_8320u32 } else { c3 >> 1 }),
            c5 == (if c4 & 1 == 1 { (c4 >> 1) ^ 0xEDB8_8320u32 } else { c4 >> 1 }),
            c6 == (if c5 & 1 == 1 { (c5 >> 1) ^ 0xEDB8_8320u32 } else { c5 >> 1 }),
            c7 == (if c6 & 1 == 1 { (c6 >> 1) ^ 0xEDB8_8320u32 } else { c6 >> 1 }),
            c8 == (if c7 & 1 == 1 { (c7 >> 1) ^ 0xEDB8_8320u32 } else { c7 >> 1 }),
            d1 == (if d0 & 1 == 1 { (d0 >> 1) ^ 0xEDB8_8320u32 } else { d0 >> 1 }),
            d2 == (if d1 & 1 == 1 { (d1 >> 1) ^ 0xEDB8_8320u32 } else { d1 >> 1 }),
            d3 == (if d2 & 1 == 1 { (d2 >> 1) ^ 0xEDB8_8320u32 } else { d2 >> 1 }),
            d4 == (if d3 & 1 == 1 { (d3 >> 1) ^ 0xEDB8_8320u32 } else { d3 >> 1 }),
            d5 == (if d4 & 1 == 1 { (d4 >> 1) ^ 0xEDB8_8320u32 } else { d4 >> 1 }),
            d6 == (if d5 & 1 == 1 { (d5 >> 1) ^ 0xEDB8_8320u32 } else { d5 >> 1 }),
            d7 == (if d6 & 1 == 1 { (d6 >> 1) ^ 0xEDB8_8320u32 } else { d6 >> 1 }),
            d8 == (if d7 & 1 == 1 { (d7 >> 1) ^ 0xEDB8_8320u32 } else { d7 >> 1 });
}

/// `k` CRC bits.
pub open spec fn crc_bits(c: u32, k: nat) -> u32
    decreases k,
{
    if k == 0 { c } else { crc_bit(crc_bits(c, (k - 1) as nat)) }
}

/// The byte table: `t[i]` is eight CRC bits of `i`.
pub fn crc_table() -> (t: [u32; 256])
    ensures forall|i: int| 0 <= i < 256 ==> #[trigger] t[i] == crc_byte(0, i as u8),
{
    let mut t = [0u32; 256];
    let mut i: usize = 0;
    while i < 256
        invariant i <= 256, forall|j: int| 0 <= j < i ==> #[trigger] t[j] == crc_byte(0, j as u8),
        decreases 256 - i,
    {
        let mut c: u32 = i as u32;
        let ghost c0 = c;
        let mut k: u64 = 0;
        while k < 8
            invariant k <= 8, c == crc_bits(c0, k as nat),
            decreases 8 - k,
        {
            c = if c & 1 == 1 { (c >> 1) ^ 0xEDB8_8320 } else { c >> 1 };
            k = k + 1;
        }
        proof {
            assert(0u32 ^ ((i as u8) as u32) == i as u32) by (bit_vector) requires i < 256;
            reveal_with_fuel(crc_bits, 9);
        }
        t[i] = c;
        i = i + 1;
    }
    t
}

// ------------------------------------------- CRC-32, eight bytes a step

/// Eight CRC bits: what a byte does to the register, after it is xored in
/// (`crc_byte(c, x) == crc8(c ^ x)`).
spec fn crc8(a: u32) -> u32 {
    crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(crc_bit(a))))))))
}

/// `crc8` applied `m` times.
spec fn fpow(a: u32, m: nat) -> u32
    decreases m,
{
    if m == 0 { a } else { crc8(fpow(a, (m - 1) as nat)) }
}

/// A CRC bit is linear over GF(2).
proof fn lemma_bit_lin(a: u32, b: u32)
    ensures crc_bit(a ^ b) == crc_bit(a) ^ crc_bit(b),
{
    let ab = a ^ b;
    let ca = crc_bit(a);
    let cb = crc_bit(b);
    let cab = crc_bit(ab);
    assert(cab == ca ^ cb) by (bit_vector)
        requires
            ab == a ^ b,
            ca == (if a & 1 == 1 { (a >> 1) ^ 0xEDB8_8320u32 } else { a >> 1 }),
            cb == (if b & 1 == 1 { (b >> 1) ^ 0xEDB8_8320u32 } else { b >> 1 }),
            cab == (if ab & 1 == 1 { (ab >> 1) ^ 0xEDB8_8320u32 } else { ab >> 1 });
}

proof fn lemma_crc8_lin(a: u32, b: u32)
    ensures crc8(a ^ b) == crc8(a) ^ crc8(b),
{
    let a1 = crc_bit(a); let a2 = crc_bit(a1); let a3 = crc_bit(a2); let a4 = crc_bit(a3);
    let a5 = crc_bit(a4); let a6 = crc_bit(a5); let a7 = crc_bit(a6);
    let b1 = crc_bit(b); let b2 = crc_bit(b1); let b3 = crc_bit(b2); let b4 = crc_bit(b3);
    let b5 = crc_bit(b4); let b6 = crc_bit(b5); let b7 = crc_bit(b6);
    lemma_bit_lin(a, b);
    lemma_bit_lin(a1, b1);
    lemma_bit_lin(a2, b2);
    lemma_bit_lin(a3, b3);
    lemma_bit_lin(a4, b4);
    lemma_bit_lin(a5, b5);
    lemma_bit_lin(a6, b6);
    lemma_bit_lin(a7, b7);
}

proof fn lemma_fpow_lin(a: u32, b: u32, m: nat)
    ensures fpow(a ^ b, m) == fpow(a, m) ^ fpow(b, m),
    decreases m,
{
    if m > 0 {
        lemma_fpow_lin(a, b, (m - 1) as nat);
        lemma_crc8_lin(fpow(a, (m - 1) as nat), fpow(b, (m - 1) as nat));
    }
}

/// `crc8` first, then `m - 1` more.
proof fn lemma_fpow_first(a: u32, m: nat)
    requires m >= 1,
    ensures fpow(a, m) == fpow(crc8(a), (m - 1) as nat),
    decreases m,
{
    if m > 1 {
        lemma_fpow_first(a, (m - 1) as nat);
        assert(fpow(a, m) == crc8(fpow(a, (m - 1) as nat)));
        assert(fpow(crc8(a), (m - 1) as nat) == crc8(fpow(crc8(a), (m - 2) as nat)));
    } else {
        assert(fpow(a, 1) == crc8(fpow(a, 0)));
    }
}

/// With its low byte zero, a register only shifts.
proof fn lemma_crc8_hi(a: u32)
    requires a & 0xff == 0,
    ensures crc8(a) == a >> 8,
{
    let c1 = crc_bit(a); let c2 = crc_bit(c1); let c3 = crc_bit(c2); let c4 = crc_bit(c3);
    let c5 = crc_bit(c4); let c6 = crc_bit(c5); let c7 = crc_bit(c6); let c8 = crc_bit(c7);
    assert(c8 == a >> 8) by (bit_vector)
        requires
            a & 0xff == 0,
            c1 == (if a & 1 == 1 { (a >> 1) ^ 0xEDB8_8320u32 } else { a >> 1 }),
            c2 == (if c1 & 1 == 1 { (c1 >> 1) ^ 0xEDB8_8320u32 } else { c1 >> 1 }),
            c3 == (if c2 & 1 == 1 { (c2 >> 1) ^ 0xEDB8_8320u32 } else { c2 >> 1 }),
            c4 == (if c3 & 1 == 1 { (c3 >> 1) ^ 0xEDB8_8320u32 } else { c3 >> 1 }),
            c5 == (if c4 & 1 == 1 { (c4 >> 1) ^ 0xEDB8_8320u32 } else { c4 >> 1 }),
            c6 == (if c5 & 1 == 1 { (c5 >> 1) ^ 0xEDB8_8320u32 } else { c5 >> 1 }),
            c7 == (if c6 & 1 == 1 { (c6 >> 1) ^ 0xEDB8_8320u32 } else { c6 >> 1 }),
            c8 == (if c7 & 1 == 1 { (c7 >> 1) ^ 0xEDB8_8320u32 } else { c7 >> 1 });
}

/// The bytes a run of 8 xors in, each carried through the steps after it.
spec fn inj8(s: Seq<u8>, i: int, j: nat) -> u32
    decreases j,
{
    if j == 0 { 0 } else { crc8(inj8(s, i, (j - 1) as nat)) ^ crc8(s[i + j - 1] as u32) }
}

/// `j` bytes from a register `g0`: the register through `j` steps, xor the
/// bytes' parts.
proof fn lemma_crc_steps(c: u32, s: Seq<u8>, i: int, j: nat)
    requires 0 <= i, i + j <= s.len(),
    ensures crc_run(c, s.take(i + j)) == fpow(crc_run(c, s.take(i)), j) ^ inj8(s, i, j),
    decreases j,
{
    if j > 0 {
        let jj = (j - 1) as nat;
        lemma_crc_steps(c, s, i, jj);
        let t = s.take(i + j);
        assert(t.drop_last() =~= s.take(i + jj));
        assert(t.last() == s[i + j - 1]);
        let g = crc_run(c, s.take(i + jj));
        let x = s[i + j - 1] as u32;
        assert(crc_run(c, t) == crc_byte(g, s[i + j - 1]));
        assert(crc_byte(g, s[i + j - 1]) == crc8(g ^ x));
        let f = fpow(crc_run(c, s.take(i)), jj);
        let z = inj8(s, i, jj);
        lemma_crc8_lin(g, x);
        lemma_crc8_lin(f, z);
        assert(g == f ^ z);
        assert(fpow(crc_run(c, s.take(i)), j) == crc8(f));
        assert(inj8(s, i, j) == crc8(z) ^ crc8(x));
        assert(crc8(g ^ x) == (crc8(f) ^ crc8(z)) ^ crc8(x));
        assert((crc8(f) ^ crc8(z)) ^ crc8(x) == crc8(f) ^ (crc8(z) ^ crc8(x))) by (bit_vector);
    } else {
        let g0 = crc_run(c, s.take(i));
        assert(g0 ^ 0 == g0) by (bit_vector);
        assert(s.take(i + j) == s.take(i));
    }
}

/// A byte xored in `8 - k` steps before the end, `k` past the first.
proof fn lemma_inj8(s: Seq<u8>, i: int)
    requires 0 <= i, i + 8 <= s.len(),
    ensures inj8(s, i, 8) == fpow(s[i] as u32, 8) ^ fpow(s[i + 1] as u32, 7) ^ fpow(s[i + 2] as u32, 6)
        ^ fpow(s[i + 3] as u32, 5) ^ fpow(s[i + 4] as u32, 4) ^ fpow(s[i + 5] as u32, 3)
        ^ fpow(s[i + 6] as u32, 2) ^ fpow(s[i + 7] as u32, 1),
{
    reveal_with_fuel(inj8, 9);
    reveal_with_fuel(fpow, 9);
    let x0 = s[i] as u32; let x1 = s[i + 1] as u32; let x2 = s[i + 2] as u32; let x3 = s[i + 3] as u32;
    let x4 = s[i + 4] as u32; let x5 = s[i + 5] as u32; let x6 = s[i + 6] as u32; let x7 = s[i + 7] as u32;
    // inj8(j) is the xor of fpow(x_t, j - t) for t < j
    let i1 = fpow(x0, 1);
    assert(inj8(s, i, 1) == crc8(0) ^ crc8(x0));
    assert(crc8(0u32) == 0) by {
        assert((0u32 & 0xff) == 0) by (bit_vector);
        lemma_crc8_hi(0);
        assert((0u32 >> 8) == 0) by (bit_vector);
    }
    assert(0u32 ^ crc8(x0) == crc8(x0)) by (bit_vector);
    assert(inj8(s, i, 1) == i1);
    let i2 = fpow(x0, 2) ^ fpow(x1, 1);
    lemma_crc8_lin(0, 0);
    assert(inj8(s, i, 2) == i2);
    let i3 = fpow(x0, 3) ^ fpow(x1, 2) ^ fpow(x2, 1);
    lemma_crc8_lin(fpow(x0, 2), fpow(x1, 1));
    assert(inj8(s, i, 3) == i3);
    let i4 = fpow(x0, 4) ^ fpow(x1, 3) ^ fpow(x2, 2) ^ fpow(x3, 1);
    lemma_crc8_lin(fpow(x0, 3) ^ fpow(x1, 2), fpow(x2, 1));
    lemma_crc8_lin(fpow(x0, 3), fpow(x1, 2));
    assert(inj8(s, i, 4) == i4);
    let i5 = fpow(x0, 5) ^ fpow(x1, 4) ^ fpow(x2, 3) ^ fpow(x3, 2) ^ fpow(x4, 1);
    lemma_crc8_lin(fpow(x0, 4) ^ fpow(x1, 3) ^ fpow(x2, 2), fpow(x3, 1));
    lemma_crc8_lin(fpow(x0, 4) ^ fpow(x1, 3), fpow(x2, 2));
    lemma_crc8_lin(fpow(x0, 4), fpow(x1, 3));
    assert(inj8(s, i, 5) == i5);
    let i6 = fpow(x0, 6) ^ fpow(x1, 5) ^ fpow(x2, 4) ^ fpow(x3, 3) ^ fpow(x4, 2) ^ fpow(x5, 1);
    lemma_crc8_lin(fpow(x0, 5) ^ fpow(x1, 4) ^ fpow(x2, 3) ^ fpow(x3, 2), fpow(x4, 1));
    lemma_crc8_lin(fpow(x0, 5) ^ fpow(x1, 4) ^ fpow(x2, 3), fpow(x3, 2));
    lemma_crc8_lin(fpow(x0, 5) ^ fpow(x1, 4), fpow(x2, 3));
    lemma_crc8_lin(fpow(x0, 5), fpow(x1, 4));
    assert(inj8(s, i, 6) == i6);
    let i7 = fpow(x0, 7) ^ fpow(x1, 6) ^ fpow(x2, 5) ^ fpow(x3, 4) ^ fpow(x4, 3) ^ fpow(x5, 2) ^ fpow(x6, 1);
    lemma_crc8_lin(fpow(x0, 6) ^ fpow(x1, 5) ^ fpow(x2, 4) ^ fpow(x3, 3) ^ fpow(x4, 2), fpow(x5, 1));
    lemma_crc8_lin(fpow(x0, 6) ^ fpow(x1, 5) ^ fpow(x2, 4) ^ fpow(x3, 3), fpow(x4, 2));
    lemma_crc8_lin(fpow(x0, 6) ^ fpow(x1, 5) ^ fpow(x2, 4), fpow(x3, 3));
    lemma_crc8_lin(fpow(x0, 6) ^ fpow(x1, 5), fpow(x2, 4));
    lemma_crc8_lin(fpow(x0, 6), fpow(x1, 5));
    assert(inj8(s, i, 7) == i7);
    lemma_crc8_lin(fpow(x0, 7) ^ fpow(x1, 6) ^ fpow(x2, 5) ^ fpow(x3, 4) ^ fpow(x4, 3) ^ fpow(x5, 2), fpow(x6, 1));
    lemma_crc8_lin(fpow(x0, 7) ^ fpow(x1, 6) ^ fpow(x2, 5) ^ fpow(x3, 4) ^ fpow(x4, 3), fpow(x5, 2));
    lemma_crc8_lin(fpow(x0, 7) ^ fpow(x1, 6) ^ fpow(x2, 5) ^ fpow(x3, 4), fpow(x4, 3));
    lemma_crc8_lin(fpow(x0, 7) ^ fpow(x1, 6) ^ fpow(x2, 5), fpow(x3, 4));
    lemma_crc8_lin(fpow(x0, 7) ^ fpow(x1, 6), fpow(x2, 5));
    lemma_crc8_lin(fpow(x0, 7), fpow(x1, 6));
}

/// `crc8` past a byte shifted up by 8: the byte, one step later.
proof fn lemma_fpow_up(y: u32, m: nat)
    requires y < 0x100_0000, m >= 1,
    ensures fpow(y << 8, m) == fpow(y, (m - 1) as nat),
{
    let z = y << 8;
    assert(z & 0xff == 0 && z >> 8 == y) by (bit_vector) requires z == y << 8, y < 0x100_0000;
    lemma_fpow_first(z, m);
    lemma_crc8_hi(z);
}

/// Eight bytes from the register `g`: eight table entries, the first four
/// at `g`'s bytes xored with the data's.
proof fn lemma_crc_8bytes(c: u32, s: Seq<u8>, i: int)
    requires 0 <= i, i + 8 <= s.len(),
    ensures ({
        let g = crc_run(c, s.take(i));
        crc_run(c, s.take(i + 8)) ==
            fpow((g & 0xff) ^ (s[i] as u32), 8) ^ fpow(((g >> 8) & 0xff) ^ (s[i + 1] as u32), 7)
            ^ fpow(((g >> 16) & 0xff) ^ (s[i + 2] as u32), 6) ^ fpow((g >> 24) ^ (s[i + 3] as u32), 5)
            ^ fpow(s[i + 4] as u32, 4) ^ fpow(s[i + 5] as u32, 3) ^ fpow(s[i + 6] as u32, 2) ^ fpow(s[i + 7] as u32, 1)
    }),
{
    let g = crc_run(c, s.take(i));
    lemma_crc_steps(c, s, i, 8);
    lemma_inj8(s, i);
    let b0 = g & 0xff; let b1 = (g >> 8) & 0xff; let b2 = (g >> 16) & 0xff; let b3 = g >> 24;
    let u1 = b1 << 8; let u2 = b2 << 16; let u3 = b3 << 24;
    let v2 = b2 << 8; let v3 = b3 << 16; let w3 = b3 << 8;
    assert(g == ((b0 ^ u1) ^ u2) ^ u3 && u2 == v2 << 8 && u3 == v3 << 8 && v3 == w3 << 8
        && b1 < 0x100_0000 && v2 < 0x100_0000 && w3 < 0x100_0000 && b2 < 0x100_0000 && b3 < 0x100_0000 && v3 < 0x100_0000)
        by (bit_vector)
        requires b0 == g & 0xff, b1 == (g >> 8) & 0xff, b2 == (g >> 16) & 0xff, b3 == g >> 24,
            u1 == b1 << 8, u2 == b2 << 16, u3 == b3 << 24, v2 == b2 << 8, v3 == b3 << 16, w3 == b3 << 8;
    lemma_fpow_lin((b0 ^ u1) ^ u2, u3, 8);
    lemma_fpow_lin(b0 ^ u1, u2, 8);
    lemma_fpow_lin(b0, u1, 8);
    lemma_fpow_up(b1, 8);
    lemma_fpow_up(v2, 8);
    lemma_fpow_up(b2, 7);
    lemma_fpow_up(v3, 8);
    lemma_fpow_up(w3, 7);
    lemma_fpow_up(b3, 6);
    let x0 = s[i] as u32; let x1 = s[i + 1] as u32; let x2 = s[i + 2] as u32; let x3 = s[i + 3] as u32;
    lemma_fpow_lin(b0, x0, 8);
    lemma_fpow_lin(b1, x1, 7);
    lemma_fpow_lin(b2, x2, 6);
    lemma_fpow_lin(b3, x3, 5);
    let f0 = fpow(b0, 8); let f1 = fpow(b1, 7); let f2 = fpow(b2, 6); let f3 = fpow(b3, 5);
    let e0 = fpow(x0, 8); let e1 = fpow(x1, 7); let e2 = fpow(x2, 6); let e3 = fpow(x3, 5);
    let e4 = fpow(s[i + 4] as u32, 4); let e5 = fpow(s[i + 5] as u32, 3);
    let e6 = fpow(s[i + 6] as u32, 2); let e7 = fpow(s[i + 7] as u32, 1);
    assert(fpow(g, 8) == ((f0 ^ f1) ^ f2) ^ f3);
    assert((((f0 ^ f1) ^ f2) ^ f3) ^ (e0 ^ e1 ^ e2 ^ e3 ^ e4 ^ e5 ^ e6 ^ e7)
        == (f0 ^ e0) ^ (f1 ^ e1) ^ (f2 ^ e2) ^ (f3 ^ e3) ^ e4 ^ e5 ^ e6 ^ e7) by (bit_vector);
}

/// Eight byte tables: `tt[256 * k + y]` is `y` through `k + 1` steps.
fn crc_tables8(t: &[u32; 256]) -> (tt: [u32; 2048])
    requires forall|i: int| 0 <= i < 256 ==> #[trigger] t[i] == crc_byte(0, i as u8),
    ensures forall|j: int| 0 <= j < 2048 ==> #[trigger] tt@[j] == fpow((j % 256) as u32, (j / 256 + 1) as nat),
{
    let mut tt = [0u32; 2048];
    let mut j: usize = 0;
    while j < 2048
        invariant
            j <= 2048,
            forall|i: int| 0 <= i < 256 ==> #[trigger] t[i] == crc_byte(0, i as u8),
            forall|q: int| 0 <= q < j ==> #[trigger] tt@[q] == fpow((q % 256) as u32, (q / 256 + 1) as nat),
        decreases 2048 - j,
    {
        if j < 256 {
            let v = t[j];
            proof {
                assert(0u32 ^ ((j as u8) as u32) == j as u32) by (bit_vector) requires j < 256;
                assert(crc_byte(0, j as u8) == crc8(j as u32));
                assert(fpow(j as u32, 1) == crc8(fpow(j as u32, 0)));
                assert((j as int) % 256 == j && (j as int) / 256 == 0);
            }
            tt[j] = v;
        } else {
            let p = tt[j - 256];
            let idx = (p & 0xff) as usize;
            assert(idx < 256) by (bit_vector) requires idx == (p & 0xff) as usize;
            let v = t[idx] ^ (p >> 8);
            proof {
                assert(((p ^ (0u8 as u32)) & 0xff) as u8 == idx as u8) by (bit_vector)
                    requires idx == (p & 0xff) as usize;
                lemma_crc_table_step(p, 0, t[idx as int]);
                assert(p ^ (0u8 as u32) == p) by (bit_vector);
                assert(crc_byte(p, 0) == crc8(p));
                let q = j as int - 256;
                assert(q % 256 == (j as int) % 256 && q / 256 + 1 == (j as int) / 256);
                let m = (q / 256 + 1) as nat;
                assert(fpow((q % 256) as u32, m + 1) == crc8(fpow((q % 256) as u32, m)));
            }
            tt[j] = v;
        }
        j = j + 1;
    }
    tt
}

/// The bytes of an 8-byte little-endian load, xored with a register.
proof fn lemma_bytes8(x: u64, c: u32, x0: u8, x1: u8, x2: u8, x3: u8, x4: u8, x5: u8, x6: u8, x7: u8)
    requires
        x == (x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64)
            | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64),
    ensures ({
        let lo = (x as u32) ^ c;
        let hi = (x >> 32u64) as u32;
        &&& (lo & 0xff) == (c & 0xff) ^ (x0 as u32)
        &&& ((lo >> 8) & 0xff) == ((c >> 8) & 0xff) ^ (x1 as u32)
        &&& ((lo >> 16) & 0xff) == ((c >> 16) & 0xff) ^ (x2 as u32)
        &&& (lo >> 24) == (c >> 24) ^ (x3 as u32)
        &&& (hi & 0xff) == x4 as u32 && ((hi >> 8) & 0xff) == x5 as u32
        &&& ((hi >> 16) & 0xff) == x6 as u32 && (hi >> 24) == x7 as u32
    }),
{
    let (y0, y1, y2, y3, y4, y5, y6, y7) = (x0 as u64, x1 as u64, x2 as u64, x3 as u64, x4 as u64, x5 as u64, x6 as u64, x7 as u64);
    let lo = (x as u32) ^ c;
    let hi = (x >> 32u64) as u32;
    assert(
        (lo & 0xff) == (c & 0xff) ^ (y0 as u32)
        && ((lo >> 8) & 0xff) == ((c >> 8) & 0xff) ^ (y1 as u32)
        && ((lo >> 16) & 0xff) == ((c >> 16) & 0xff) ^ (y2 as u32)
        && (lo >> 24) == (c >> 24) ^ (y3 as u32)
        && (hi & 0xff) == y4 as u32 && ((hi >> 8) & 0xff) == y5 as u32
        && ((hi >> 16) & 0xff) == y6 as u32 && (hi >> 24) == y7 as u32) by (bit_vector)
        requires
            x == y0 | (y1 << 8u64) | (y2 << 16u64) | (y3 << 24u64) | (y4 << 32u64) | (y5 << 40u64) | (y6 << 48u64) | (y7 << 56u64),
            y0 < 256, y1 < 256, y2 < 256, y3 < 256, y4 < 256, y5 < 256, y6 < 256, y7 < 256,
            lo == (x as u32) ^ c, hi == (x >> 32u64) as u32;
}

/// CRC-32 of `s`, continuing from `c` (before inversion).
pub fn crc_run_x(t: &[u32; 256], c: u32, s: &[u8]) -> (r: u32)
    requires forall|i: int| 0 <= i < 256 ==> #[trigger] t[i] == crc_byte(0, i as u8),
    ensures r == crc_run(c, s@),
{
    let mut c = c;
    let ghost c00 = c;
    let mut i: usize = 0;
    proof { assert(s@.take(0) =~= Seq::<u8>::empty()); }
    if s.len() >= 2048 {
        // eight bytes a step, from eight tables made here (about 1800
        // table steps, so only for longer inputs)
        let tt = crc_tables8(t);
        while 8 <= s.len() - i
            invariant
                i <= s.len(), c == crc_run(c00, s@.take(i as int)),
                forall|j: int| 0 <= j < 2048 ==> #[trigger] tt@[j] == fpow((j % 256) as u32, (j / 256 + 1) as nat),
            decreases s.len() - i,
        {
            let x = vsimd::mem::load_u64le(s, i);
            let lo = (x as u32) ^ c;
            let hi = (x >> 32u64) as u32;
            proof {
                let q = s@;
                let k = i as int;
                lemma_bytes8(x, c, q[k], q[k + 1], q[k + 2], q[k + 3], q[k + 4], q[k + 5], q[k + 6], q[k + 7]);
                lemma_crc_8bytes(c00, q, k);
                assert(lo >> 24 < 256 && hi >> 24 < 256 && (lo & 0xff) < 256 && ((lo >> 8) & 0xff) < 256
                    && ((lo >> 16) & 0xff) < 256 && (hi & 0xff) < 256 && ((hi >> 8) & 0xff) < 256
                    && ((hi >> 16) & 0xff) < 256) by (bit_vector);
            }
            // the last four bytes' part does not wait on c
            let rh = (tt[768 + (hi & 0xff) as usize] ^ tt[512 + ((hi >> 8) & 0xff) as usize])
                ^ (tt[256 + ((hi >> 16) & 0xff) as usize] ^ tt[(hi >> 24) as usize]);
            let rl = (tt[1792 + (lo & 0xff) as usize] ^ tt[1536 + ((lo >> 8) & 0xff) as usize])
                ^ (tt[1280 + ((lo >> 16) & 0xff) as usize] ^ tt[1024 + (lo >> 24) as usize]);
            let r = rl ^ rh;
            proof {
                assert(tt@[1792 + (lo & 0xff) as int] == fpow(lo & 0xff, 8));
                assert(tt@[1536 + ((lo >> 8) & 0xff) as int] == fpow((lo >> 8) & 0xff, 7));
                assert(tt@[1280 + ((lo >> 16) & 0xff) as int] == fpow((lo >> 16) & 0xff, 6));
                assert(tt@[1024 + (lo >> 24) as int] == fpow(lo >> 24, 5));
                assert(tt@[768 + (hi & 0xff) as int] == fpow(hi & 0xff, 4));
                assert(tt@[512 + ((hi >> 8) & 0xff) as int] == fpow((hi >> 8) & 0xff, 3));
                assert(tt@[256 + ((hi >> 16) & 0xff) as int] == fpow((hi >> 16) & 0xff, 2));
                assert(tt@[(hi >> 24) as int] == fpow(hi >> 24, 1));
                let (a7, a6, a5, a4) = (tt@[1792 + (lo & 0xff) as int], tt@[1536 + ((lo >> 8) & 0xff) as int],
                                        tt@[1280 + ((lo >> 16) & 0xff) as int], tt@[1024 + (lo >> 24) as int]);
                let (a3, a2, a1, a0) = (tt@[768 + (hi & 0xff) as int], tt@[512 + ((hi >> 8) & 0xff) as int],
                                        tt@[256 + ((hi >> 16) & 0xff) as int], tt@[(hi >> 24) as int]);
                assert(((a7 ^ a6) ^ (a5 ^ a4)) ^ ((a3 ^ a2) ^ (a1 ^ a0))
                    == a7 ^ a6 ^ a5 ^ a4 ^ a3 ^ a2 ^ a1 ^ a0) by (bit_vector);
            }
            c = r;
            i = i + 8;
        }
    }
    while i < s.len()
        invariant
            i <= s.len(), c == crc_run(c00, s@.take(i as int)),
            forall|i: int| 0 <= i < 256 ==> #[trigger] t[i] == crc_byte(0, i as u8),
        decreases s.len() - i,
    {
        let x = s[i];
        let idx = ((c ^ (x as u32)) & 0xff) as usize;
        assert(idx < 256) by (bit_vector) requires idx == ((c ^ (x as u32)) & 0xff) as usize;
        proof {
            assert((idx as u8) as u32 == (c ^ (x as u32)) & 0xff) by (bit_vector)
                requires idx == ((c ^ (x as u32)) & 0xff) as usize;
            assert(((c ^ (x as u32)) & 0xff) as u8 == idx as u8);
            lemma_crc_table_step(c, x, t[idx as int]);
            let tt = s@.take(i as int + 1);
            assert(tt.drop_last() =~= s@.take(i as int));
        }
        c = t[idx] ^ (c >> 8);
        i = i + 1;
    }
    proof { assert(s@.take(s.len() as int) =~= s@); }
    c
}

pub fn crc32_x(t: &[u32; 256], s: &[u8]) -> (r: u32)
    requires forall|i: int| 0 <= i < 256 ==> #[trigger] t[i] == crc_byte(0, i as u8),
    ensures r == crc32(s@),
{
    crc_run_x(t, 0xFFFF_FFFF, s) ^ 0xFFFF_FFFF
}

// ---------------------------------------------------------------- zlib

/// The byte position after a DEFLATE stream of `q` bits that starts at byte
/// `h`.
pub open spec fn after_bits(h: int, q: nat) -> int {
    h + (q + 7) as int / 8
}

/// A zlib stream: the data, the bytes it took, and whether zlib accepts it.
pub open spec fn zlib_decode(s: Seq<u8>) -> Option<(Seq<u8>, int, bool)> {
    if s.len() < 2 {
        None
    } else {
        let cmf = s[0] as nat;
        let flg = s[1] as nat;
        if cmf % 16 != 8 || cmf / 16 > 7 || (cmf * 256 + flg) % 31 != 0 || (flg / 32) % 2 == 1 {
            None
        } else {
            match inflate(lbits(s.skip(2))) {
                None => None,
                Some((o, q, st)) => {
                    let a = after_bits(2, q);
                    if a + 4 > s.len() {
                        None
                    } else {
                        let want = ((s[a] as nat * 256 + s[a + 1] as nat) * 256 + s[a + 2] as nat) * 256 + s[a + 3] as nat;
                        if want != adler32(o) { None } else { Some((o, a + 4, st)) }
                    }
                }
            }
        }
    }
}

pub fn inflate_zlib(buf: &[u8], max_out: usize) -> (r: Result<(Vec<u8>, usize, bool), Error>)
    requires buf.len() < max_input(), max_out <= max_len(),
    ensures
        match r {
            Ok((o, n, st)) => zlib_decode(buf@) == Some((o@, n as int, st)),
            Err(Error::Bad) => zlib_decode(buf@) is None,
            Err(Error::TooBig) => zlib_decode(buf@) matches Some((o, _, _)) ==> o.len() > max_out,
        },
{
    if buf.len() < 2 {
        return Err(Error::Bad);
    }
    let cmf = buf[0] as u32;
    let flg = buf[1] as u32;
    if cmf % 16 != 8 || cmf / 16 > 7 || (cmf * 256 + flg) % 31 != 0 || (flg / 32) % 2 == 1 {
        return Err(Error::Bad);
    }
    let body = vstd::slice::slice_subrange(buf, 2, buf.len());
    proof { assert(body@ =~= buf@.skip(2)); }
    let (o, q, st) = match inflate_raw(body, max_out) {
        Err(e) => return Err(e),
        Ok(x) => x,
    };
    let a = 2 + (q + 7) / 8;
    proof { assert(q <= 8 * body.len()); }
    if a > buf.len() || buf.len() - a < 4 {
        return Err(Error::Bad);
    }
    let want = ((buf[a] as u32 * 256 + buf[a + 1] as u32) * 256 + buf[a + 2] as u32) * 256 + buf[a + 3] as u32;
    if want != adler32_x(&o) {
        return Err(Error::Bad);
    }
    Ok((o, a + 4, st))
}

/// `inflate_zlib` into `out`, reused as it is: the data is `out[..n]`; a
/// buffer at least as long as the data needs no growing (nor zeroing).
pub fn inflate_zlib_into(buf: &[u8], out: &mut Vec<u8>, max_out: usize) -> (r: Result<(usize, usize, bool), Error>)
    requires buf.len() < max_input(), max_out <= max_len(),
    ensures
        match r {
            Ok((n, used, st)) => n <= final(out)@.len() && zlib_decode(buf@) == Some((final(out)@.take(n as int), used as int, st)),
            Err(Error::Bad) => zlib_decode(buf@) is None,
            Err(Error::TooBig) => zlib_decode(buf@) matches Some((o, _, _)) ==> o.len() > max_out,
        },
{
    if buf.len() < 2 {
        return Err(Error::Bad);
    }
    let cmf = buf[0] as u32;
    let flg = buf[1] as u32;
    if cmf % 16 != 8 || cmf / 16 > 7 || (cmf * 256 + flg) % 31 != 0 || (flg / 32) % 2 == 1 {
        return Err(Error::Bad);
    }
    let body = vstd::slice::slice_subrange(buf, 2, buf.len());
    proof { assert(body@ =~= buf@.skip(2)); }
    let (n, q, st) = match crate::inflate::inflate_raw_into(body, out, max_out) {
        Err(e) => return Err(e),
        Ok(x) => x,
    };
    let a = 2 + (q + 7) / 8;
    proof { assert(q <= 8 * body.len()); }
    if a > buf.len() || buf.len() - a < 4 {
        return Err(Error::Bad);
    }
    let want = ((buf[a] as u32 * 256 + buf[a + 1] as u32) * 256 + buf[a + 2] as u32) * 256 + buf[a + 3] as u32;
    let data = vstd::slice::slice_subrange(out.as_slice(), 0, n);
    proof { assert(data@ =~= out@.take(n as int)); }
    if want != adler32_x(data) {
        return Err(Error::Bad);
    }
    Ok((n, a + 4, st))
}

/// A zlib stream with a preset dictionary (RFC 1950 2.2, FDICT): the
/// header names the dictionary by its Adler-32 (DICTID), and the DEFLATE
/// stream decodes as if the dictionary were the output before it. Without
/// FDICT, `dict` is not used, and this is `zlib_decode`.
pub open spec fn zlib_decode_dict(s: Seq<u8>, dict: Seq<u8>) -> Option<(Seq<u8>, int, bool)> {
    if s.len() < 2 {
        None
    } else {
        let cmf = s[0] as nat;
        let flg = s[1] as nat;
        if (flg / 32) % 2 == 0 {
            zlib_decode(s)
        } else if cmf % 16 != 8 || cmf / 16 > 7 || (cmf * 256 + flg) % 31 != 0 || s.len() < 6 {
            None
        } else {
            let id = ((s[2] as nat * 256 + s[3] as nat) * 256 + s[4] as nat) * 256 + s[5] as nat;
            if id != adler32(dict) {
                None
            } else {
                match inflate_blocks(lbits(s.skip(6)), 0, dict, true) {
                    None => None,
                    Some((full, q, st)) => {
                        let o = full.skip(dict.len() as int);
                        let a = after_bits(6, q as nat);
                        if q < 0 || a + 4 > s.len() {
                            None
                        } else {
                            let want = ((s[a] as nat * 256 + s[a + 1] as nat) * 256 + s[a + 2] as nat) * 256 + s[a + 3] as nat;
                            if want != adler32(o) { None } else { Some((o, a + 4, st)) }
                        }
                    }
                }
            }
        }
    }
}

/// Decode a zlib stream that may use the preset dictionary `dict`.
pub fn inflate_zlib_dict(buf: &[u8], dict: &[u8], max_out: usize) -> (r: Result<(Vec<u8>, usize, bool), Error>)
    requires buf.len() < max_input(), max_out + dict.len() <= max_len(),
    ensures
        match r {
            Ok((o, n, st)) => zlib_decode_dict(buf@, dict@) == Some((o@, n as int, st)),
            Err(Error::Bad) => zlib_decode_dict(buf@, dict@) is None,
            Err(Error::TooBig) => zlib_decode_dict(buf@, dict@) matches Some((o, _, _)) ==> o.len() > max_out,
        },
{
    if buf.len() < 2 {
        return Err(Error::Bad);
    }
    let cmf = buf[0] as u32;
    let flg = buf[1] as u32;
    if (flg / 32) % 2 == 0 {
        return inflate_zlib(buf, max_out);
    }
    if cmf % 16 != 8 || cmf / 16 > 7 || (cmf * 256 + flg) % 31 != 0 || buf.len() < 6 {
        return Err(Error::Bad);
    }
    let id = ((buf[2] as u32 * 256 + buf[3] as u32) * 256 + buf[4] as u32) * 256 + buf[5] as u32;
    if id != adler32_x(dict) {
        return Err(Error::Bad);
    }
    let body = vstd::slice::slice_subrange(buf, 6, buf.len());
    proof { assert(body@ =~= buf@.skip(6)); }
    // the dictionary, then room for the output
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < dict.len()
        invariant i <= dict@.len(), out@ == dict@.take(i as int),
        decreases dict@.len() - i,
    {
        out.push(dict[i]);
        i = i + 1;
        proof { assert(out@ =~= dict@.take(i as int)); }
    }
    proof { assert(out@.take(dict@.len() as int) =~= dict@); assert(dict@.take(dict@.len() as int) =~= dict@); }
    let dl = dict.len();
    let (n, q, st) = match inflate_raw_after(body, &mut out, dl, max_out + dl) {
        Err(e) => {
            proof {
                if e == Error::TooBig {
                    if let Some((full, _, _)) = inflate_blocks(lbits(body@), 0, dict@, true) {
                        lemma_blocks_grow(lbits(body@), 0, dict@, true);
                    }
                }
            }
            return Err(e);
        }
        Ok(x) => x,
    };
    proof { lemma_blocks_grow(lbits(body@), 0, dict@, true); }
    let a = 6 + (q + 7) / 8;
    if a > buf.len() || buf.len() - a < 4 {
        return Err(Error::Bad);
    }
    let o = vstd::slice::slice_subrange(out.as_slice(), dl, n);
    proof { assert(o@ =~= out@.take(n as int).skip(dl as int)); }
    let want = ((buf[a] as u32 * 256 + buf[a + 1] as u32) * 256 + buf[a + 2] as u32) * 256 + buf[a + 3] as u32;
    if want != adler32_x(o) {
        return Err(Error::Bad);
    }
    let mut v: Vec<u8> = Vec::with_capacity(o.len());
    let mut j: usize = 0;
    while j < o.len()
        invariant j <= o@.len(), v@ == o@.take(j as int),
        decreases o@.len() - j,
    {
        v.push(o[j]);
        j = j + 1;
        proof { assert(v@ =~= o@.take(j as int)); }
    }
    proof {
        assert(o@.take(o@.len() as int) =~= o@);
        assert(o@ =~= out@.take(n as int).skip(dl as int));
    }
    Ok((v, a + 4, st))
}

// ---------------------------------------------------------------- gzip

/// The first zero byte at or after `i`, if there is one.
pub open spec fn zero_at(s: Seq<u8>, i: int) -> Option<int>
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() { None } else if s[i] == 0 { Some(i) } else { zero_at(s, i + 1) }
}

/// The byte position after a gzip header.
pub open spec fn gzip_header(s: Seq<u8>) -> Option<int> {
    if s.len() < 10 || s[0] != 0x1f || s[1] != 0x8b || s[2] != 8 || s[3] / 32 != 0 {
        None
    } else {
        let flg = s[3] as nat;
        let i0: int = 10;
        let i1: Option<int> = if (flg / 4) % 2 == 1 {
            if i0 + 2 > s.len() { None } else {
                let xlen = s[i0] as int + 256 * s[i0 + 1] as int;
                if i0 + 2 + xlen > s.len() { None } else { Some(i0 + 2 + xlen) }
            }
        } else { Some(i0) };
        match i1 {
            None => None,
            Some(i1) => {
                let i2: Option<int> = if (flg / 8) % 2 == 1 {
                    match zero_at(s, i1) { None => None, Some(z) => Some(z + 1) }
                } else { Some(i1) };
                match i2 {
                    None => None,
                    Some(i2) => {
                        let i3: Option<int> = if (flg / 16) % 2 == 1 {
                            match zero_at(s, i2) { None => None, Some(z) => Some(z + 1) }
                        } else { Some(i2) };
                        match i3 {
                            None => None,
                            Some(i3) =>
                                if (flg / 2) % 2 == 1 {
                                    if i3 + 2 > s.len() { None } else {
                                        let want = s[i3] as nat + 256 * s[i3 + 1] as nat;
                                        if want != crc32(s.take(i3)) as nat % 65536 { None } else { Some(i3 + 2) }
                                    }
                                } else { Some(i3) },
                        }
                    }
                }
            }
        }
    }
}

/// One gzip member: the data, the bytes it took, and whether zlib accepts it.
pub open spec fn gzip_decode(s: Seq<u8>) -> Option<(Seq<u8>, int, bool)> {
    match gzip_header(s) {
        None => None,
        Some(h) => match inflate(lbits(s.skip(h))) {
            None => None,
            Some((o, q, st)) => {
                let a = after_bits(h, q);
                if a + 8 > s.len() {
                    None
                } else {
                    let crc = ((s[a + 3] as nat * 256 + s[a + 2] as nat) * 256 + s[a + 1] as nat) * 256 + s[a] as nat;
                    let isize = ((s[a + 7] as nat * 256 + s[a + 6] as nat) * 256 + s[a + 5] as nat) * 256 + s[a + 4] as nat;
                    if crc != crc32(o) as nat || isize != o.len() % 0x1_0000_0000 {
                        None
                    } else {
                        Some((o, a + 8, st))
                    }
                }
            }
        },
    }
}

fn zero_at_x(s: &[u8], i: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(z) => zero_at(s@, i as int) == Some(z as int) && z < s.len(),
            None => zero_at(s@, i as int) is None,
        },
{
    let mut j = i;
    while j < s.len()
        invariant i <= j, zero_at(s@, j as int) == zero_at(s@, i as int),
        decreases s.len() - j,
    {
        if s[j] == 0 {
            return Some(j);
        }
        j = j + 1;
    }
    None
}

pub fn gzip_header_x(t: &[u32; 256], s: &[u8]) -> (r: Option<usize>)
    requires forall|i: int| 0 <= i < 256 ==> #[trigger] t[i] == crc_byte(0, i as u8),
    ensures
        match r {
            Some(h) => gzip_header(s@) == Some(h as int) && h <= s.len(),
            None => gzip_header(s@) is None,
        },
{
    if s.len() < 10 || s[0] != 0x1f || s[1] != 0x8b || s[2] != 8 || s[3] / 32 != 0 {
        return None;
    }
    let flg = s[3] as usize;
    let mut i: usize = 10;
    if (flg / 4) % 2 == 1 {
        if s.len() - i < 2 {
            return None;
        }
        let xlen = s[i] as usize + 256 * s[i + 1] as usize;
        if s.len() - (i + 2) < xlen {
            return None;
        }
        i = i + 2 + xlen;
    }
    if (flg / 8) % 2 == 1 {
        match zero_at_x(s, i) { None => return None, Some(z) => { i = z + 1; } }
    }
    if (flg / 16) % 2 == 1 {
        match zero_at_x(s, i) { None => return None, Some(z) => { i = z + 1; } }
    }
    if (flg / 2) % 2 == 1 {
        if s.len() - i < 2 {
            return None;
        }
        let want = s[i] as u32 + 256 * s[i + 1] as u32;
        let hd = vstd::slice::slice_subrange(s, 0, i);
        proof { assert(hd@ =~= s@.take(i as int)); }
        let c = crc32_x(t, hd);
        if want != c % 65536 {
            return None;
        }
        i = i + 2;
    }
    Some(i)
}

pub fn inflate_gzip(buf: &[u8], max_out: usize) -> (r: Result<(Vec<u8>, usize, bool), Error>)
    requires buf.len() < max_input(), max_out <= max_len(),
    ensures
        match r {
            Ok((o, n, st)) => gzip_decode(buf@) == Some((o@, n as int, st)),
            Err(Error::Bad) => gzip_decode(buf@) is None,
            Err(Error::TooBig) => gzip_decode(buf@) matches Some((o, _, _)) ==> o.len() > max_out,
        },
{
    let t = crc_table();
    let h = match gzip_header_x(&t, buf) {
        None => return Err(Error::Bad),
        Some(h) => h,
    };
    let body = vstd::slice::slice_subrange(buf, h, buf.len());
    proof { assert(body@ =~= buf@.skip(h as int)); }
    let (o, q, st) = match inflate_raw(body, max_out) {
        Err(e) => return Err(e),
        Ok(x) => x,
    };
    let a = h + (q + 7) / 8;
    proof { assert(q <= 8 * body.len()); }
    if a > buf.len() || buf.len() - a < 8 {
        return Err(Error::Bad);
    }
    let crc = ((buf[a + 3] as u32 * 256 + buf[a + 2] as u32) * 256 + buf[a + 1] as u32) * 256 + buf[a] as u32;
    let isize = ((buf[a + 7] as u64 * 256 + buf[a + 6] as u64) * 256 + buf[a + 5] as u64) * 256 + buf[a + 4] as u64;
    if crc != crc32_x(&t, &o) || isize != (o.len() as u64) % 0x1_0000_0000 {
        return Err(Error::Bad);
    }
    Ok((o, a + 8, st))
}

// ------------------------------------------------- gzip, several members

/// gzip members one after another to the end (RFC 1952 2.2: "a gzip file
/// consists of a series of members"), their data joined.
pub open spec fn gzip_members(s: Seq<u8>) -> Option<Seq<u8>>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(Seq::empty())
    } else {
        match gzip_decode(s) {
            None => None,
            Some((o, n, _)) =>
                if n <= 0 || n > s.len() {
                    None
                } else {
                    match gzip_members(s.skip(n)) {
                        None => None,
                        Some(r) => Some(o + r),
                    }
                },
        }
    }
}

/// A gzip file: at least one member.
pub open spec fn gzip_file(s: Seq<u8>) -> Option<Seq<u8>> {
    if s.len() == 0 { None } else { gzip_members(s) }
}

proof fn lemma_members_unfold(s: Seq<u8>)
    requires s.len() > 0,
    ensures gzip_members(s) == match gzip_decode(s) {
        None => None,
        Some((o, n, _)) =>
            if n <= 0 || n > s.len() { None } else {
                match gzip_members(s.skip(n)) { None => None, Some(r) => Some(o + r) }
            },
    },
{
}

proof fn lemma_members_empty()
    ensures gzip_members(Seq::<u8>::empty()) == Some(Seq::<u8>::empty()),
{
}

/// Decode a gzip file of one or more members.
pub fn inflate_gzip_file(buf: &[u8], max_out: usize) -> (r: Result<Vec<u8>, Error>)
    requires buf.len() < max_input(), max_out <= max_len(),
    ensures
        match r {
            Ok(o) => gzip_file(buf@) == Some(o@),
            Err(Error::Bad) => gzip_file(buf@) is None,
            Err(Error::TooBig) => gzip_file(buf@) matches Some(o) ==> o.len() > max_out,
        },
{
    hide(gzip_decode);
    hide(gzip_members);
    if buf.len() == 0 {
        return Err(Error::Bad);
    }
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    proof { assert(buf@.skip(0) =~= buf@); assert(out@ + Seq::<u8>::empty() =~= out@); }
    while i < buf.len()
        invariant
            i <= buf@.len(), buf@.len() < max_input(), max_out <= max_len(), out@.len() <= max_out,
            gzip_members(buf@) == match gzip_members(buf@.skip(i as int)) { None => None, Some(r) => Some(out@ + r) },
        decreases buf@.len() - i,
    {
        let rest = vstd::slice::slice_subrange(buf, i, buf.len());
        proof { assert(rest@ =~= buf@.skip(i as int)); lemma_members_unfold(rest@); }
        match inflate_gzip(rest, max_out - out.len()) {
            Err(Error::Bad) => {
                return Err(Error::Bad);
            }
            Err(Error::TooBig) => {
                proof {
                    // the rest's first member alone is too long for what is left
                    if let Some(all) = gzip_members(buf@) {
                        let r = gzip_members(rest@).unwrap();
                        let (o, n, z) = gzip_decode(rest@).unwrap();
                        assert(r == o + gzip_members(rest@.skip(n)).unwrap());
                        assert(all.len() == out@.len() + r.len());
                        assert(o.len() > max_out - out@.len());
                    }
                }
                return Err(Error::TooBig);
            }
            Ok((o, n, _)) => {
                if n == 0 || n > rest.len() {
                    return Err(Error::Bad);
                }
                if o.len() > max_out - out.len() {
                    proof {
                        if let Some(all) = gzip_members(buf@) {
                            let r = gzip_members(rest@).unwrap();
                            assert(r == o@ + gzip_members(rest@.skip(n as int)).unwrap());
                            assert(all.len() == out@.len() + r.len());
                        }
                    }
                    return Err(Error::TooBig);
                }
                let ghost out0 = out@;
                let mut o = o;
                out.append(&mut o);
                proof {
                    assert(rest@.skip(n as int) =~= buf@.skip(i + n));
                    match gzip_members(buf@.skip(i + n)) {
                        None => {}
                        Some(r2) => { assert(out0 + (gzip_decode(rest@).unwrap().0 + r2) =~= out@ + r2); }
                    }
                }
                i = i + n;
            }
        }
    }
    proof {
        assert(buf@.skip(i as int) =~= Seq::<u8>::empty());
        lemma_members_empty();
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
    Ok(out)
}

// ---------------------------------------------------------- compression

proof fn lemma_lbits_skip_bytes(a: Seq<u8>, k: int)
    requires 0 <= k <= a.len(),
    ensures lbits(a.skip(k)) == lbits(a).skip(8 * k),
{
    vbits::lsb::lemma_lbits_add(a.take(k), a.skip(k));
    assert(a =~= a.take(k) + a.skip(k));
    assert(lbits(a).skip(8 * k) =~= lbits(a.skip(k)));
}

/// A DEFLATE stream followed by more bytes is a stream that starts with it.
proof fn lemma_body_then(body: Seq<u8>, tail: Seq<u8>)
    ensures crate::step::is_prefix(lbits(body), lbits(body + tail)),
{
    vbits::lsb::lemma_lbits_add(body, tail);
}

proof fn lemma_u32_bytes_be(a: u32)
    ensures ((((a >> 24) as u8) as nat * 256 + ((a >> 16) as u8) as nat) * 256 + ((a >> 8) as u8) as nat) * 256
        + (a as u8) as nat == a as nat,
{
    let b0 = ((a >> 24) as u8) as u32;
    let b1 = ((a >> 16) as u8) as u32;
    let b2 = ((a >> 8) as u8) as u32;
    let b3 = (a as u8) as u32;
    assert(((b0 * 256 + b1) * 256 + b2) * 256 + b3 == a) by (bit_vector)
        requires b0 == ((a >> 24) as u8) as u32, b1 == ((a >> 16) as u8) as u32, b2 == ((a >> 8) as u8) as u32,
                 b3 == (a as u8) as u32;
}

proof fn lemma_u32_bytes_le(a: u32)
    ensures ((((a >> 24) as u8) as nat * 256 + ((a >> 16) as u8) as nat) * 256 + ((a >> 8) as u8) as nat) * 256
        + (a as u8) as nat == a as nat,
{
    lemma_u32_bytes_be(a);
}

pub proof fn lemma_zlib_out(data: Seq<u8>, body: Seq<u8>, a: u32, o: Seq<u8>)
    requires
        crate::enc2::deflate_ok(data, body), a == adler32(data),
        o == seq![0x78u8, 0x01u8] + (body + seq![(a >> 24) as u8, (a >> 16) as u8, (a >> 8) as u8, a as u8]),
    ensures zlib_decode(o) matches Some((d, n, z)) && d == data && n == o.len() && z,
{
    let tail = seq![(a >> 24) as u8, (a >> 16) as u8, (a >> 8) as u8, a as u8];
    assert(o.skip(2) =~= body + tail);
    let (q, st) = choose|q: nat, st: bool| #![trigger crate::enc2::inflate_q(body, q, st)]
        crate::enc2::inflate_q(body, q, st) && st && (q + 7) / 8 == body.len()
        && forall|b: Seq<bool>| #[trigger] crate::step::is_prefix(lbits(body), b) ==> inflate(b) == Some((data, q, st));
    lemma_body_then(body, tail);
    assert(inflate(lbits(o.skip(2))) == Some((data, q, st)));
    let k = 2 + body.len() as int;
    assert(after_bits(2, q) == k);
    lemma_u32_bytes_be(a);
    assert(o[k] == tail[0] && o[k + 1] == tail[1] && o[k + 2] == tail[2] && o[k + 3] == tail[3]);
    assert(o[0] == 0x78u8 && o[1] == 0x01u8);
    assert(((120nat * 256 + 1) % 31) == 0);
}

/// Compress into a zlib stream: CMF 0x78 (a 32K window), FLG 0x01, the
/// DEFLATE stream, the Adler-32 of the data.
pub fn deflate_zlib(data: &[u8], lv: crate::enc2::Level) -> (r: Option<Vec<u8>>)
    requires data.len() < 0x1000_0000, crate::enc2::level_ok(lv),
    ensures r matches Some(o) ==> (zlib_decode(o@) matches Some((d, n, z)) && d == data@ && n == o@.len() && z),
{
    let body = match crate::enc2::deflate_level(data, lv) { None => return None, Some(b) => b };
    let mut out: Vec<u8> = Vec::new();
    out.push(0x78);
    out.push(0x01);
    let mut i: usize = 0;
    while i < body.len()
        invariant i <= body@.len(), out@ == seq![0x78u8, 0x01u8] + body@.take(i as int),
        decreases body@.len() - i,
    {
        out.push(body[i]);
        i = i + 1;
        proof { assert(out@ =~= seq![0x78u8, 0x01u8] + body@.take(i as int)); }
    }
    let a = adler32_x(data);
    let t0 = (a >> 24) as u8;
    let t1 = (a >> 16) as u8;
    let t2 = (a >> 8) as u8;
    let t3 = a as u8;
    out.push(t0);
    out.push(t1);
    out.push(t2);
    out.push(t3);
    proof {
        assert(body@.take(body@.len() as int) =~= body@);
        let tail = seq![t0, t1, t2, t3];
        assert(out@ =~= seq![0x78u8, 0x01u8] + (body@ + tail));
        lemma_zlib_out(data@, body@, a, out@);
    }
    Some(out)
}

/// Compress into a gzip member: a 10-byte header (no flags, MTIME 0, OS
/// 255), the DEFLATE stream, CRC-32 and ISIZE.
#[verifier::spinoff_prover]
pub fn deflate_gzip(data: &[u8], lv: crate::enc2::Level) -> (r: Option<Vec<u8>>)
    requires data.len() < 0x1000_0000, crate::enc2::level_ok(lv),
    ensures r matches Some(o) ==> (gzip_decode(o@) matches Some((d, n, z)) && d == data@ && n == o@.len() && z),
{
    let body = match crate::enc2::deflate_level(data, lv) { None => return None, Some(b) => b };
    let hdr: [u8; 10] = [0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 0xff];
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < 10
        invariant i <= 10, out@ =~= hdr@.take(i as int),
        decreases 10 - i,
    {
        out.push(hdr[i]);
        i = i + 1;
        proof { assert(out@ =~= hdr@.take(i as int)); }
    }
    let mut i: usize = 0;
    while i < body.len()
        invariant i <= body@.len(), out@ == hdr@ + body@.take(i as int),
        decreases body@.len() - i,
    {
        out.push(body[i]);
        i = i + 1;
        proof { assert(out@ =~= hdr@ + body@.take(i as int)); }
    }
    let tb = crc_table();
    let c = crc32_x(&tb, data);
    let z = (data.len() as u64 % 0x1_0000_0000) as u32;
    let t = [c as u8, (c >> 8) as u8, (c >> 16) as u8, (c >> 24) as u8,
             z as u8, (z >> 8) as u8, (z >> 16) as u8, (z >> 24) as u8];
    let mut k: usize = 0;
    let ghost o0 = out@;
    while k < 8
        invariant k <= 8, out@ == o0 + t@.take(k as int),
        decreases 8 - k,
    {
        out.push(t[k]);
        k = k + 1;
        proof { assert(out@ =~= o0 + t@.take(k as int)); }
    }
    proof {
        let o = out@;
        let tail = t@;
        assert(t@.take(8) =~= t@);
        assert(body@.take(body@.len() as int) =~= body@);
        assert(o =~= hdr@ + (body@ + tail));
        assert(o.skip(10) =~= body@ + tail);
        assert(gzip_header(o) == Some(10int));
        let (q, st) = choose|q: nat, st: bool| #![trigger crate::enc2::inflate_q(body@, q, st)]
            crate::enc2::inflate_q(body@, q, st) && st && (q + 7) / 8 == body@.len()
            && forall|b: Seq<bool>| #[trigger] crate::step::is_prefix(lbits(body@), b) ==> inflate(b) == Some((data@, q, st));
        lemma_body_then(body@, tail);
        assert(inflate(lbits(o.skip(10))) == Some((data@, q, st)));
        let a = 10 + body@.len() as int;
        assert(after_bits(10, q) == a);
        lemma_u32_bytes_le(c);
        lemma_u32_bytes_le(z);
        assert(o[a] == t[0] && o[a + 1] == t[1] && o[a + 2] == t[2] && o[a + 3] == t[3]);
        assert(o[a + 4] == t[4] && o[a + 5] == t[5] && o[a + 6] == t[6] && o[a + 7] == t[7]);
        assert(z as nat == data@.len() % 0x1_0000_0000);
    }
    Some(out)
}

// ------------------------------------------------ incremental checksums

pub proof fn lemma_crc_run_append(c: u32, a: Seq<u8>, b: Seq<u8>)
    ensures crc_run(c, a + b) == crc_run(crc_run(c, a), b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        lemma_crc_run_append(c, a, b.drop_last());
    }
}

// ------------------------------------------- Adler-32, sixteen bytes a step

/// The first `n` bytes of `c`, summed.
spec fn sumi(c: Seq<u8>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { sumi(c, n - 1) + c[n - 1] as int }
}

/// The first `n` bytes of `c`, each times the number of bytes from it to
/// the `n`th (the first `n` times, the last once).
spec fn wsumi(c: Seq<u8>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { wsumi(c, n - 1) + sumi(c, n) }
}

proof fn lemma_sumi_eq(c: Seq<u8>, d: Seq<u8>, n: int)
    requires forall|j: int| 0 <= j < n ==> #[trigger] c[j] == d[j],
    ensures sumi(c, n) == sumi(d, n), wsumi(c, n) == wsumi(d, n),
    decreases n,
{
    if n > 0 {
        lemma_sumi_eq(c, d, n - 1);
    }
}

/// What appending `c` does to Adler-32's unreduced sums.
proof fn lemma_adler_app(t: Seq<u8>, c: Seq<u8>)
    ensures
        adler_a(t + c) == adler_a(t) + sumi(c, c.len() as int),
        adler_b(t + c) == adler_b(t) + c.len() * adler_a(t) + wsumi(c, c.len() as int),
    decreases c.len(),
{
    if c.len() == 0 {
        assert(t + c =~= t);
    } else {
        let n = c.len() as int;
        let c1 = c.drop_last();
        lemma_adler_app(t, c1);
        assert((t + c).drop_last() =~= t + c1);
        assert((t + c).last() == c[n - 1]);
        lemma_sumi_eq(c1, c, n - 1);
        let at = adler_a(t);
        assert((n - 1) * at + at == n * at) by (nonlinear_arith);
    }
}

/// Sums of a sequence made of two.
proof fn lemma_sumi_cat(d: Seq<u8>, e: Seq<u8>)
    ensures
        sumi(d + e, (d.len() + e.len()) as int) == sumi(d, d.len() as int) + sumi(e, e.len() as int),
        wsumi(d + e, (d.len() + e.len()) as int)
            == wsumi(d, d.len() as int) + e.len() * sumi(d, d.len() as int) + wsumi(e, e.len() as int),
    decreases e.len(),
{
    let de = d + e;
    let nd = d.len() as int;
    if e.len() == 0 {
        lemma_sumi_eq(de, d, nd);
    } else {
        let e1 = e.drop_last();
        lemma_sumi_cat(d, e1);
        let n = (d.len() + e.len()) as int;
        lemma_sumi_eq(d + e1, de, n - 1);
        lemma_sumi_eq(e1, e, e.len() - 1);
        assert(de[n - 1] == e[e.len() - 1]);
        let sd = sumi(d, nd);
        assert((e.len() - 1) * sd + sd == e.len() * sd) by (nonlinear_arith);
    }
}

/// A 16-byte block's sums, term by term.
proof fn lemma_sumi16(e: Seq<u8>)
    requires e.len() == 16,
    ensures
        sumi(e, 16) == e[0] as int + e[1] as int + e[2] as int + e[3] as int + e[4] as int + e[5] as int
            + e[6] as int + e[7] as int + e[8] as int + e[9] as int + e[10] as int + e[11] as int
            + e[12] as int + e[13] as int + e[14] as int + e[15] as int,
        wsumi(e, 16) == 16 * e[0] as int + 15 * e[1] as int + 14 * e[2] as int + 13 * e[3] as int
            + 12 * e[4] as int + 11 * e[5] as int + 10 * e[6] as int + 9 * e[7] as int
            + 8 * e[8] as int + 7 * e[9] as int + 6 * e[10] as int + 5 * e[11] as int
            + 4 * e[12] as int + 3 * e[13] as int + 2 * e[14] as int + 1 * e[15] as int,
{
    reveal_with_fuel(sumi, 17);
    reveal_with_fuel(wsumi, 17);
}

proof fn lemma_sumi_bound(c: Seq<u8>, n: int)
    requires 0 <= n <= c.len(),
    ensures 0 <= sumi(c, n) <= 255 * n, 0 <= wsumi(c, n) <= 255 * n * n,
    decreases n,
{
    if n > 0 {
        lemma_sumi_bound(c, n - 1);
        assert(255 * (n - 1) * (n - 1) + 255 * n <= 255 * n * n) by (nonlinear_arith) requires n >= 1;
    }
}

/// Adler-32's register mod 65521 past a run whose unreduced sums are known.
proof fn lemma_adler_mod(a: int, b: int, aa: int, bb: int, n: int, sm: int, ws: int)
    requires a % 65521 == aa % 65521, b % 65521 == bb % 65521, a >= 0, b >= 0, aa >= 0, bb >= 0, n >= 0,
    ensures (a + sm) % 65521 == (aa + sm) % 65521, (b + n * a + ws) % 65521 == (bb + n * aa + ws) % 65521,
{
    use vstd::arithmetic::div_mod::*;
    lemma_add_mod_noop(a, sm, 65521);
    lemma_add_mod_noop(aa, sm, 65521);
    lemma_mul_mod_noop_right(n, a, 65521);
    lemma_mul_mod_noop_right(n, aa, 65521);
    lemma_add_mod_noop(b, n * a, 65521);
    lemma_add_mod_noop(bb, n * aa, 65521);
    lemma_add_mod_noop(b + n * a, ws, 65521);
    lemma_add_mod_noop(bb + n * aa, ws, 65521);
}

/// Lane `j` of a vector, unsigned 32-bit.
#[cfg(target_arch = "x86_64")]
spec fn l32(v: __m128i, j: int) -> int { vsimd::spec::w32(v8(v), j) }

/// A 16-byte block's sum in lanes 0 and 2 of `sad_epu8(x, 0)`.
#[cfg(target_arch = "x86_64")]
proof fn lemma_sad_block(x8: Seq<u8>, z8: Seq<u8>)
    requires x8.len() == 16, z8 == vsimd::spec::set1_epi8(0),
    ensures ({
        let sd = vsimd::spec::sad_epu8(x8, z8);
        &&& vsimd::spec::w32(sd, 0) + vsimd::spec::w32(sd, 2) == sumi(x8, 16)
        &&& vsimd::spec::w32(sd, 1) == 0 && vsimd::spec::w32(sd, 3) == 0
        &&& 0 <= vsimd::spec::w32(sd, 0) <= 2040 && 0 <= vsimd::spec::w32(sd, 2) <= 2040
    }),
{
    use vsimd::spec::*;
    lemma_sad_lane(x8, z8, 0);
    lemma_sad_lane(x8, z8, 1);
    assert(sad8(x8, z8, 0) == x8[0] as int + x8[1] as int + x8[2] as int + x8[3] as int
        + x8[4] as int + x8[5] as int + x8[6] as int + x8[7] as int);
    assert(sad8(x8, z8, 1) == x8[8] as int + x8[9] as int + x8[10] as int + x8[11] as int
        + x8[12] as int + x8[13] as int + x8[14] as int + x8[15] as int);
    lemma_sumi16(x8);
}

/// One `madd_epi16` lane against the weights, as two products.
#[cfg(target_arch = "x86_64")]
proof fn lemma_madd_w(x8: Seq<u8>, z8: Seq<u8>, w8: Seq<u8>, hi: bool, j: int, c0: int, c1: int)
    requires x8.len() == 16, z8 == vsimd::spec::set1_epi8(0), w8.len() == 16, 0 <= j < 4,
        w8[4 * j] as int == c0, w8[4 * j + 2] as int == c1,
        forall|t: int| 0 <= t < 16 ==> #[trigger] w8[t] <= 16,
        forall|t: int| 0 <= t < 8 ==> #[trigger] w8[2 * t + 1] == 0,
    ensures ({
        let u = if hi { vsimd::spec::unpackhi_epi8(x8, z8) } else { vsimd::spec::unpacklo_epi8(x8, z8) };
        let o = if hi { 8 } else { 0int };
        &&& vsimd::spec::w32(vsimd::spec::madd_epi16(u, w8), j) == x8[o + 2 * j] as int * c0 + x8[o + 2 * j + 1] as int * c1
        &&& vsimd::spec::madd_epi16(u, w8).len() == 16
    }),
{
    use vsimd::spec::*;
    let u = if hi { unpackhi_epi8(x8, z8) } else { unpacklo_epi8(x8, z8) };
    let o = if hi { 8 } else { 0int };
    assert forall|k: int| 0 <= k < 16 implies #[trigger] z8[k] == 0 by {}
    lemma_zext_lane(x8, z8, 2 * j);
    lemma_zext_lane(x8, z8, 2 * j + 1);
    let a0 = x8[o + 2 * j] as int;
    let a1 = x8[o + 2 * j + 1] as int;
    assert(sw16(u, 2 * j) == a0 && sw16(u, 2 * j + 1) == a1);
    assert(w8[2 * (2 * j) + 1] == 0 && w8[2 * (2 * j + 1) + 1] == 0);
    assert(2 * (2 * j) == 4 * j && 2 * (2 * j + 1) == 4 * j + 2);
    assert(sw16(w8, 2 * j) == c0 && sw16(w8, 2 * j + 1) == c1);
    lemma_madd_lane(u, w8, j);
    assert(0 <= c0 <= 16 && 0 <= c1 <= 16);
    assert(0 <= a0 * c0 + a1 * c1 <= 8160) by (nonlinear_arith)
        requires 0 <= a0 <= 255, 0 <= a1 <= 255, 0 <= c0 <= 16, 0 <= c1 <= 16;
    vstd::arithmetic::div_mod::lemma_small_mod((a0 * c0 + a1 * c1) as nat, 4294967296);
}

/// A 16-byte block's weighted sum over the four lanes of
/// `add_epi32(madd_epi16(lo, wlo), madd_epi16(hi, whi))`.
#[cfg(target_arch = "x86_64")]
proof fn lemma_madd_block(x8: Seq<u8>, z8: Seq<u8>, wl: Seq<u8>, wh: Seq<u8>)
    requires x8.len() == 16, z8 == vsimd::spec::set1_epi8(0),
        wl == seq![16u8, 0, 15, 0, 14, 0, 13, 0, 12, 0, 11, 0, 10, 0, 9, 0],
        wh == seq![8u8, 0, 7, 0, 6, 0, 5, 0, 4, 0, 3, 0, 2, 0, 1, 0],
    ensures ({
        let m = vsimd::spec::add_epi32(vsimd::spec::madd_epi16(vsimd::spec::unpacklo_epi8(x8, z8), wl),
                                       vsimd::spec::madd_epi16(vsimd::spec::unpackhi_epi8(x8, z8), wh));
        &&& vsimd::spec::w32(m, 0) + vsimd::spec::w32(m, 1) + vsimd::spec::w32(m, 2) + vsimd::spec::w32(m, 3) == wsumi(x8, 16)
        &&& 0 <= vsimd::spec::w32(m, 0) <= 11730 && 0 <= vsimd::spec::w32(m, 1) <= 11730
        &&& 0 <= vsimd::spec::w32(m, 2) <= 11730 && 0 <= vsimd::spec::w32(m, 3) <= 11730
    }),
{
    use vsimd::spec::*;
    hide(madd_epi16);
    hide(add_epi32);
    hide(unpacklo_epi8);
    hide(unpackhi_epi8);
    let ml = madd_epi16(unpacklo_epi8(x8, z8), wl);
    let mh = madd_epi16(unpackhi_epi8(x8, z8), wh);
    assert forall|t: int| 0 <= t < 16 implies #[trigger] wl[t] <= 16 && #[trigger] wh[t] <= 16 by {}
    assert forall|t: int| 0 <= t < 8 implies #[trigger] wl[2 * t + 1] == 0 && #[trigger] wh[2 * t + 1] == 0 by {}
    lemma_madd_w(x8, z8, wl, false, 0, 16, 15);
    lemma_madd_w(x8, z8, wl, false, 1, 14, 13);
    lemma_madd_w(x8, z8, wl, false, 2, 12, 11);
    lemma_madd_w(x8, z8, wl, false, 3, 10, 9);
    lemma_madd_w(x8, z8, wh, true, 0, 8, 7);
    lemma_madd_w(x8, z8, wh, true, 1, 6, 5);
    lemma_madd_w(x8, z8, wh, true, 2, 4, 3);
    lemma_madd_w(x8, z8, wh, true, 3, 2, 1);
    lemma_madd_sum(x8, ml, mh);
}

/// A 32-bit lane of a sum that does not wrap.
proof fn lemma_add_lane(a: Seq<u8>, b: Seq<u8>, j: int)
    requires 0 <= j < 4, a.len() == 16, b.len() == 16,
        vsimd::spec::w32(a, j) + vsimd::spec::w32(b, j) < 4294967296,
    ensures vsimd::spec::w32(vsimd::spec::add_epi32(a, b), j) == vsimd::spec::w32(a, j) + vsimd::spec::w32(b, j),
{
    vsimd::spec::lemma_add32_lane(a, b, j);
    vsimd::spec::lemma_w32_bounds(a, j);
    vsimd::spec::lemma_w32_bounds(b, j);
    vstd::arithmetic::div_mod::lemma_small_mod(
        (vsimd::spec::w32(a, j) + vsimd::spec::w32(b, j)) as nat, 4294967296);
}

/// The four lanes of the two weighted products, added.
proof fn lemma_madd_sum(x8: Seq<u8>, ml: Seq<u8>, mh: Seq<u8>)
    requires
        x8.len() == 16, ml.len() == 16, mh.len() == 16,
        vsimd::spec::w32(ml, 0) == 16 * x8[0] as int + 15 * x8[1] as int,
        vsimd::spec::w32(ml, 1) == 14 * x8[2] as int + 13 * x8[3] as int,
        vsimd::spec::w32(ml, 2) == 12 * x8[4] as int + 11 * x8[5] as int,
        vsimd::spec::w32(ml, 3) == 10 * x8[6] as int + 9 * x8[7] as int,
        vsimd::spec::w32(mh, 0) == 8 * x8[8] as int + 7 * x8[9] as int,
        vsimd::spec::w32(mh, 1) == 6 * x8[10] as int + 5 * x8[11] as int,
        vsimd::spec::w32(mh, 2) == 4 * x8[12] as int + 3 * x8[13] as int,
        vsimd::spec::w32(mh, 3) == 2 * x8[14] as int + 1 * x8[15] as int,
    ensures ({
        let m = vsimd::spec::add_epi32(ml, mh);
        &&& vsimd::spec::w32(m, 0) + vsimd::spec::w32(m, 1) + vsimd::spec::w32(m, 2) + vsimd::spec::w32(m, 3) == wsumi(x8, 16)
        &&& 0 <= vsimd::spec::w32(m, 0) <= 11730 && 0 <= vsimd::spec::w32(m, 1) <= 11730
        &&& 0 <= vsimd::spec::w32(m, 2) <= 11730 && 0 <= vsimd::spec::w32(m, 3) <= 11730
    }),
{
    hide(vsimd::spec::add_epi32);
    hide(vsimd::spec::w32);
    lemma_sumi16(x8);
    lemma_add_lane(ml, mh, 0);
    lemma_add_lane(ml, mh, 1);
    lemma_add_lane(ml, mh, 2);
    lemma_add_lane(ml, mh, 3);
}

/// `adler_blocks`'s loop, past one more block: its accumulators' lanes,
/// as byte sequences (`vs`, `vp`, `vw` before, `vs2`, `vp2`, `vw2` after).
#[cfg(target_arch = "x86_64")]
proof fn lemma_loop_step(vs: Seq<u8>, vp: Seq<u8>, vw: Seq<u8>, vs2: Seq<u8>, vp2: Seq<u8>, vw2: Seq<u8>,
                         x8: Seq<u8>, z8: Seq<u8>, wl: Seq<u8>, wh: Seq<u8>, sd: Seq<u8>, m: Seq<u8>,
                         c0: Seq<u8>, k: int)
    requires
        vs.len() == 16, vp.len() == 16, vw.len() == 16, x8.len() == 16, 0 <= k < 1024, c0.len() == 16 * k,
        sd.len() == 16, m.len() == 16,
        z8 == vsimd::spec::set1_epi8(0),
        wl == seq![16u8, 0, 15, 0, 14, 0, 13, 0, 12, 0, 11, 0, 10, 0, 9, 0],
        wh == seq![8u8, 0, 7, 0, 6, 0, 5, 0, 4, 0, 3, 0, 2, 0, 1, 0],
        sd == vsimd::spec::sad_epu8(x8, z8),
        m == vsimd::spec::add_epi32(vsimd::spec::madd_epi16(vsimd::spec::unpacklo_epi8(x8, z8), wl),
                                    vsimd::spec::madd_epi16(vsimd::spec::unpackhi_epi8(x8, z8), wh)),
        vp2 == vsimd::spec::add_epi32(vp, vs), vs2 == vsimd::spec::add_epi32(vs, sd), vw2 == vsimd::spec::add_epi32(vw, m),
        aw_inv(vs, vp, vw, c0, k),
    ensures aw_inv(vs2, vp2, vw2, c0 + x8, k + 1),
{
    use vsimd::spec::*;
    hide(add_epi32);
    hide(madd_epi16);
    hide(sad_epu8);
    hide(unpacklo_epi8);
    hide(unpackhi_epi8);
    hide(w32);
    lemma_sad_block(x8, z8);
    lemma_madd_block(x8, z8, wl, wh);
    assert(2040 * k * k + 2040 * k <= 2040 * (k + 1) * (k + 1)) by (nonlinear_arith) requires k >= 0;
    assert(2040 * (k + 1) * (k + 1) < 4294967296) by (nonlinear_arith) requires 0 <= k < 1024;
    assert(11730 * (k + 1) < 4294967296);
    lemma_add_lane(vp, vs, 0); lemma_add_lane(vp, vs, 1); lemma_add_lane(vp, vs, 2); lemma_add_lane(vp, vs, 3);
    lemma_add_lane(vs, sd, 0); lemma_add_lane(vs, sd, 1); lemma_add_lane(vs, sd, 2); lemma_add_lane(vs, sd, 3);
    lemma_add_lane(vw, m, 0); lemma_add_lane(vw, m, 1); lemma_add_lane(vw, m, 2); lemma_add_lane(vw, m, 3);
    lemma_acc_step(c0, x8, k, w32(vs, 0) + w32(vs, 2), w32(vp, 0) + w32(vp, 2),
                   w32(vw, 0) + w32(vw, 1) + w32(vw, 2) + w32(vw, 3),
                   w32(sd, 0) + w32(sd, 2), w32(m, 0) + w32(m, 1) + w32(m, 2) + w32(m, 3));
}

/// `adler_blocks`'s accumulators after `k` blocks `c`: the bytes' sum over
/// `vs`'s lanes 0 and 2; 16 times `vp`'s lanes plus `vw`'s, their weighted
/// sum; every lane below 2^32.
#[cfg(target_arch = "x86_64")]
spec fn aw_inv(vs: Seq<u8>, vp: Seq<u8>, vw: Seq<u8>, c: Seq<u8>, k: int) -> bool {
    use vsimd::spec::w32;
    &&& w32(vs, 0) + w32(vs, 2) == sumi(c, 16 * k) && w32(vs, 1) == 0 && w32(vs, 3) == 0
    &&& 0 <= w32(vs, 0) <= 2040 * k && 0 <= w32(vs, 2) <= 2040 * k
    &&& 16 * (w32(vp, 0) + w32(vp, 1) + w32(vp, 2) + w32(vp, 3)) + (w32(vw, 0) + w32(vw, 1) + w32(vw, 2) + w32(vw, 3))
            == wsumi(c, 16 * k)
    &&& w32(vp, 1) == 0 && w32(vp, 3) == 0
    &&& 0 <= w32(vp, 0) <= 2040 * k * k && 0 <= w32(vp, 2) <= 2040 * k * k
    &&& 0 <= w32(vw, 0) <= 11730 * k && 0 <= w32(vw, 1) <= 11730 * k
    &&& 0 <= w32(vw, 2) <= 11730 * k && 0 <= w32(vw, 3) <= 11730 * k
}

/// The accumulators past one more block.
proof fn lemma_acc_step(c0: Seq<u8>, e: Seq<u8>, k: int, sv: int, pv: int, wv: int, sd: int, mv: int)
    requires
        k >= 0, c0.len() == 16 * k, e.len() == 16,
        sv == sumi(c0, 16 * k), 16 * pv + wv == wsumi(c0, 16 * k),
        sd == sumi(e, 16), mv == wsumi(e, 16),
    ensures
        sv + sd == sumi(c0 + e, 16 * k + 16),
        16 * (pv + sv) + (wv + mv) == wsumi(c0 + e, 16 * k + 16),
{
    lemma_sumi_cat(c0, e);
}

/// The sums `adler_run_x` takes of the `16 * nb` bytes from `i`, sixteen
/// bytes a step in SSE2: the bytes' sum, and their sum weighted by the
/// number of bytes from each to the end. The lanes are reduced once, at
/// the end; 1024 blocks keep every lane below 2^32.
#[cfg(target_arch = "x86_64")]
fn adler_blocks(s: &[u8], i: usize, nb: usize) -> (r: (u64, u64))
    requires i + 16 * nb <= s@.len(), nb <= 1024,
    ensures ({
        let c = s@.subrange(i as int, i + 16 * nb);
        r.0 as int == sumi(c, 16 * nb as int) && r.1 as int == wsumi(c, 16 * nb as int)
    }),
{
    hide(vsimd::spec::add_epi32);
    hide(vsimd::spec::madd_epi16);
    hide(vsimd::spec::sad_epu8);
    hide(vsimd::spec::unpacklo_epi8);
    hide(vsimd::spec::unpackhi_epi8);
    let z = setzero();
    let wlo = from_bytes([16u8, 0, 15, 0, 14, 0, 13, 0, 12, 0, 11, 0, 10, 0, 9, 0]);
    let whi = from_bytes([8u8, 0, 7, 0, 6, 0, 5, 0, 4, 0, 3, 0, 2, 0, 1, 0]);
    proof {
        assert(v8(wlo) =~= seq![16u8, 0, 15, 0, 14, 0, 13, 0, 12, 0, 11, 0, 10, 0, 9, 0]);
        assert(v8(whi) =~= seq![8u8, 0, 7, 0, 6, 0, 5, 0, 4, 0, 3, 0, 2, 0, 1, 0]);
    }
    let slen = s.len();
    let mut vs = z;
    let mut vp = z;
    let mut vw = z;
    let mut k: usize = 0;
    proof {
        assert(l32(z, 0) == 0 && l32(z, 1) == 0 && l32(z, 2) == 0 && l32(z, 3) == 0);
        assert(s@.subrange(i as int, i as int) =~= Seq::<u8>::empty());
        assert(aw_inv(v8(vs), v8(vp), v8(vw), s@.subrange(i as int, i as int), 0));
    }
    while k < nb
        invariant
            k <= nb, nb <= 1024, i + 16 * nb <= s@.len(), slen == s@.len(),
            v8(z) == vsimd::spec::set1_epi8(0),
            v8(wlo) == seq![16u8, 0, 15, 0, 14, 0, 13, 0, 12, 0, 11, 0, 10, 0, 9, 0],
            v8(whi) == seq![8u8, 0, 7, 0, 6, 0, 5, 0, 4, 0, 3, 0, 2, 0, 1, 0],
            aw_inv(v8(vs), v8(vp), v8(vw), s@.subrange(i as int, i + 16 * k), k as int),
        decreases nb - k,
    {
        let x = loadu(s, i + 16 * k);
        let vp2 = add_epi32(vp, vs);
        let sd = sad_epu8(x, z);
        let vs2 = add_epi32(vs, sd);
        let lo = unpacklo_epi8(x, z);
        let hi = unpackhi_epi8(x, z);
        let m = add_epi32(madd_epi16(lo, wlo), madd_epi16(hi, whi));
        let vw2 = add_epi32(vw, m);
        proof {
            let c0 = s@.subrange(i as int, i + 16 * k);
            let e = s@.subrange(i + 16 * k, i + 16 * k + 16);
            lemma_loop_step(v8(vs), v8(vp), v8(vw), v8(vs2), v8(vp2), v8(vw2), v8(x), v8(z), v8(wlo), v8(whi),
                            v8(sd), v8(m), c0, k as int);
            assert(s@.subrange(i as int, i + 16 * (k + 1)) =~= c0 + e);
        }
        vp = vp2;
        vs = vs2;
        vw = vw2;
        k = k + 1;
    }
    let bs = to_bytes(vs);
    let bp = to_bytes(vp);
    let bw = to_bytes(vw);
    let sum = (vsimd::model::w32_x(&bs, 0) + vsimd::model::w32_x(&bs, 2)) as u64;
    let pp = (vsimd::model::w32_x(&bp, 0) + vsimd::model::w32_x(&bp, 2)) as u64;
    let ww = (vsimd::model::w32_x(&bw, 0) + vsimd::model::w32_x(&bw, 1) + vsimd::model::w32_x(&bw, 2)
        + vsimd::model::w32_x(&bw, 3)) as u64;
    (sum, 16 * pp + ww)
}

/// Adler-32's sums (reduced) after `p`, continued over `s`: unreduced
/// within each 64 KB, reduced after (the sums stay below 2^42).
pub fn adler_run_x(a0: u32, b0: u32, s: &[u8], Ghost(p): Ghost<Seq<u8>>) -> (r: (u32, u32))
    requires a0 as nat == adler_a(p) % 65521, b0 as nat == adler_b(p) % 65521,
    ensures r.0 as nat == adler_a(p + s@) % 65521, r.1 as nat == adler_b(p + s@) % 65521,
{
    let m: u64 = 65521;
    let mut a: u64 = a0 as u64;
    let mut b: u64 = b0 as u64;
    let mut i: usize = 0;
    let ghost ps = p + s@;
    proof { assert(ps.take(p.len() as int) =~= p); }
    while i < s.len()
        invariant
            i <= s.len(), m == 65521, ps == p + s@,
            a as nat == adler_a(ps.take(p.len() + i)) % 65521,
            b as nat == adler_b(ps.take(p.len() + i)) % 65521,
        decreases s.len() - i,
    {
        let end = if s.len() - i > 65536 { i + 65536 } else { s.len() };
        let i0 = i;
        // up to 1024 sixteen-byte blocks at a time in SSE2
        #[cfg(target_arch = "x86_64")]
        {
            while end - i >= 16
                invariant
                    i0 <= i <= end, end <= s.len(), end - i0 <= 65536, m == 65521, ps == p + s@,
                    a as int % 65521 == adler_a(ps.take(p.len() + i)) % 65521,
                    b as int % 65521 == adler_b(ps.take(p.len() + i)) % 65521,
                    a < 0x200_0000, b < (i - i0 + 1) * 0x200_0000,
                    a <= 65521 + 255 * (i - i0),
                decreases end - i,
            {
                let nb0 = (end - i) / 16;
                let nb = if nb0 > 1024 { 1024 } else { nb0 };
                let (sm, ws) = adler_blocks(s, i, nb);
                let n = 16 * nb;
                proof {
                    let c = s@.subrange(i as int, i + n);
                    let t = ps.take(p.len() + i);
                    assert(ps.take(p.len() + i + n) =~= t + c);
                    lemma_adler_app(t, c);
                    lemma_sumi_bound(c, n as int);
                    lemma_adler_mod(a as int, b as int, adler_a(t) as int, adler_b(t) as int, n as int, sm as int, ws as int);
                    let ni = n as int;
                    let ai = a as int;
                    assert(ni * ai <= ni * 16777201) by (nonlinear_arith) requires 0 <= ai <= 16777201, ni >= 0;
                    assert(255 * ni * ni <= ni * 4177920) by (nonlinear_arith) requires 0 <= ni <= 16384;
                    assert(ni * 16777201 + ni * 4177920 <= ni * 0x200_0000) by (nonlinear_arith) requires ni >= 0;
                    assert((i - i0 + 1) * 0x200_0000 + ni * 0x200_0000 == (i + ni - i0 + 1) * 0x200_0000) by (nonlinear_arith);
                }
                b = b + (n as u64) * a + ws;
                a = a + sm;
                i = i + n;
            }
        }
        // sixteen bytes at a time from a slice of sixteen (no bounds checks)
        while end - i >= 16
            invariant
                i0 <= i <= end, end <= s.len(), end - i0 <= 65536, m == 65521, ps == p + s@,
                a as int % 65521 == adler_a(ps.take(p.len() + i)) % 65521,
                b as int % 65521 == adler_b(ps.take(p.len() + i)) % 65521,
                a < 0x200_0000, b < (i - i0 + 1) * 0x200_0000,
                a <= 65521 + 255 * (i - i0),
            decreases end - i,
        {
            let c = vstd::slice::slice_subrange(s, i, i + 16);
            let mut j: usize = 0;
            while j < 16
                invariant
                    i0 <= i, i + 16 <= end, end <= s.len(), end - i0 <= 65536, m == 65521, ps == p + s@,
                    c@ == s@.subrange(i as int, i + 16), j <= 16,
                    a as int % 65521 == adler_a(ps.take(p.len() + i + j)) % 65521,
                    b as int % 65521 == adler_b(ps.take(p.len() + i + j)) % 65521,
                    a <= 65521 + 255 * (i + j - i0), b < (i + j - i0 + 1) * 0x200_0000,
                decreases 16 - j,
            {
                let x = c[j] as u64;
                let ghost k = p.len() + i + j;
                let ghost (a1, b1) = (a as int, b as int);
                proof {
                    let t = ps.take(k + 1);
                    assert(t.drop_last() =~= ps.take(k));
                    assert(t.last() == s@[i + j]);
                    vstd::arithmetic::div_mod::lemma_add_mod_noop(a1, x as int, 65521);
                    vstd::arithmetic::div_mod::lemma_add_mod_noop(adler_a(ps.take(k)) as int, x as int, 65521);
                }
                a = a + x;
                proof {
                    let t = ps.take(k + 1);
                    vstd::arithmetic::div_mod::lemma_add_mod_noop(b1, a as int, 65521);
                    vstd::arithmetic::div_mod::lemma_add_mod_noop(adler_b(ps.take(k)) as int, adler_a(t) as int, 65521);
                }
                b = b + a;
                j = j + 1;
            }
            i = i + 16;
        }
        while i < end
            invariant
                i0 <= i <= end, end <= s.len(), end - i0 <= 65536, m == 65521, ps == p + s@,
                a as int % 65521 == adler_a(ps.take(p.len() + i)) % 65521,
                b as int % 65521 == adler_b(ps.take(p.len() + i)) % 65521,
                a < 0x200_0000, b < (i - i0 + 1) * 0x200_0000,
                a <= 65521 + 255 * (i - i0),
            decreases end - i,
        {
            let x = s[i] as u64;
            let ghost k = p.len() + i;
            let ghost (a1, b1) = (a as int, b as int);
            proof {
                let t = ps.take(k + 1);
                assert(t.drop_last() =~= ps.take(k));
                assert(t.last() == s@[i as int]);
                vstd::arithmetic::div_mod::lemma_add_mod_noop(a1, x as int, 65521);
                vstd::arithmetic::div_mod::lemma_add_mod_noop(adler_a(ps.take(k)) as int, x as int, 65521);
            }
            a = a + x;
            proof {
                let t = ps.take(k + 1);
                vstd::arithmetic::div_mod::lemma_add_mod_noop(b1, a as int, 65521);
                vstd::arithmetic::div_mod::lemma_add_mod_noop(adler_b(ps.take(k)) as int, adler_a(t) as int, 65521);
            }
            b = b + a;
            i = i + 1;
        }
        a = a % m;
        b = b % m;
    }
    proof { assert(ps.take(p.len() + s.len()) =~= ps); }
    (a as u32, b as u32)
}

pub open spec fn gz_hdr() -> Seq<u8> { seq![0x1fu8, 0x8bu8, 8u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0xffu8] }

pub open spec fn gz_tail(c: u32, z: u32) -> Seq<u8> {
    seq![c as u8, (c >> 8) as u8, (c >> 16) as u8, (c >> 24) as u8, z as u8, (z >> 8) as u8, (z >> 16) as u8, (z >> 24) as u8]
}

pub open spec fn zl_tail(a: u32) -> Seq<u8> {
    seq![(a >> 24) as u8, (a >> 16) as u8, (a >> 8) as u8, a as u8]
}

/// A gzip member around a DEFLATE stream of `data`.
pub proof fn lemma_gzip_out(data: Seq<u8>, body: Seq<u8>, c: u32, z: u32, o: Seq<u8>)
    requires
        crate::enc2::deflate_ok(data, body), c == crc32(data), z as nat == data.len() % 0x1_0000_0000,
        o == gz_hdr() + (body + gz_tail(c, z)),
    ensures gzip_decode(o) matches Some((d, n, zl)) && d == data && n == o.len() && zl,
{
    let tail = gz_tail(c, z);
    assert(o.skip(10) =~= body + tail);
    assert(o.take(10) =~= gz_hdr());
    assert(gzip_header(o) == Some(10int));
    let (q, st) = choose|q: nat, st: bool| #![trigger crate::enc2::inflate_q(body, q, st)]
        crate::enc2::inflate_q(body, q, st) && st && (q + 7) / 8 == body.len()
        && forall|b: Seq<bool>| #[trigger] crate::step::is_prefix(lbits(body), b) ==> inflate(b) == Some((data, q, st));
    lemma_body_then(body, tail);
    assert(inflate(lbits(o.skip(10))) == Some((data, q, st)));
    let a = 10 + body.len() as int;
    assert(after_bits(10, q) == a);
    lemma_u32_bytes_le(c);
    lemma_u32_bytes_le(z);
    assert(o[a] == tail[0] && o[a + 1] == tail[1] && o[a + 2] == tail[2] && o[a + 3] == tail[3]);
    assert(o[a + 4] == tail[4] && o[a + 5] == tail[5] && o[a + 6] == tail[6] && o[a + 7] == tail[7]);
}

} // verus!

