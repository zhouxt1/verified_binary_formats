//! The pixelwise inverse transforms four pixels at a time in SSE2, after
//! libwebp's AddGreenToBlueAndRed_SSE2 and TransformColorInverse_SSE2: each
//! proved, byte by byte, to give the spec's pixels. A pixel is a 32-bit lane
//! whose bytes are blue, green, red, alpha (lowest first).
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vsimd::spec::{w16, sw16, w32, put16, put32, u32s, lemma_mulhi_lane, lemma_w16_bounds};
#[cfg(verus_keep_ghost)]
use vsimd::x86::{v8, byte, lemma_byte};
use vsimd::x86::__m128i;
use vsimd::x86 as sx;
use crate::spec::*;
use crate::inv::*;
#[cfg(verus_keep_ghost)]
use vbits::bitspec::p2;

verus! {

broadcast use lemma_byte;

// ---------------------------------------------------------- bytes of pixels

/// Byte `q` of a pixel, the way a 32-bit lane holds it.
pub open spec fn pb(c: u32, q: int) -> u8 { put32(c as int, q) }

/// The four bytes are blue, green, red and alpha.
pub proof fn lemma_pb(c: u32)
    ensures pb(c, 0) as int == blue(c), pb(c, 1) as int == green(c), pb(c, 2) as int == red(c), pb(c, 3) as int == alpha(c),
{
    vstd::bits::lemma_u32_shr_is_div(c, 8);
    vstd::bits::lemma_u32_shr_is_div(c, 16);
    vstd::bits::lemma_u32_shr_is_div(c, 24);
    vstd::arithmetic::power2::lemma2_to64();
    assert(c & 0xffu32 == c % 256) by (bit_vector);
    assert((c >> 8u32) & 0xffu32 == (c >> 8u32) % 256) by (bit_vector);
    assert((c >> 16u32) & 0xffu32 == (c >> 16u32) % 256) by (bit_vector);
    assert(c >> 24u32 < 256) by (bit_vector);
    assert((c as int % 4294967296) == c as int);
}

/// A pixel from its four bytes, as a lane is stored.
pub proof fn lemma_pack(b0: u8, b1: u8, b2: u8, b3: u8)
    ensures (b0 as int + 256 * b1 as int + 65536 * b2 as int + 16777216 * b3 as int) as u32
        == argb(b3 as int, b2 as int, b1 as int, b0 as int),
{
    let (x0, x1, x2, x3) = (b0 as u32, b1 as u32, b2 as u32, b3 as u32);
    assert(crate::spec::byte(b0 as int) == x0 && crate::spec::byte(b1 as int) == x1 && crate::spec::byte(b2 as int) == x2 && crate::spec::byte(b3 as int) == x3);
    assert((x3 << 24u32) | (x2 << 16u32) | (x1 << 8u32) | x0
        == (x0 + 256 * x1 + 65536 * x2 + 16777216 * x3) as u32) by (bit_vector)
        requires x0 < 256, x1 < 256, x2 < 256, x3 < 256;
}

// --------------------------------------------- byte moves by shifts

pub proof fn lemma_srli16_8(a: Seq<u8>, k: int)
    requires a.len() == 16, 0 <= k < 16,
    ensures vsimd::spec::srli_epi16(a, 8)[k] == if k % 2 == 0 { a[k + 1] } else { 0u8 },
{
    vstd::arithmetic::power2::lemma2_to64();
    let j = k / 2;
    let x = w16(a, j) / 256;
    assert(x == a[2 * j + 1] as int);
}

pub proof fn lemma_slli16_8(a: Seq<u8>, k: int)
    requires a.len() == 16, 0 <= k < 16,
    ensures vsimd::spec::slli_epi16(a, 8)[k] == if k % 2 == 0 { 0u8 } else { a[k - 1] },
{
    vstd::arithmetic::power2::lemma2_to64();
    let j = k / 2;
    let x = w16(a, j) * 256;
    assert(x % 65536 == 256 * a[2 * j] as int) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, 65536, a[2 * j + 1] as int, 256 * a[2 * j] as int);
    }
    assert((256 * a[2 * j] as int) % 256 == 0 && (256 * a[2 * j] as int) / 256 == a[2 * j] as int);
}

pub proof fn lemma_srli32_8(a: Seq<u8>, k: int)
    requires a.len() == 16, 0 <= k < 16,
    ensures vsimd::spec::srli_epi32(a, 8)[k] == if k % 4 < 3 { a[k + 1] } else { 0u8 },
{
    vstd::arithmetic::power2::lemma2_to64();
    let j = k / 4;
    let (a0, a1, a2, a3) = (a[4 * j] as int, a[4 * j + 1] as int, a[4 * j + 2] as int, a[4 * j + 3] as int);
    let x = w32(a, j) / 256;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(w32(a, j), 256, a1 + 256 * a2 + 65536 * a3, a0);
    assert(x == a1 + 256 * a2 + 65536 * a3);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, 256, a2 + 256 * a3, a1);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, 65536, a3, a1 + 256 * a2);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x / 256, 256, a3, a2);
    assert(x < 16777216);
    assert(x / 16777216 == 0);
}

pub proof fn lemma_slli32_16(a: Seq<u8>, k: int)
    requires a.len() == 16, 0 <= k < 16,
    ensures vsimd::spec::slli_epi32(a, 16)[k] == if k % 4 < 2 { 0u8 } else { a[k - 2] },
{
    vstd::arithmetic::power2::lemma2_to64();
    let j = k / 4;
    let (a0, a1, a2, a3) = (a[4 * j] as int, a[4 * j + 1] as int, a[4 * j + 2] as int, a[4 * j + 3] as int);
    let x = w32(a, j) * 65536;
    let u = 65536 * (a0 + 256 * a1);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, 4294967296, a2 + 256 * a3, u);
    assert(x % 4294967296 == u);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(u / 65536, 256, a1, a0);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(u, 256, 256 * (a0 + 256 * a1), 0);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(u, 65536, a0 + 256 * a1, 0);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(u, 16777216, a1, 65536 * a0);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(u / 256, 256, 256 * a1 + a0 * 1, 0);
}

// ----------------------------------------------------- subtract green

/// Lane `j` of a subtract-green result is the spec's pixel.
pub proof fn lemma_sg_lane(v: Seq<u8>, r: Seq<u8>, c: u32, j: int)
    requires 0 <= j < 4, v.len() == 16, r.len() == 16,
        forall|q: int| 0 <= q < 4 ==> #[trigger] v[4 * j + q] == put32(c as int, 4 * j + q),
        forall|k: int| 0 <= k < 16 ==> #[trigger] r[k] ==
            if k % 2 == 0 { ((v[k] as int + v[(k / 4) * 4 + 1] as int) % 256) as u8 } else { v[k] },
    ensures w32(r, j) as u32 == argb(alpha(c), red(c) + green(c), green(c), blue(c) + green(c)),
{
    lemma_pb(c);
    assert forall|q: int| 0 <= q < 4 implies #[trigger] put32(c as int, 4 * j + q) == pb(c, q) by {
        assert((4 * j + q) % 4 == q % 4);
    }
    let b = 4 * j;
    assert((b / 4) * 4 + 1 == b + 1 && (b + 2) / 4 * 4 + 1 == b + 1);
    assert(b % 2 == 0 && (b + 1) % 2 == 1 && (b + 2) % 2 == 0 && (b + 3) % 2 == 1);
    assert(v[4 * j + 0] == put32(c as int, 4 * j + 0) && v[4 * j + 1] == put32(c as int, 4 * j + 1)
        && v[4 * j + 2] == put32(c as int, 4 * j + 2) && v[4 * j + 3] == put32(c as int, 4 * j + 3));
    assert(put32(c as int, 4 * j + 0) == pb(c, 0) && put32(c as int, 4 * j + 1) == pb(c, 1)
        && put32(c as int, 4 * j + 2) == pb(c, 2) && put32(c as int, 4 * j + 3) == pb(c, 3));
    assert(v[b] == pb(c, 0) && v[b + 1] == pb(c, 1) && v[b + 2] == pb(c, 2) && v[b + 3] == pb(c, 3));
    lemma_pack(r[b], r[b + 1], r[b + 2], r[b + 3]);
}

/// Four pixels' `AddGreenToBlueAndRed`: green's byte added to blue's and
/// red's (mod 256).
#[inline(always)]
pub fn sub_green4(v: __m128i) -> (r: __m128i)
    ensures forall|k: int| 0 <= k < 16 ==> #[trigger] byte(r, k) ==
        if k % 2 == 0 { ((byte(v, k) as int + byte(v, (k / 4) * 4 + 1) as int) % 256) as u8 } else { byte(v, k) },
{
    let mg = sx::set1_epi32(0x0000ff00u32);
    let t1 = sx::and_si128(v, mg);            // 0 g 0 0
    let t2 = sx::srli_epi16_8(t1);            // g 0 0 0
    let t3 = sx::slli_epi32_16(t2);           // 0 0 g 0
    let t4 = sx::or_si128(t2, t3);            // g 0 g 0
    let r = sx::add_epi8(v, t4);
    proof {
        assert forall|k: int| 0 <= k < 16 implies #[trigger] byte(r, k) ==
            if k % 2 == 0 { ((byte(v, k) as int + byte(v, (k / 4) * 4 + 1) as int) % 256) as u8 } else { byte(v, k) } by {
            let m = k % 4;
            let b = (k / 4) * 4;
            assert(put32(0x0000ff00, b) == 0u8 && put32(0x0000ff00, b + 1) == 255u8
                && put32(0x0000ff00, b + 2) == 0u8 && put32(0x0000ff00, b + 3) == 0u8) by {
                assert(b % 4 == 0 && (b + 1) % 4 == 1 && (b + 2) % 4 == 2 && (b + 3) % 4 == 3);
            }
            assert forall|q: int| 0 <= q < 16 implies #[trigger] v8(t1)[q] ==
                if q % 4 == 1 { byte(v, q) } else { 0u8 } by {
                assert((q / 4) * 4 + q % 4 == q);
                vsimd::idiom::lemma_and_mask(byte(v, q));
            }
            lemma_srli16_8(v8(t1), k);
            lemma_srli16_8(v8(t1), b);
            lemma_slli32_16(v8(t2), k);
            lemma_srli16_8(v8(t1), b + 2);
            assert(v8(t2)[b] == byte(v, b + 1));
            lemma_srli16_8(v8(t1), b + 1);
            assert(v8(t2)[b + 1] == 0u8);
            if m == 2 { lemma_srli16_8(v8(t1), k - 2); }
            let g = byte(v, b + 1);
            assert(v8(t4)[k] == if m == 0 || m == 2 { g } else { 0u8 }) by {
                assert(0u8 | 0u8 == 0u8 && g | 0u8 == g && 0u8 | g == g) by (bit_vector);
            }
            if k % 2 == 1 {
                assert(((byte(v, k) as int + 0) % 256) as u8 == byte(v, k));
            }
        }
    }
    r
}


// ------------------------------------------------------ color transform

/// A 16-bit lane's bytes.
pub proof fn lemma_w16_bytes(a: Seq<u8>, j: int)
    requires 0 <= j < 8, a.len() == 16,
    ensures w16(a, j) % 256 == a[2 * j] as int, w16(a, j) / 256 == a[2 * j + 1] as int,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(w16(a, j), 256, a[2 * j + 1] as int, a[2 * j] as int);
}

/// A 16-bit lane whose low byte is 0 and high byte x, signed, is 256 sbyte(x).
pub proof fn lemma_sw16_hi(a: Seq<u8>, j: int)
    requires 0 <= j < 8, a.len() == 16, a[2 * j] == 0,
    ensures sw16(a, j) == 256 * sbyte(a[2 * j + 1] as int),
{}

/// A 16-bit lane of `set1_epi32(lo + 65536 * hi)`.
pub proof fn lemma_set1_32_16(lo: int, hi: int, j: int)
    requires 0 <= lo < 65536, 0 <= hi < 65536, 0 <= j < 8,
    ensures w16(vsimd::spec::set1_epi32((lo + 65536 * hi) as u32), j) == if j % 2 == 0 { lo } else { hi },
{
    let x = lo + 65536 * hi;
    let a = vsimd::spec::set1_epi32(x as u32);
    let (k0, k1) = (2 * j, 2 * j + 1);
    assert(a[k0] == put32(x, k0) && a[k1] == put32(x, k1));
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, 65536, hi, lo);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(lo, 256, lo / 256, lo % 256);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(hi, 256, hi / 256, hi % 256);
    vstd::arithmetic::div_mod::lemma_div_denominator(x, 256, 256);
    vstd::arithmetic::div_mod::lemma_div_denominator(x, 65536, 256);
    assert(x / 256 == 256 * hi + lo / 256) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, 256, 256 * hi + lo / 256, lo % 256);
    }
    assert(x / 16777216 == hi / 256) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, 16777216, hi / 256, lo + 65536 * (hi % 256));
    }
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x / 256, 256, hi, lo / 256);
    assert((x / 256) % 256 == (lo / 256) % 256);
    assert(lo / 256 < 256);
    assert(k0 % 4 == 0 || k0 % 4 == 2);
    assert((k0 % 4 == 0) == (j % 2 == 0));
    assert(k1 % 4 == k0 % 4 + 1);
}

/// The 16-bit multiplier of `ColorTransformDelta`: 8 times the signed
/// byte, mod 2^16 (libwebp's CST_5b).
pub open spec fn cst(m: int) -> int { (8 * m) % 65536 }

#[inline(always)]
fn cst_x(m: i32) -> (r: u32)
    requires -128 <= m < 128,
    ensures r as int == cst(m as int), r < 65536,
{
    let u = (8 * m + 65536) as u32;
    let r = u & 0xffffu32;
    proof {
        assert(r == u % 65536) by (bit_vector) requires r == u & 0xffffu32;
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(1, 8 * m as int, 65536);
    }
    r
}

/// The multipliers for `inv_color4` of an element whose three multipliers
/// as signed bytes are given.
#[inline(always)]
pub fn color_mults(g2r: i32, g2b: i32, r2b: i32) -> (r: (__m128i, __m128i))
    requires -128 <= g2r < 128, -128 <= g2b < 128, -128 <= r2b < 128,
    ensures
        v8(r.0) == vsimd::spec::set1_epi32((cst(g2b as int) + 65536 * cst(g2r as int)) as u32),
        v8(r.1) == vsimd::spec::set1_epi32((0 + 65536 * cst(r2b as int)) as u32),
{
    let x = cst_x(g2b);
    let y = cst_x(g2r);
    let z = cst_x(r2b);
    let a = x | (y << 16u32);
    let b = z << 16u32;
    proof {
        assert((x | (y << 16u32)) == x + 65536 * y) by (bit_vector) requires x < 65536, y < 65536;
        assert((z << 16u32) == 65536 * z) by (bit_vector) requires z < 65536;
    }
    (sx::set1_epi32(a), sx::set1_epi32(b))
}

/// Four pixels' inverse color transform, each with the element whose
/// multipliers `color_mults` made `mrb` and `m2`.
#[inline(always)]
pub fn inv_color4(v: __m128i, mrb: __m128i, m2: __m128i) -> (r: __m128i)
    ensures inv_color4_ok(v8(v), v8(mrb), v8(m2), v8(r)),
{
    let mag = sx::set1_epi32(0xff00ff00u32);
    let mg = sx::set1_epi32(0x0000ff00u32);
    let a = sx::and_si128(v, mag);           // 0 g 0 a
    let g1 = sx::and_si128(v, mg);           // 0 g 0 0
    let g2 = sx::slli_epi32_16(g1);          // 0 0 0 g
    let c = sx::or_si128(g1, g2);            // 0 g 0 g
    let d = sx::mulhi_epi16(c, mrb);         // dgb . dgr .
    let e = sx::add_epi8(v, d);              // b' . r' .
    let f = sx::slli_epi16_8(e);             // 0 b' 0 r'
    let g = sx::mulhi_epi16(f, m2);          // 0 0 drb .
    let h = sx::srli_epi32_8(g);             // 0 drb . 0
    let i = sx::add_epi8(h, f);              // 0 b'' . r'
    let j = sx::srli_epi16_8(i);             // b'' 0 r' 0
    let r = sx::or_si128(j, a);
    proof {
        assert(inv_color4_steps(v8(v), v8(mrb), v8(m2), v8(a), v8(g1), v8(g2), v8(c), v8(d), v8(e), v8(f), v8(g),
                                v8(h), v8(i), v8(j), v8(r)));
    }
    r
}

pub open spec fn inv_color4_steps(v: Seq<u8>, mrb: Seq<u8>, m2: Seq<u8>, a: Seq<u8>, g1: Seq<u8>, g2: Seq<u8>, c: Seq<u8>,
                                  d: Seq<u8>, e: Seq<u8>, f: Seq<u8>, g: Seq<u8>, h: Seq<u8>, i: Seq<u8>, j: Seq<u8>, r: Seq<u8>) -> bool {
    &&& v.len() == 16 && mrb.len() == 16 && m2.len() == 16
    &&& a == vsimd::spec::and_si128(v, vsimd::spec::set1_epi32(0xff00ff00u32))
    &&& g1 == vsimd::spec::and_si128(v, vsimd::spec::set1_epi32(0x0000ff00u32))
    &&& g2 == vsimd::spec::slli_epi32(g1, 16)
    &&& c == vsimd::spec::or_si128(g1, g2)
    &&& d == vsimd::spec::mulhi_epi16(c, mrb)
    &&& e == vsimd::spec::add_epi8(v, d)
    &&& f == vsimd::spec::slli_epi16(e, 8)
    &&& g == vsimd::spec::mulhi_epi16(f, m2)
    &&& h == vsimd::spec::srli_epi32(g, 8)
    &&& i == vsimd::spec::add_epi8(h, f)
    &&& j == vsimd::spec::srli_epi16(i, 8)
    &&& r == vsimd::spec::or_si128(j, a)
}

pub open spec fn inv_color4_ok(v: Seq<u8>, mrb: Seq<u8>, m2: Seq<u8>, r: Seq<u8>) -> bool {
    exists|a: Seq<u8>, g1: Seq<u8>, g2: Seq<u8>, c: Seq<u8>, d: Seq<u8>, e: Seq<u8>, f: Seq<u8>, g: Seq<u8>,
           h: Seq<u8>, i: Seq<u8>, j: Seq<u8>|
        inv_color4_steps(v, mrb, m2, a, g1, g2, c, d, e, f, g, h, i, j, r)
}

/// Bytes of the two masks.
proof fn lemma_masks(k: int)
    requires 0 <= k < 16,
    ensures
        put32(0xff00ff00u32 as int, k) == if k % 2 == 0 { 0u8 } else { 255u8 },
        put32(0x0000ff00u32 as int, k) == if k % 4 == 1 { 255u8 } else { 0u8 },
{}

/// A 16-bit lane of `mulhi` by `8 * m`, the high byte of a lane being `x`
/// and the low 0: its low byte is `ColorTransformDelta` mod 256.
proof fn lemma_delta_lane(a: Seq<u8>, mm: Seq<u8>, l: int, m: int)
    requires 0 <= l < 8, a.len() == 16, mm.len() == 16, a[2 * l] == 0, -128 <= m < 128,
        w16(mm, l) == cst(m),
    ensures
        vsimd::spec::mulhi_epi16(a, mm)[2 * l] as int == ((m * sbyte(a[2 * l + 1] as int)) / 32) % 256,
        sw16(vsimd::spec::mulhi_epi16(a, mm), l) == (m * sbyte(a[2 * l + 1] as int)) / 32,
{
    let d = vsimd::spec::mulhi_epi16(a, mm);
    lemma_sw16_hi(a, l);
    lemma_w16_bounds(mm, l);
    assert(sw16(mm, l) == 8 * m);
    lemma_mulhi_lane(a, mm, l);
    let x = sbyte(a[2 * l + 1] as int);
    let y = m * x;
    assert(256 * x * (8 * m) == y * 2048) by (nonlinear_arith) requires y == m * x;
    let q = y / 32;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(y, 32);
    assert(y * 2048 == q * 65536 + (y % 32) * 2048) by (nonlinear_arith) requires y == q * 32 + y % 32;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(y * 2048, 65536, q, (y % 32) * 2048);
    assert(sw16(a, l) * sw16(mm, l) / 65536 == q);
    lemma_w16_bytes(d, l);
    assert(w16(d, l) == q % 65536);
    vstd::arithmetic::div_mod::lemma_mod_mod(q, 256, 256);
    assert(q % 65536 % 256 == q % 256);
}


/// The masked and broadcast greens: a = 0 g 0 alpha, cc = 0 g 0 g.
#[verifier::spinoff_prover]
proof fn lemma_stage1(v: Seq<u8>, a: Seq<u8>, g1: Seq<u8>, g2: Seq<u8>, cc: Seq<u8>, b: int)
    requires 0 <= b <= 12, b % 4 == 0, v.len() == 16,
        a == vsimd::spec::and_si128(v, vsimd::spec::set1_epi32(0xff00ff00u32)),
        g1 == vsimd::spec::and_si128(v, vsimd::spec::set1_epi32(0x0000ff00u32)),
        g2 == vsimd::spec::slli_epi32(g1, 16),
        cc == vsimd::spec::or_si128(g1, g2),
    ensures a[b] == 0 && a[b + 1] == v[b + 1] && a[b + 2] == 0 && a[b + 3] == v[b + 3],
        cc[b] == 0 && cc[b + 1] == v[b + 1] && cc[b + 2] == 0 && cc[b + 3] == v[b + 1],
{
    assert((b + 1) % 4 == 1 && (b + 2) % 4 == 2 && (b + 3) % 4 == 3);
    lemma_masks(b); lemma_masks(b + 1); lemma_masks(b + 2); lemma_masks(b + 3);
    vsimd::idiom::lemma_and_mask(v[b]); vsimd::idiom::lemma_and_mask(v[b + 1]);
    vsimd::idiom::lemma_and_mask(v[b + 2]); vsimd::idiom::lemma_and_mask(v[b + 3]);
    lemma_slli32_16(g1, b); lemma_slli32_16(g1, b + 1); lemma_slli32_16(g1, b + 2); lemma_slli32_16(g1, b + 3);
    let c1 = v[b + 1];
    assert(0u8 | 0u8 == 0u8 && c1 | 0u8 == c1 && 0u8 | c1 == c1) by (bit_vector);
}

/// Blue and red plus their deltas from green.
#[verifier::spinoff_prover]
proof fn lemma_stage2a(v: Seq<u8>, mrb: Seq<u8>, cc: Seq<u8>, d: Seq<u8>, ee: Seq<u8>, b: int, mb: int, mr: int)
    requires 0 <= b <= 12, b % 4 == 0, v.len() == 16, cc.len() == 16, mrb.len() == 16,
        -128 <= mb < 128, -128 <= mr < 128,
        cc[b] == 0 && cc[b + 1] == v[b + 1] && cc[b + 2] == 0 && cc[b + 3] == v[b + 1],
        mrb == vsimd::spec::set1_epi32((cst(mb) + 65536 * cst(mr)) as u32),
        d == vsimd::spec::mulhi_epi16(cc, mrb),
        ee == vsimd::spec::add_epi8(v, d),
    ensures
        ee[b] as int == (v[b] as int + (mb * sbyte(v[b + 1] as int)) / 32) % 256,
        ee[b + 2] as int == (v[b + 2] as int + (mr * sbyte(v[b + 1] as int)) / 32) % 256,
{
    let l = b / 2;
    assert(2 * l == b && 2 * (l + 1) == b + 2 && l % 2 == 0 && (l + 1) % 2 == 1);
    assert(0 <= cst(mb) < 65536 && 0 <= cst(mr) < 65536);
    lemma_set1_32_16(cst(mb), cst(mr), l);
    lemma_set1_32_16(cst(mb), cst(mr), l + 1);
    lemma_delta_lane(cc, mrb, l, mb);
    lemma_delta_lane(cc, mrb, l + 1, mr);
    let qb = (mb * sbyte(v[b + 1] as int)) / 32;
    let qr = (mr * sbyte(v[b + 1] as int)) / 32;
    vstd::arithmetic::div_mod::lemma_add_mod_noop(v[b] as int, qb, 256);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(v[b + 2] as int, qr, 256);
    vstd::arithmetic::div_mod::lemma_mod_twice(qb, 256);
    vstd::arithmetic::div_mod::lemma_mod_twice(qr, 256);
}

/// Those in the high bytes of f.
#[verifier::spinoff_prover]
proof fn lemma_stage2(v: Seq<u8>, mrb: Seq<u8>, cc: Seq<u8>, d: Seq<u8>, ee: Seq<u8>, f: Seq<u8>, b: int, mb: int, mr: int)
    requires 0 <= b <= 12, b % 4 == 0, v.len() == 16, cc.len() == 16, mrb.len() == 16,
        -128 <= mb < 128, -128 <= mr < 128,
        cc[b] == 0 && cc[b + 1] == v[b + 1] && cc[b + 2] == 0 && cc[b + 3] == v[b + 1],
        mrb == vsimd::spec::set1_epi32((cst(mb) + 65536 * cst(mr)) as u32),
        d == vsimd::spec::mulhi_epi16(cc, mrb),
        ee == vsimd::spec::add_epi8(v, d),
        f == vsimd::spec::slli_epi16(ee, 8),
    ensures
        f[b] == 0 && f[b + 2] == 0,
        f[b + 1] as int == (v[b] as int + (mb * sbyte(v[b + 1] as int)) / 32) % 256,
        f[b + 3] as int == (v[b + 2] as int + (mr * sbyte(v[b + 1] as int)) / 32) % 256,
{
    lemma_stage2a(v, mrb, cc, d, ee, b, mb, mr);
    assert((b + 1) % 2 == 1 && (b + 3) % 2 == 1 && b % 2 == 0 && (b + 2) % 2 == 0);
    assert(ee.len() == 16);
    lemma_slli16_8(ee, b); lemma_slli16_8(ee, b + 1); lemma_slli16_8(ee, b + 2); lemma_slli16_8(ee, b + 3);
}

#[verifier::spinoff_prover]
proof fn lemma_stage3a(m2: Seq<u8>, f: Seq<u8>, g: Seq<u8>, h: Seq<u8>, b: int, m3: int)
    requires 0 <= b <= 12, b % 4 == 0, f.len() == 16, -128 <= m3 < 128,
        f[b] == 0 && f[b + 2] == 0,
        m2 == vsimd::spec::set1_epi32((0 + 65536 * cst(m3)) as u32),
        g == vsimd::spec::mulhi_epi16(f, m2),
        h == vsimd::spec::srli_epi32(g, 8),
    ensures h[b] == 0 && h[b + 1] as int == ((m3 * sbyte(f[b + 3] as int)) / 32) % 256 && h[b + 3] == 0,
{
    let l = b / 2;
    assert(2 * l == b && 2 * (l + 1) == b + 2 && l % 2 == 0 && (l + 1) % 2 == 1);
    assert(0 <= cst(m3) < 65536 && cst(0) == 0);
    lemma_set1_32_16(0, cst(m3), l);
    lemma_set1_32_16(0, cst(m3), l + 1);
    lemma_delta_lane(f, m2, l, 0);
    lemma_delta_lane(f, m2, l + 1, m3);
    let q3 = (m3 * sbyte(f[b + 3] as int)) / 32;
    assert(sw16(g, l) == 0) by { assert(0 * sbyte(f[b + 1] as int) == 0); }
    lemma_w16_bytes(g, l);
    lemma_w16_bounds(g, l);
    assert(g[b] == 0 && g[b + 1] == 0);
    assert((b + 1) % 4 == 1 && (b + 2) % 4 == 2 && (b + 3) % 4 == 3);
    lemma_srli32_8(g, b); lemma_srli32_8(g, b + 1); lemma_srli32_8(g, b + 3);
    assert(h[b] == 0 && h[b + 1] as int == q3 % 256 && h[b + 3] == 0);
}

/// The red-to-blue delta added, and the bytes put back in place.
#[verifier::spinoff_prover]
proof fn lemma_stage3(a: Seq<u8>, f: Seq<u8>, h: Seq<u8>, i: Seq<u8>, j: Seq<u8>, r: Seq<u8>, b: int, m3: int)
    requires 0 <= b <= 12, b % 4 == 0, f.len() == 16, a.len() == 16, h.len() == 16, -128 <= m3 < 128,
        f[b] == 0 && f[b + 2] == 0, a[b] == 0 && a[b + 2] == 0,
        h[b] == 0 && h[b + 1] as int == ((m3 * sbyte(f[b + 3] as int)) / 32) % 256 && h[b + 3] == 0,
        i == vsimd::spec::add_epi8(h, f),
        j == vsimd::spec::srli_epi16(i, 8),
        r == vsimd::spec::or_si128(j, a),
    ensures
        r[b] as int == ((m3 * sbyte(f[b + 3] as int)) / 32 + f[b + 1] as int) % 256,
        r[b + 1] == a[b + 1], r[b + 2] == f[b + 3], r[b + 3] == a[b + 3],
{
    let q3 = (m3 * sbyte(f[b + 3] as int)) / 32;
    vstd::arithmetic::div_mod::lemma_add_mod_noop(q3, f[b + 1] as int, 256);
    vstd::arithmetic::div_mod::lemma_mod_twice(q3, 256);
    assert(i[b + 1] as int == (q3 + f[b + 1] as int) % 256);
    assert(i[b + 3] == f[b + 3]);
    assert((b + 1) % 2 == 1 && (b + 3) % 2 == 1 && b % 2 == 0 && (b + 2) % 2 == 0);
    lemma_srli16_8(i, b); lemma_srli16_8(i, b + 1); lemma_srli16_8(i, b + 2); lemma_srli16_8(i, b + 3);
    let (x0, x2, a1, a3) = (j[b], j[b + 2], a[b + 1], a[b + 3]);
    assert(x0 | 0u8 == x0 && x2 | 0u8 == x2 && 0u8 | a1 == a1 && 0u8 | a3 == a3) by (bit_vector);
}


/// The pixel of the bytes `inv_color4` leaves in a lane.
#[verifier::spinoff_prover]
proof fn lemma_color_final(c: u32, e: u32, c0: u8, c1: u8, c2: u8, c3: u8, f1: u8, f3: u8, r0: u8, r1: u8, r2: u8, r3: u8)
    requires
        c0 as int == blue(c), c1 as int == green(c), c2 as int == red(c), c3 as int == alpha(c),
        -128 <= sbyte(green(e)) < 128, -128 <= sbyte(blue(e)) < 128, -128 <= sbyte(red(e)) < 128,
        f1 as int == (c0 as int + (sbyte(green(e)) * sbyte(c1 as int)) / 32) % 256,
        f3 as int == (c2 as int + (sbyte(blue(e)) * sbyte(c1 as int)) / 32) % 256,
        r0 as int == ((sbyte(red(e)) * sbyte(f3 as int)) / 32 + f1 as int) % 256,
        r1 == c1, r2 == f3, r3 == c3,
    ensures (r0 as int + 256 * r1 as int + 65536 * r2 as int + 16777216 * r3 as int) as u32 == inv_color_px(c, e),
{
    let gc = green(c);
    let nr = (red(c) + ct_delta(blue(e), gc)) % 256;
    let nb = (blue(c) + ct_delta(green(e), gc) + ct_delta(red(e), nr)) % 256;
    assert(sbyte(green(e)) * sbyte(gc) == sbyte(gc) * sbyte(green(e))) by (nonlinear_arith);
    assert(sbyte(blue(e)) * sbyte(gc) == sbyte(gc) * sbyte(blue(e))) by (nonlinear_arith);
    assert(f3 as int == nr);
    assert(sbyte(red(e)) * sbyte(nr) == sbyte(nr) * sbyte(red(e))) by (nonlinear_arith);
    let q3 = ct_delta(red(e), nr);
    let bp = (blue(c) + ct_delta(green(e), gc)) % 256;
    assert(f1 as int == bp);
    assert(r0 as int == nb) by {
        vstd::arithmetic::div_mod::lemma_add_mod_noop(q3, blue(c) + ct_delta(green(e), gc), 256);
        vstd::arithmetic::div_mod::lemma_mod_twice(blue(c) + ct_delta(green(e), gc), 256);
        vstd::arithmetic::div_mod::lemma_add_mod_noop(q3, bp, 256);
    }
    lemma_pack(r0, r1, r2, r3);
    assert(crate::spec::byte(nb) == r0 as u32 && crate::spec::byte(nr) == r2 as u32);
}

/// The bytes lane `jj` of `inv_color4` holds, for multipliers `mb`, `mr`, `m3`.
#[verifier::spinoff_prover]
proof fn lemma_color_bytes(v: Seq<u8>, mrb: Seq<u8>, m2: Seq<u8>, r: Seq<u8>, jj: int, mb: int, mr: int, m3: int)
    requires
        0 <= jj < 4, inv_color4_ok(v, mrb, m2, r), -128 <= mb < 128, -128 <= mr < 128, -128 <= m3 < 128,
        mrb == vsimd::spec::set1_epi32((cst(mb) + 65536 * cst(mr)) as u32),
        m2 == vsimd::spec::set1_epi32((0 + 65536 * cst(m3)) as u32),
    ensures ({
        let b = 4 * jj;
        let f1 = (v[b] as int + (mb * sbyte(v[b + 1] as int)) / 32) % 256;
        let f3 = (v[b + 2] as int + (mr * sbyte(v[b + 1] as int)) / 32) % 256;
        &&& r[b] as int == ((m3 * sbyte(f3)) / 32 + f1) % 256
        &&& r[b + 1] == v[b + 1] && r[b + 2] as int == f3 && r[b + 3] == v[b + 3]
    }),
{
    let (a, g1, g2, cc, d, ee, f, g, h, i, j) = choose|a: Seq<u8>, g1: Seq<u8>, g2: Seq<u8>, cc: Seq<u8>, d: Seq<u8>, ee: Seq<u8>,
        f: Seq<u8>, g: Seq<u8>, h: Seq<u8>, i: Seq<u8>, j: Seq<u8>|
        inv_color4_steps(v, mrb, m2, a, g1, g2, cc, d, ee, f, g, h, i, j, r);
    let b = 4 * jj;
    lemma_stage1(v, a, g1, g2, cc, b);
    lemma_stage2(v, mrb, cc, d, ee, f, b, mb, mr);
    lemma_stage3a(m2, f, g, h, b, m3);
    lemma_stage3(a, f, h, i, j, r, b, m3);
}

/// Lane `jj` of `inv_color4` is the spec's pixel.
#[verifier::spinoff_prover]
pub proof fn lemma_color_lane(v: Seq<u8>, mrb: Seq<u8>, m2: Seq<u8>, r: Seq<u8>, c: u32, e: u32, jj: int)
    requires
        0 <= jj < 4, inv_color4_ok(v, mrb, m2, r), v.len() == 16, r.len() == 16,
        v[4 * jj + 0] == put32(c as int, 4 * jj + 0), v[4 * jj + 1] == put32(c as int, 4 * jj + 1),
        v[4 * jj + 2] == put32(c as int, 4 * jj + 2), v[4 * jj + 3] == put32(c as int, 4 * jj + 3),
        mrb == vsimd::spec::set1_epi32((cst(sbyte(green(e))) + 65536 * cst(sbyte(blue(e)))) as u32),
        m2 == vsimd::spec::set1_epi32((0 + 65536 * cst(sbyte(red(e)))) as u32),
    ensures w32(r, jj) as u32 == inv_color_px(c, e),
{
    let b = 4 * jj;
    lemma_pb(c);
    assert(put32(c as int, b + 0) == pb(c, 0) && put32(c as int, b + 1) == pb(c, 1)
        && put32(c as int, b + 2) == pb(c, 2) && put32(c as int, b + 3) == pb(c, 3));
    assert(-128 <= sbyte(green(e)) < 128 && -128 <= sbyte(blue(e)) < 128 && -128 <= sbyte(red(e)) < 128) by {
        assert((e >> 8u32) & 0xffu32 < 256 && e & 0xffu32 < 256 && (e >> 16u32) & 0xffu32 < 256) by (bit_vector);
    }
    lemma_color_bytes(v, mrb, m2, r, jj, sbyte(green(e)), sbyte(blue(e)), sbyte(red(e)));
    let f1 = ((v[b] as int + (sbyte(green(e)) * sbyte(v[b + 1] as int)) / 32) % 256) as u8;
    let f3 = ((v[b + 2] as int + (sbyte(blue(e)) * sbyte(v[b + 1] as int)) / 32) % 256) as u8;
    lemma_color_final(c, e, v[b], v[b + 1], v[b + 2], v[b + 3], f1, f3, r[b], r[b + 1], r[b + 2], r[b + 3]);
    assert(w32(r, jj) == r[b] as int + 256 * r[b + 1] as int + 65536 * r[b + 2] as int + 16777216 * r[b + 3] as int);
}

/// Four pixels from a multiple of 4 are in one tile (tiles are 4 or more wide).
proof fn lemma_tile4(x: u64, q: u64, bits: u64, t: u64)
    requires 2 <= bits <= 9, t == (1u64 << bits), x < 0x10000, x & 3 == 0, q < 4,
    ensures ((x + q) as u64) >> bits == x >> bits,
{
    assert(((x + q) as u64) >> bits == x >> bits) by (bit_vector)
        requires 2 <= bits <= 9, t == (1u64 << bits), x < 0x10000, x & 3 == 0, q < 4;
}

/// Four pixels on, off a tile's first column, is the same tile.
proof fn lemma_tile4_next(x: u64, bits: u64, t: u64)
    requires 2 <= bits <= 9, t == (1u64 << bits), x < 0x10000, x & 3 == 0, ((x + 4) as u64) & ((t - 1) as u64) != 0,
    ensures ((x + 4) as u64) >> bits == x >> bits,
{
    assert(((x + 4) as u64) >> bits == x >> bits) by (bit_vector)
        requires 2 <= bits <= 9, t == (1u64 << bits), x < 0x10000, x & 3 == 0, ((x + 4) as u64) & ((t - 1) as u64) != 0;
}

/// `inv_color4` on pixels `i..i + 4`, (x, y) to (x + 3, y), all of the tile
/// whose element is `e`.
#[inline(always)]
fn color4_at(px: &mut Vec<u32>, i: usize, Ghost(row): Ghost<int>, Ghost(x): Ghost<int>, Ghost(y): Ghost<int>, w: usize,
             mrb: __m128i, m2: __m128i, Ghost(e): Ghost<u32>, Ghost(bits): Ghost<u64>, Ghost(t): Ghost<u64>,
             Ghost(img): Ghost<Seq<u32>>, Ghost(px0): Ghost<Seq<u32>>, Ghost(f): Ghost<Seq<u32>>)
    requires
        2 <= bits <= 9, t == (1u64 << bits), t as nat == p2(bits as nat), 1 <= w <= 16384, 0 <= y,
        i == row + x, row == y * w, 0 <= x, x + 4 <= w, (x as u64) & 3 == 0,
        old(px)@.len() == px0.len(), f.len() == px0.len(), row + w <= px0.len(),
        f == inv_color(bits as nat, w as nat, img, px0),
        e == tile(img, bits as nat, w as nat, x as nat, y as nat),
        v8(mrb) == vsimd::spec::set1_epi32((cst(sbyte(green(e))) + 65536 * cst(sbyte(blue(e)))) as u32),
        v8(m2) == vsimd::spec::set1_epi32((0 + 65536 * cst(sbyte(red(e)))) as u32),
        forall|k: int| 0 <= k < i ==> #[trigger] old(px)@[k] == f[k],
        forall|k: int| i <= k < px0.len() ==> #[trigger] old(px)@[k] == px0[k],
    ensures
        final(px)@.len() == px0.len(),
        forall|k: int| 0 <= k < i + 4 ==> #[trigger] final(px)@[k] == f[k],
        forall|k: int| i + 4 <= k < px0.len() ==> #[trigger] final(px)@[k] == px0[k],
{
    let v = vsimd::x86::loadu_u32(px.as_slice(), i);
    let r = inv_color4(v, mrb, m2);
    let ghost pre = px@;
    vsimd::x86::storeu_u32(px, i, r);
    proof {
        assert forall|k: int| i <= k < i + 4 implies #[trigger] px@[k] == f[k] by {
            let q = k - i;
            let xq = x + q;
            lemma_tile4(x as u64, q as u64, bits, t);
            lemma_shr_div(xq as u64, bits);
            lemma_shr_div(x as u64, bits);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(k, w as int, y, xq);
            assert(tile(img, bits as nat, w as nat, xq as nat, y as nat) == e);
            assert(f[k] == inv_color_px(px0[k], e));
            assert(v8(v)[4 * q + 0] == put32(pre[k] as int, 4 * q + 0));
            assert(v8(v)[4 * q + 1] == put32(pre[k] as int, 4 * q + 1));
            assert(v8(v)[4 * q + 2] == put32(pre[k] as int, 4 * q + 2));
            assert(v8(v)[4 * q + 3] == put32(pre[k] as int, 4 * q + 3));
            lemma_color_lane(v8(v), v8(mrb), v8(m2), v8(r), pre[k], e, q);
        }
    }
}

/// `inv_color` in place (as `inv::inv_color_scalar_x`), four pixels at a
/// time with `inv_color4` where a row has four more.
pub fn inv_color_sse2(bits: u64, w: usize, h: usize, img: &Vec<u32>, px: &mut Vec<u32>)
    requires 2 <= bits <= 9, 1 <= w <= 16384, 1 <= h <= 16384, old(px)@.len() == w * h,
        tiles_wf(img@, bits as nat, w as nat, h as nat),
    ensures final(px)@ == inv_color(bits as nat, w as nat, img@, old(px)@),
{
    let ghost px0 = px@;
    let ghost f = inv_color(bits as nat, w as nat, img@, px0);
    proof { assert(w * h <= 0x1000_0000) by (nonlinear_arith) requires w <= 16384, h <= 16384; }
    let n = px.len();
    let (t, tw) = tile_dims(bits, w);
    let mut y: usize = 0;
    let mut row: usize = 0;
    while y < h
        invariant
            2 <= bits <= 9, 1 <= w <= 16384, 1 <= h <= 16384, n == w * h, n <= 0x1000_0000, px@.len() == n,
            px0.len() == n, f == inv_color(bits as nat, w as nat, img@, px0), f.len() == n,
            tiles_wf(img@, bits as nat, w as nat, h as nat),
            t as nat == p2(bits as nat), tw as nat == div_round_up(w as nat, p2(bits as nat)), t == (1u64 << bits),
            4 <= t <= 512, 1 <= tw <= 16384,
            y <= h, row == y * w,
            forall|k: int| 0 <= k < row ==> #[trigger] px@[k] == f[k],
            forall|k: int| row <= k < n ==> #[trigger] px@[k] == px0[k],
        decreases h - y,
    {
        proof {
            assert(row + w <= n) by (nonlinear_arith) requires row == y * w, y < h, n == w * h;
        }
        let ty = ((y as u64) >> bits) as usize;
        proof {
            lemma_shr_div(y as u64, bits);
            crate::pix::lemma_tile_in(w as nat, h as nat, bits as nat, 0, y as nat);
            assert(ty * tw + tw <= img@.len()) by (nonlinear_arith)
                requires ty < div_round_up(h as nat, p2(bits as nat)), img@.len() == tw * div_round_up(h as nat, p2(bits as nat));
            assert(ty <= y) by (nonlinear_arith) requires ty == y as nat / p2(bits as nat), p2(bits as nat) >= 1;
            assert(ty * tw + tw <= 16384 * 16384 + 16384) by (nonlinear_arith) requires ty < 16384, tw <= 16384;
        }
        let trow = ty * tw;
        let mut x: usize = 0;
        let mut e: u32 = 0;
        let mut g2r: i32 = 0;
        let mut g2b: i32 = 0;
        let mut r2b: i32 = 0;
        let (mut mrb, mut m2) = color_mults(0, 0, 0);
        proof {
            assert(0u64 & ((t - 1) as u64) == 0) by (bit_vector);
            assert(0u64 & 3 == 0) by (bit_vector);
            assert(0u32 & 0xffu32 == 0 && (0u32 >> 8u32) & 0xffu32 == 0 && (0u32 >> 16u32) & 0xffu32 == 0) by (bit_vector);
        }
        while x < w
            invariant
                2 <= bits <= 9, 1 <= w <= 16384, 1 <= h <= 16384, n == w * h, px@.len() == n,
                px0.len() == n, f == inv_color(bits as nat, w as nat, img@, px0), f.len() == n,
                tiles_wf(img@, bits as nat, w as nat, h as nat),
                t as nat == p2(bits as nat), tw as nat == div_round_up(w as nat, p2(bits as nat)), t == (1u64 << bits),
                4 <= t <= 512, 1 <= tw <= 16384,
                y < h, row == y * w, row + w <= n, x <= w, ty as nat == y as nat / p2(bits as nat), trow == ty * tw,
                trow + tw <= img@.len(), trow + tw <= 16384 * 16384 + 16384,
                x < w && (x as u64) & ((t - 1) as u64) != 0 ==> e == tile(img@, bits as nat, w as nat, x as nat, y as nat),
                g2r as int == sbyte(blue(e)), g2b as int == sbyte(green(e)), r2b as int == sbyte(red(e)),
                -128 <= g2r < 128, -128 <= g2b < 128, -128 <= r2b < 128,
                v8(mrb) == vsimd::spec::set1_epi32((cst(g2b as int) + 65536 * cst(g2r as int)) as u32),
                v8(m2) == vsimd::spec::set1_epi32((0 + 65536 * cst(r2b as int)) as u32),
                w - x >= 4 ==> (x as u64) & 3 == 0,
                forall|k: int| 0 <= k < row + x ==> #[trigger] px@[k] == f[k],
                forall|k: int| row + x <= k < n ==> #[trigger] px@[k] == px0[k],
            decreases w - x,
        {
            if (x as u64) & ((t - 1) as u64) == 0 {
                proof {
                    lemma_shr_div(x as u64, bits);
                    crate::pix::lemma_tile_in(w as nat, h as nat, bits as nat, x as nat, y as nat);
                }
                let tx = ((x as u64) >> bits) as usize;
                e = img[trow + tx];
                let m = crate::inv::ct_mults(e);
                g2r = m.0;
                g2b = m.1;
                r2b = m.2;
                let mm = color_mults(g2r, g2b, r2b);
                mrb = mm.0;
                m2 = mm.1;
            }
            proof {
                if x < w {
                    lemma_shr_div(x as u64, bits);
                    crate::pix::lemma_tile_in(w as nat, h as nat, bits as nat, x as nat, y as nat);
                    assert(e == tile(img@, bits as nat, w as nat, x as nat, y as nat));
                }
            }
            if w - x >= 4 {
                let i = row + x;
                proof {
                    assert(g2r as int == sbyte(blue(e)) && g2b as int == sbyte(green(e)) && r2b as int == sbyte(red(e)));
                }
                color4_at(px, i, Ghost(row as int), Ghost(x as int), Ghost(y as int), w, mrb, m2, Ghost(e), Ghost(bits), Ghost(t as u64),
                          Ghost(img@), Ghost(px0), Ghost(f));
                let ghost x0 = x;
                x = x + 4;
                proof {
                    if x < w && (x as u64) & ((t - 1) as u64) != 0 {
                        lemma_tile4_next(x0 as u64, bits, t as u64);
                        lemma_shr_div(x as u64, bits);
                        lemma_shr_div(x0 as u64, bits);
                    }
                    if w - x >= 4 {
                        assert((x as u64) & 3 == 0) by (bit_vector) requires (x0 as u64) & 3 == 0, x == x0 + 4, x < 0x10000;
                    }
                }
            } else {
            let i = row + x;
            proof {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(i as int, w as int, y as int, x as int);
                assert(f[i as int] == inv_color_px(px0[i as int], tile(img@, bits as nat, w as nat, x as nat, y as nat)));
            }
            let c = vsimd::mem::get(px.as_slice(), i);
            vsimd::mem::vset(px, i, crate::inv::inv_color_fast(c, g2r, g2b, r2b, Ghost(e)));
            x = x + 1;
            proof {
                if x < w && (x as u64) & ((t - 1) as u64) != 0 {
                    lemma_same_tile((x - 1) as u64, bits, t as u64);
                    lemma_shr_div(x as u64, bits);
                    lemma_shr_div((x - 1) as u64, bits);
                }
            }
            }
        }
        proof { assert(row + w == (y + 1) * w) by (nonlinear_arith) requires row == y * w; }
        row = row + w;
        y = y + 1;
    }
    proof {
        assert(row == n) by (nonlinear_arith) requires row == y * w, y == h, n == w * h;
        assert(px@ =~= f);
    }
}

// ------------------------------------------------ Select's distances

/// The mask bytes of `sad4`.
proof fn lemma_masks2(k: int)
    requires 0 <= k < 16,
    ensures
        put32(0x00ff00ffu32 as int, k) == if k % 2 == 0 { 255u8 } else { 0u8 },
        put32(0x0000ffffu32 as int, k) == if k % 4 < 2 { 255u8 } else { 0u8 },
{}

pub open spec fn absd4(t: Seq<u8>, tl: Seq<u8>, j: int) -> int {
    vsimd::idiom::absd8(t[4 * j], tl[4 * j]) + vsimd::idiom::absd8(t[4 * j + 1], tl[4 * j + 1])
        + vsimd::idiom::absd8(t[4 * j + 2], tl[4 * j + 2]) + vsimd::idiom::absd8(t[4 * j + 3], tl[4 * j + 3])
}

/// Each 32-bit lane: the sum of its four bytes' absolute differences.
#[verifier::spinoff_prover]
pub fn sad4(t: __m128i, tl: __m128i) -> (r: __m128i)
    ensures forall|j: int| 0 <= j < 4 ==> #[trigger] w32(v8(r), j) == absd4(v8(t), v8(tl), j),
{
    let a = vsimd::idiom::absdiff_epu8(t, tl);
    let lo = sx::and_si128(a, sx::set1_epi32(0x00ff00ffu32));
    let hi = sx::srli_epi16_8(a);
    let s = sx::add_epi16(lo, hi);
    let s1 = sx::srli_epi32_8(s);
    let s2 = sx::srli_epi32_8(s1);
    let tot = sx::add_epi16(s, s2);
    let r = sx::and_si128(tot, sx::set1_epi32(0x0000ffffu32));
    proof {
        assert forall|j: int| 0 <= j < 4 implies #[trigger] w32(v8(r), j) == absd4(v8(t), v8(tl), j) by {
            let b = 4 * j;
            assert(b % 4 == 0 && (b + 1) % 4 == 1 && (b + 2) % 4 == 2 && (b + 3) % 4 == 3);
            assert(b % 2 == 0 && (b + 1) % 2 == 1 && (b + 2) % 2 == 0 && (b + 3) % 2 == 1);
            let (a0, a1, a2, a3) = (byte(a, b), byte(a, b + 1), byte(a, b + 2), byte(a, b + 3));
            assert(a0 as int == vsimd::idiom::absd8(byte(t, b), byte(tl, b)));
            assert(a1 as int == vsimd::idiom::absd8(byte(t, b + 1), byte(tl, b + 1)));
            assert(a2 as int == vsimd::idiom::absd8(byte(t, b + 2), byte(tl, b + 2)));
            assert(a3 as int == vsimd::idiom::absd8(byte(t, b + 3), byte(tl, b + 3)));
            lemma_masks2(b); lemma_masks2(b + 1); lemma_masks2(b + 2); lemma_masks2(b + 3);
            vsimd::idiom::lemma_and_mask(a0); vsimd::idiom::lemma_and_mask(a1);
            vsimd::idiom::lemma_and_mask(a2); vsimd::idiom::lemma_and_mask(a3);
            lemma_srli16_8(v8(a), b); lemma_srli16_8(v8(a), b + 1); lemma_srli16_8(v8(a), b + 2); lemma_srli16_8(v8(a), b + 3);
            let l = 2 * j;
            assert(2 * l == b && 2 * (l + 1) == b + 2);
            assert(w16(v8(lo), l) == a0 as int && w16(v8(lo), l + 1) == a2 as int);
            assert(w16(v8(hi), l) == a1 as int && w16(v8(hi), l + 1) == a3 as int);
            vsimd::spec::lemma_add16_lane(v8(lo), v8(hi), l);
            vsimd::spec::lemma_add16_lane(v8(lo), v8(hi), l + 1);
            let (u, v) = (a0 as int + a1 as int, a2 as int + a3 as int);
            assert(w16(v8(s), l) == u && w16(v8(s), l + 1) == v);
            lemma_srli32_8(v8(s), b); lemma_srli32_8(v8(s), b + 1); lemma_srli32_8(v8(s), b + 2); lemma_srli32_8(v8(s), b + 3);
            lemma_srli32_8(v8(s1), b); lemma_srli32_8(v8(s1), b + 1); lemma_srli32_8(v8(s1), b + 2); lemma_srli32_8(v8(s1), b + 3);
            assert(v8(s2)[b] == v8(s)[b + 2] && v8(s2)[b + 1] == v8(s)[b + 3]);
            assert(w16(v8(s2), l) == w16(v8(s), l + 1));
            vsimd::spec::lemma_add16_lane(v8(s), v8(s2), l);
            assert(w16(v8(tot), l) == u + v);
            let (t0, t1) = (byte(tot, b), byte(tot, b + 1));
            vsimd::idiom::lemma_and_mask(t0); vsimd::idiom::lemma_and_mask(t1);
            vsimd::idiom::lemma_and_mask(byte(tot, b + 2)); vsimd::idiom::lemma_and_mask(byte(tot, b + 3));
            assert(byte(r, b) == t0 && byte(r, b + 1) == t1 && byte(r, b + 2) == 0 && byte(r, b + 3) == 0);
        }
    }
    r
}

/// Four pixels' `sad` against the pixels before them, from their bytes.
#[verifier::spinoff_prover]
pub proof fn lemma_sad_lane(t: Seq<u8>, tl: Seq<u8>, ct: u32, ctl: u32, j: int)
    requires 0 <= j < 4, t.len() == 16, tl.len() == 16,
        forall|q: int| 0 <= q < 4 ==> #[trigger] t[4 * j + q] == put32(ct as int, 4 * j + q),
        forall|q: int| 0 <= q < 4 ==> #[trigger] tl[4 * j + q] == put32(ctl as int, 4 * j + q),
    ensures absd4(t, tl, j) == sad(ct, ctl),
{
    lemma_pb(ct);
    lemma_pb(ctl);
    assert(t[4 * j + 0] == put32(ct as int, 4 * j + 0) && tl[4 * j + 0] == put32(ctl as int, 4 * j + 0));
    assert(t[4 * j + 1] == put32(ct as int, 4 * j + 1) && tl[4 * j + 1] == put32(ctl as int, 4 * j + 1));
    assert(t[4 * j + 2] == put32(ct as int, 4 * j + 2) && tl[4 * j + 2] == put32(ctl as int, 4 * j + 2));
    assert(t[4 * j + 3] == put32(ct as int, 4 * j + 3) && tl[4 * j + 3] == put32(ctl as int, 4 * j + 3));
    assert(put32(ct as int, 4 * j + 0) == pb(ct, 0) && put32(ct as int, 4 * j + 1) == pb(ct, 1)
        && put32(ct as int, 4 * j + 2) == pb(ct, 2) && put32(ct as int, 4 * j + 3) == pb(ct, 3));
    assert(put32(ctl as int, 4 * j + 0) == pb(ctl, 0) && put32(ctl as int, 4 * j + 1) == pb(ctl, 1)
        && put32(ctl as int, 4 * j + 2) == pb(ctl, 2) && put32(ctl as int, 4 * j + 3) == pb(ctl, 3));
}

/// `pl[x] = sad(px[up + x], px[up + x - 1])` for `x0 <= x < x1`, four at
/// a time.
pub fn fill_sad4(px: &Vec<u32>, pl: &mut Vec<u32>, up: usize, x0: usize, x1: usize, w: usize) -> (x: usize)
    requires 1 <= x0 <= x1 <= w, up + w <= px@.len(), old(pl)@.len() == w + 4, w <= 16384, px@.len() <= 0x1000_0000,
    ensures final(pl)@.len() == w + 4, x0 <= x <= x1, x1 - x < 4,
        forall|xx: int| x0 <= xx < x ==> #[trigger] final(pl)@[xx] as int == sad(px@[up + xx], px@[up + xx - 1]),
{
    let mut x = x0;
    while x1 - x >= 4
        invariant 1 <= x0 <= x <= x1 <= w, up + w <= px@.len(), pl@.len() == w + 4, px@.len() <= 0x1000_0000,
            forall|xx: int| x0 <= xx < x ==> #[trigger] pl@[xx] as int == sad(px@[up + xx], px@[up + xx - 1]),
        decreases x1 - x,
    {
        let t = sx::loadu_u32(px.as_slice(), up + x);
        let tl = sx::loadu_u32(px.as_slice(), up + x - 1);
        let r = sad4(t, tl);
        let ghost pre = pl@;
        sx::storeu_u32(pl, x, r);
        proof {
            assert forall|xx: int| x0 <= xx < x + 4 implies #[trigger] pl@[xx] as int == sad(px@[up + xx], px@[up + xx - 1]) by {
                if xx >= x {
                    let j = xx - x;
                    lemma_sad_lane(v8(t), v8(tl), px@[up + xx], px@[up + xx - 1], j);
                    assert(w32(v8(r), j) == absd4(v8(t), v8(tl), j));
                    assert(0 <= w32(v8(r), j) <= 1020);
                }
            }
        }
        x = x + 4;
    }
    x
}

// ------------------------------------------ predictors from the row above

/// Byte-wise sums of pixels are `add_pixels`.
#[verifier::spinoff_prover]
pub proof fn lemma_add_lane(a: Seq<u8>, b: Seq<u8>, ca: u32, cb: u32, j: int)
    requires 0 <= j < 4, a.len() == 16, b.len() == 16,
        forall|q: int| 0 <= q < 4 ==> #[trigger] a[4 * j + q] == put32(ca as int, 4 * j + q),
        forall|q: int| 0 <= q < 4 ==> #[trigger] b[4 * j + q] == put32(cb as int, 4 * j + q),
    ensures w32(vsimd::spec::add_epi8(a, b), j) as u32 == add_pixels(ca, cb),
{
    let r = vsimd::spec::add_epi8(a, b);
    let bb = 4 * j;
    lemma_pb(ca);
    lemma_pb(cb);
    assert(a[4 * j + 0] == put32(ca as int, 4 * j + 0) && b[4 * j + 0] == put32(cb as int, 4 * j + 0));
    assert(a[4 * j + 1] == put32(ca as int, 4 * j + 1) && b[4 * j + 1] == put32(cb as int, 4 * j + 1));
    assert(a[4 * j + 2] == put32(ca as int, 4 * j + 2) && b[4 * j + 2] == put32(cb as int, 4 * j + 2));
    assert(a[4 * j + 3] == put32(ca as int, 4 * j + 3) && b[4 * j + 3] == put32(cb as int, 4 * j + 3));
    assert(put32(ca as int, bb + 0) == pb(ca, 0) && put32(ca as int, bb + 1) == pb(ca, 1)
        && put32(ca as int, bb + 2) == pb(ca, 2) && put32(ca as int, bb + 3) == pb(ca, 3));
    assert(put32(cb as int, bb + 0) == pb(cb, 0) && put32(cb as int, bb + 1) == pb(cb, 1)
        && put32(cb as int, bb + 2) == pb(cb, 2) && put32(cb as int, bb + 3) == pb(cb, 3));
    lemma_pack(r[bb], r[bb + 1], r[bb + 2], r[bb + 3]);
    assert(w32(r, j) == r[bb] as int + 256 * r[bb + 1] as int + 65536 * r[bb + 2] as int + 16777216 * r[bb + 3] as int);
    assert(crate::spec::byte(r[bb] as int) == crate::spec::byte(blue(ca) + blue(cb)));
    assert(crate::spec::byte(r[bb + 1] as int) == crate::spec::byte(green(ca) + green(cb)));
    assert(crate::spec::byte(r[bb + 2] as int) == crate::spec::byte(red(ca) + red(cb)));
    assert(crate::spec::byte(r[bb + 3] as int) == crate::spec::byte(alpha(ca) + alpha(cb)));
}

/// What mode 0, 2, 3 or 4 predicts for pixel `i` from the row above.
pub open spec fn up_pred(mode: int, s: Seq<u32>, i: int, w: int) -> u32 {
    if mode == 2 { s[i - w] } else if mode == 3 { s[i - w + 1] } else if mode == 4 { s[i - w - 1] } else { 0xff000000u32 }
}

/// One of those four steps.
#[verifier::spinoff_prover]
proof fn lemma_up_step(bits: nat, w: nat, img: Seq<u32>, px0: Seq<u32>, pre: Seq<u32>, fin: Seq<u32>, i: int, x: int,
                       y: int, mode: int, q: int)
    requires
        mode == 0 || mode == 2 || mode == 3 || mode == 4, 0 <= q < 4, i >= w + 1,
        1 <= y, 1 <= x, x + 4 <= w, i == y * w + x, i + 4 <= px0.len(), pre.len() == px0.len(), fin.len() == px0.len(),
        forall|k: int| 0 <= k < i ==> #[trigger] fin[k] == pre[k],
        fin[i + q] == add_pixels(px0[i + q], up_pred(mode, pre, i + q, w as int)),
        green(tile(img, bits, w, (x + q) as nat, y as nat)) % 16 == mode,
    ensures inv_predictor(bits, w, img, px0, fin.take(i + q)) == inv_predictor(bits, w, img, px0, fin.take(i + q + 1)),
{
    let out = fin.take(i + q);
    lemma_prediction_at(bits, w, img, out, i + q, (x + q) as nat, y as nat, mode);
    assert(out[i + q - w] == pre[i + q - w] && out[i + q - w + 1] == pre[i + q - w + 1]
        && out[i + q - w - 1] == pre[i + q - w - 1]);
    assert(prediction(bits, w, img, out, i + q) == up_pred(mode, pre, i + q, w as int));
    crate::inv::lemma_pred_step(bits, w, img, px0, fin, i + q);
}

/// The four stored pixels.
#[verifier::spinoff_prover]
proof fn lemma_up_vals(src: Seq<u8>, up: Seq<u8>, r: Seq<u8>, pre: Seq<u32>, fin: Seq<u32>, px0: Seq<u32>, i: int, u: int,
                       w: int, mode: int)
    requires
        mode == 0 || mode == 2 || mode == 3 || mode == 4, 0 <= i, i + 4 <= pre.len(), pre.len() == px0.len(),
        fin.len() == pre.len(), i >= w + 1, w >= 1,
        forall|k: int| i <= k < px0.len() ==> #[trigger] pre[k] == px0[k],
        src == u32s(pre, i), r == vsimd::spec::add_epi8(src, up),
        u == (if mode == 2 { i - w } else if mode == 3 { i - w + 1 } else { i - w - 1 }),
        mode == 0 ==> up == vsimd::spec::set1_epi32(0xff000000u32),
        mode != 0 ==> up == u32s(pre, u),
        forall|j: int| 0 <= j < fin.len() ==> #[trigger] fin[j] == if i <= j < i + 4 { w32(r, j - i) as u32 } else { pre[j] },
    ensures
        forall|q: int| 0 <= q < 4 ==> #[trigger] fin[i + q] == add_pixels(px0[i + q], up_pred(mode, pre, i + q, w)),
{
    assert forall|q: int| 0 <= q < 4 implies #[trigger] fin[i + q] == add_pixels(px0[i + q], up_pred(mode, pre, i + q, w)) by {
        let cu = up_pred(mode, pre, i + q, w);
        assert((4 * q + 0) / 4 == q && (4 * q + 1) / 4 == q && (4 * q + 2) / 4 == q && (4 * q + 3) / 4 == q);
        if mode != 0 {
            assert(cu == pre[u + q]);
        }
        lemma_add_lane(src, up, pre[i + q], cu, q);
    }
}

/// Four pixels of such a mode, written at once, are four steps.
#[verifier::spinoff_prover]
proof fn lemma_up_block(bits: nat, w: nat, img: Seq<u32>, px0: Seq<u32>, pre: Seq<u32>, fin: Seq<u32>, i: int, x: int,
                        y: int, mode: int)
    requires
        mode == 0 || mode == 2 || mode == 3 || mode == 4,
        1 <= y, 1 <= x, x + 4 <= w, i == y * w + x, i + 4 <= px0.len(), pre.len() == px0.len(), fin.len() == px0.len(),
        forall|k: int| 0 <= k < i ==> #[trigger] fin[k] == pre[k],
        forall|q: int| 0 <= q < 4 ==> #[trigger] fin[i + q] == add_pixels(px0[i + q], up_pred(mode, pre, i + q, w as int)),
        forall|q: int| 0 <= q < 4 ==> #[trigger] green(tile(img, bits, w, (x + q) as nat, y as nat)) % 16 == mode,
    ensures inv_predictor(bits, w, img, px0, fin.take(i)) == inv_predictor(bits, w, img, px0, fin.take(i + 4)),
{
    assert(i >= w + 1) by (nonlinear_arith) requires i == y * w + x, y >= 1, x >= 1;
    assert(fin[i + 0] == add_pixels(px0[i + 0], up_pred(mode, pre, i + 0, w as int)));
    assert(fin[i + 1] == add_pixels(px0[i + 1], up_pred(mode, pre, i + 1, w as int)));
    assert(fin[i + 2] == add_pixels(px0[i + 2], up_pred(mode, pre, i + 2, w as int)));
    assert(fin[i + 3] == add_pixels(px0[i + 3], up_pred(mode, pre, i + 3, w as int)));
    assert(green(tile(img, bits, w, (x + 0) as nat, y as nat)) % 16 == mode);
    assert(green(tile(img, bits, w, (x + 1) as nat, y as nat)) % 16 == mode);
    assert(green(tile(img, bits, w, (x + 2) as nat, y as nat)) % 16 == mode);
    assert(green(tile(img, bits, w, (x + 3) as nat, y as nat)) % 16 == mode);
    lemma_up_step(bits, w, img, px0, pre, fin, i, x, y, mode, 0);
    lemma_up_step(bits, w, img, px0, pre, fin, i, x, y, mode, 1);
    lemma_up_step(bits, w, img, px0, pre, fin, i, x, y, mode, 2);
    lemma_up_step(bits, w, img, px0, pre, fin, i, x, y, mode, 3);
}

/// Modes 0, 2, 3, 4 four pixels at a time from `x0` while four are left;
/// the column reached.
#[verifier::spinoff_prover]
pub fn pred_up4(mode: i64, px: &mut Vec<u32>, y: usize, row: usize, x0: usize, x1: usize, w: usize,
                Ghost(bits): Ghost<nat>, Ghost(img): Ghost<Seq<u32>>, Ghost(px0): Ghost<Seq<u32>>, Ghost(target): Ghost<Seq<u32>>)
    -> (x: usize)
    requires
        mode == 0 || mode == 2 || mode == 3 || mode == 4,
        1 <= y, row == y * w, 1 <= x0 <= x1 <= w, w <= 16384, old(px)@.len() == px0.len(), row + w <= px0.len(),
        px0.len() <= 0x1000_0000,
        forall|k: int| row + x0 <= k < px0.len() ==> #[trigger] old(px)@[k] == px0[k],
        inv_predictor(bits, w as nat, img, px0, old(px)@.take(row + x0)) == target,
        forall|x: int| x0 <= x < x1 ==> #[trigger] green(tile(img, bits, w as nat, x as nat, y as nat)) % 16 == mode,
    ensures
        x0 <= x <= x1, final(px)@.len() == px0.len(),
        forall|k: int| row + x <= k < px0.len() ==> #[trigger] final(px)@[k] == px0[k],
        inv_predictor(bits, w as nat, img, px0, final(px)@.take(row + x)) == target,
{
    let black = sx::set1_epi32(0xff000000u32);
    let mut x = x0;
    proof { assert(row >= w) by (nonlinear_arith) requires row == y * w, y >= 1; }
    while x1 - x >= 4
        invariant
            mode == 0 || mode == 2 || mode == 3 || mode == 4,
            1 <= y, row == y * w, 1 <= x0 <= x <= x1 <= w, w <= 16384, px@.len() == px0.len(), row + w <= px0.len(),
            px0.len() <= 0x1000_0000, row >= w,
            v8(black) == vsimd::spec::set1_epi32(0xff000000u32),
            forall|k: int| row + x <= k < px0.len() ==> #[trigger] px@[k] == px0[k],
            inv_predictor(bits, w as nat, img, px0, px@.take(row + x)) == target,
            forall|xx: int| x0 <= xx < x1 ==> #[trigger] green(tile(img, bits, w as nat, xx as nat, y as nat)) % 16 == mode,
        decreases x1 - x,
    {
        let i = row + x;
        let u = if mode == 2 { i - w } else if mode == 3 { i - w + 1 } else { i - w - 1 };
        let up = if mode == 0 { black } else { sx::loadu_u32(px.as_slice(), u) };
        let src = sx::loadu_u32(px.as_slice(), i);
        let r = sx::add_epi8(src, up);
        let ghost pre = px@;
        sx::storeu_u32(px, i, r);
        proof {
            lemma_up_vals(v8(src), v8(up), v8(r), pre, px@, px0, i as int, u as int, w as int, mode as int);
            assert forall|q: int| 0 <= q < 4 implies #[trigger] green(tile(img, bits, w as nat, (x + q) as nat, y as nat)) % 16 == mode by {
                assert(x0 <= x + q < x1);
            }
            lemma_up_block(bits, w as nat, img, px0, pre, px@, i as int, x as int, y as int, mode as int);
            assert(px@.take(i as int) =~= pre.take(i as int));
        }
        x = x + 4;
    }
    x
}

} // verus!
