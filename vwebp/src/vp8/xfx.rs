//! The inverse DCT added to the prediction, in SSE2 (after libwebp's
//! Transform_SSE2), proved to compute `add_block(p, x, y, idct(c))`.
//!
//! The first pass runs in 16-bit lanes, as RFC 6386's reference decoder
//! stores it in `short`s: wrapping arithmetic is exact mod 2^16, and the
//! products use libwebp's identity (x * 35468) >> 16 = mulhi(x, -30068) + x.
//! The second pass, which the reference decoder computes in `int`, runs in
//! 32-bit lanes, so it is exact where libwebp's 16-bit one can overflow.
use vstd::prelude::*;
use super::spec::*;
use super::plane::*;
use super::hdr::*;
use super::tok::*;
#[cfg(verus_keep_ghost)]
use super::lfx::rows_w;
#[cfg(verus_keep_ghost)]
use vsimd::spec::{w16, sw16, w32, sw32, clamp, lemma_rt16, lemma_w16_bounds, lemma_w32_bounds, lemma_add16_lane, lemma_sub16_lane,
    lemma_mulhi_lane, lemma_set1_16_lane, lemma_add32_lane, lemma_sub32_lane, lemma_srai32_lane, lemma_packs32_lane,
    lemma_unpack16_lane, lemma_unpack32_lane16, lemma_widen_lane, lemma_zext_lane};
#[cfg(verus_keep_ghost)]
use vsimd::x86::{v8, byte, lemma_byte};
use vsimd::x86::__m128i;
use vsimd::x86 as sx;
use vsimd::model::put16_x;

verus! {

// ------------------------------------------------------------ arithmetic

proof fn lemma_mod_add(x: int, y: int)
    ensures ((x % 65536) + (y % 65536)) % 65536 == (x + y) % 65536,
{
    vstd::arithmetic::div_mod::lemma_add_mod_noop(x, y, 65536);
}

proof fn lemma_mod_sub(x: int, y: int)
    ensures ((x % 65536) - (y % 65536)) % 65536 == (x - y) % 65536,
{
    vstd::arithmetic::div_mod::lemma_sub_mod_noop(x, y, 65536);
}

/// libwebp's form of `ms`: the product by 35468 - 65536, plus x.
proof fn lemma_ms(i: int)
    requires -32768 <= i < 32768,
    ensures (i * -30068) / 65536 + i == ms(i), -17734 <= ms(i) <= 17734, -10046 <= (i * 20091) / 65536 <= 10045,
{
    use vstd::arithmetic::div_mod::*;
    let a = i * -30068;
    lemma_fundamental_div_mod(a, 65536);
    let (q, r) = (a / 65536, a % 65536);
    assert(i * 35468 == 65536 * (q + i) + r) by (nonlinear_arith) requires a == i * -30068, a == 65536 * q + r;
    lemma_div_multiples_vanish_fancy(q + i, r, 65536);
    assert(-1162215424 <= i * 35468 <= 1162179956) by (nonlinear_arith) requires -32768 <= i < 32768;
    assert(-658341888 <= i * 20091 <= 658321797) by (nonlinear_arith) requires -32768 <= i < 32768;
}

/// A 16-bit lane that is x mod 2^16 reads, signed, as wrap16(x).
proof fn lemma_wrap(a: Seq<u8>, j: int, x: int)
    requires a.len() == 16, 0 <= j < 8, w16(a, j) == x % 65536,
    ensures sw16(a, j) == wrap16(x),
{}

// ----------------------------------------------------------------- input

/// Row r of a block's coefficients, in 16-bit lanes 0 .. 4: four 32-bit
/// values packed to 16 bits (exactly, as they are within 16 bits).
fn row_in(c: &[i32; 16], r: usize) -> (v: __m128i)
    requires c16(c@), r < 4,
    ensures forall|l: int| 0 <= l < 4 ==> #[trigger] sw16(v8(v), l) == c@[4 * r + l] as int,
{
    let a = sx::load_i32x4(c, r);
    let z = sx::setzero();
    let v = sx::packs_epi32(a, z);
    proof {
        assert forall|l: int| 0 <= l < 4 implies #[trigger] sw16(v8(v), l) == c@[4 * r + l] as int by {
            assert(sw32(v8(a), l) == c@[4 * r + l] as int);
            lemma_packs32_lane(v8(a), v8(z), l);
        }
    }
    v
}

// ------------------------------------------------------------ first pass

/// ms and mc of a 16-bit lane, mod 2^16.
proof fn lemma_msmc_lane(r: Seq<u8>, k1: Seq<u8>, k2: Seq<u8>, sm: Seq<u8>, cm: Seq<u8>, c: int)
    requires 0 <= c < 8, r.len() == 16, k1 == vsimd::spec::set1_epi16(20091), k2 == vsimd::spec::set1_epi16(35468),
        sm == vsimd::spec::add_epi16(vsimd::spec::mulhi_epi16(r, k2), r),
        cm == vsimd::spec::add_epi16(vsimd::spec::mulhi_epi16(r, k1), r),
    ensures w16(sm, c) == ms(sw16(r, c)) % 65536, w16(cm, c) == mc(sw16(r, c)) % 65536,
{
    let i = sw16(r, c);
    lemma_w16_bounds(r, c);
    lemma_set1_16_lane(20091, c);
    lemma_set1_16_lane(35468, c);
    assert(sw16(k1, c) == 20091 && sw16(k2, c) == -30068);
    lemma_ms(i);
    let m = vsimd::spec::mulhi_epi16(r, k2);
    let hh = vsimd::spec::mulhi_epi16(r, k1);
    lemma_mulhi_lane(r, k2, c);
    lemma_mulhi_lane(r, k1, c);
    lemma_add16_lane(m, r, c);
    lemma_add16_lane(hh, r, c);
    lemma_mod_add(i * -30068 / 65536, i);
    lemma_mod_add(i * 20091 / 65536, i);
}

/// A sum and a difference of lanes known mod 2^16.
proof fn lemma_bf_lane(p: Seq<u8>, q: Seq<u8>, c: int, x: int, y: int)
    requires 0 <= c < 8, p.len() == 16, q.len() == 16, w16(p, c) == x % 65536, w16(q, c) == y % 65536,
    ensures w16(vsimd::spec::add_epi16(p, q), c) == (x + y) % 65536, w16(vsimd::spec::sub_epi16(p, q), c) == (x - y) % 65536,
{
    hide(w16);
    lemma_add16_lane(p, q, c);
    lemma_sub16_lane(p, q, c);
    lemma_mod_add(x, y);
    lemma_mod_sub(x, y);
}

/// One lane of the first pass: rows R0 .. R3 of column c to `idct_col`.
proof fn lemma_pass1_lane(r0: Seq<u8>, r1: Seq<u8>, r2: Seq<u8>, r3: Seq<u8>, k1: Seq<u8>, k2: Seq<u8>,
    s1: Seq<u8>, s3: Seq<u8>, c1: Seq<u8>, c3: Seq<u8>, a: Seq<u8>, b: Seq<u8>, cc: Seq<u8>, d: Seq<u8>,
    t0: Seq<u8>, t1: Seq<u8>, t2: Seq<u8>, t3: Seq<u8>, iv: Seq<int>, c: int)
    requires 0 <= c < 4, iv.len() == 16, r0.len() == 16, r1.len() == 16, r2.len() == 16, r3.len() == 16,
        s1.len() == 16, s3.len() == 16, c1.len() == 16, c3.len() == 16, a.len() == 16, b.len() == 16, cc.len() == 16, d.len() == 16,
        t0.len() == 16, t1.len() == 16, t2.len() == 16, t3.len() == 16,
        sw16(r0, c) == iv[c], sw16(r1, c) == iv[4 + c], sw16(r2, c) == iv[8 + c], sw16(r3, c) == iv[12 + c],
        k1 == vsimd::spec::set1_epi16(20091), k2 == vsimd::spec::set1_epi16(35468),
        s1 == vsimd::spec::add_epi16(vsimd::spec::mulhi_epi16(r1, k2), r1),
        s3 == vsimd::spec::add_epi16(vsimd::spec::mulhi_epi16(r3, k2), r3),
        c1 == vsimd::spec::add_epi16(vsimd::spec::mulhi_epi16(r1, k1), r1),
        c3 == vsimd::spec::add_epi16(vsimd::spec::mulhi_epi16(r3, k1), r3),
        a == vsimd::spec::add_epi16(r0, r2), b == vsimd::spec::sub_epi16(r0, r2),
        cc == vsimd::spec::sub_epi16(s1, c3), d == vsimd::spec::add_epi16(c1, s3),
        t0 == vsimd::spec::add_epi16(a, d), t1 == vsimd::spec::add_epi16(b, cc),
        t2 == vsimd::spec::sub_epi16(b, cc), t3 == vsimd::spec::sub_epi16(a, d),
    ensures sw16(t0, c) == idct_col(iv, c)[0], sw16(t1, c) == idct_col(iv, c)[1],
        sw16(t2, c) == idct_col(iv, c)[2], sw16(t3, c) == idct_col(iv, c)[3],
{
    hide(w16); hide(sw16); hide(wrap16); hide(ms); hide(mc);
    hide(vsimd::spec::add_epi16); hide(vsimd::spec::sub_epi16); hide(vsimd::spec::mulhi_epi16); hide(vsimd::spec::set1_epi16);
    let (i0, i1, i2, i3) = (iv[c], iv[4 + c], iv[8 + c], iv[12 + c]);
    lemma_w16_bounds(r0, c);
    lemma_w16_bounds(r2, c);
    lemma_msmc_lane(r1, k1, k2, s1, c1, c);
    lemma_msmc_lane(r3, k1, k2, s3, c3, c);
    let (av, bv, cv, dv) = (i0 + i2, i0 - i2, ms(i1) - mc(i3), mc(i1) + ms(i3));
    lemma_bf_lane(r0, r2, c, i0, i2);
    lemma_bf_lane(s1, c3, c, ms(i1), mc(i3));
    lemma_bf_lane(c1, s3, c, mc(i1), ms(i3));
    lemma_bf_lane(a, d, c, av, dv);
    lemma_bf_lane(b, cc, c, bv, cv);
    lemma_wrap(t0, c, av + dv);
    lemma_wrap(t1, c, bv + cv);
    lemma_wrap(t2, c, bv - cv);
    lemma_wrap(t3, c, av - dv);
}

/// The first pass on rows R0 .. R3 (16-bit lanes 0 .. 4 are the columns).
fn pass1(r0: __m128i, r1: __m128i, r2: __m128i, r3: __m128i, Ghost(iv): Ghost<Seq<int>>) -> (t: [__m128i; 4])
    requires iv.len() == 16,
        forall|c: int| 0 <= c < 4 ==> #[trigger] sw16(v8(r0), c) == iv[c],
        forall|c: int| 0 <= c < 4 ==> #[trigger] sw16(v8(r1), c) == iv[4 + c],
        forall|c: int| 0 <= c < 4 ==> #[trigger] sw16(v8(r2), c) == iv[8 + c],
        forall|c: int| 0 <= c < 4 ==> #[trigger] sw16(v8(r3), c) == iv[12 + c],
    ensures forall|rr: int, c: int| 0 <= rr < 4 && 0 <= c < 4 ==> #[trigger] sw16(v8(t@[rr]), c) == idct_col(iv, c)[rr],
{
    let k1 = sx::set1_epi16(20091);
    let k2 = sx::set1_epi16(35468);
    let s1 = sx::add_epi16(sx::mulhi_epi16(r1, k2), r1);
    let s3 = sx::add_epi16(sx::mulhi_epi16(r3, k2), r3);
    let c1 = sx::add_epi16(sx::mulhi_epi16(r1, k1), r1);
    let c3 = sx::add_epi16(sx::mulhi_epi16(r3, k1), r3);
    let a = sx::add_epi16(r0, r2);
    let b = sx::sub_epi16(r0, r2);
    let cc = sx::sub_epi16(s1, c3);
    let d = sx::add_epi16(c1, s3);
    let t = [sx::add_epi16(a, d), sx::add_epi16(b, cc), sx::sub_epi16(b, cc), sx::sub_epi16(a, d)];
    proof {
        assert forall|rr: int, c: int| 0 <= rr < 4 && 0 <= c < 4 implies #[trigger] sw16(v8(t@[rr]), c) == idct_col(iv, c)[rr] by {
            assert(sw16(v8(r0), c) == iv[c] && sw16(v8(r1), c) == iv[4 + c] && sw16(v8(r2), c) == iv[8 + c] && sw16(v8(r3), c) == iv[12 + c]);
            lemma_pass1_lane(v8(r0), v8(r1), v8(r2), v8(r3), v8(k1), v8(k2), v8(s1), v8(s3), v8(c1), v8(c3),
                v8(a), v8(b), v8(cc), v8(d), v8(t@[0]), v8(t@[1]), v8(t@[2]), v8(t@[3]), iv, c);
        }
    }
    t
}

// ------------------------------------------- transpose, widen, products

/// 16-bit lane l of the columns pair after the transpose: C01 holds
/// columns 0 and 1 (rows 0 .. 4 each), C23 columns 2 and 3.
proof fn lemma_cols_lane(t0: Seq<u8>, t1: Seq<u8>, t2: Seq<u8>, t3: Seq<u8>, x01: Seq<u8>, x23: Seq<u8>, c01: Seq<u8>, c23: Seq<u8>, l: int)
    requires 0 <= l < 8, t0.len() == 16, t1.len() == 16, t2.len() == 16, t3.len() == 16,
        x01 == vsimd::spec::unpacklo_epi16(t0, t1), x23 == vsimd::spec::unpacklo_epi16(t2, t3),
        c01 == vsimd::spec::unpacklo_epi32(x01, x23), c23 == vsimd::spec::unpackhi_epi32(x01, x23),
    ensures
        w16(c01, l) == w16(seq![t0, t1, t2, t3][l % 4], l / 4),
        w16(c23, l) == w16(seq![t0, t1, t2, t3][l % 4], 2 + l / 4),
{
    let q = (l / 4) * 2 + l % 2;
    lemma_unpack32_lane16(x01, x23, l);
    lemma_unpack16_lane(t0, t1, q);
    lemma_unpack16_lane(t2, t3, q);
    lemma_unpack16_lane(t0, t1, 4 + q);
    lemma_unpack16_lane(t2, t3, 4 + q);
    assert(l % 4 == 2 * ((l / 2) % 2) + l % 2);
}

/// A 16-bit lane widened to 32 bits: into the high half, shifted down.
proof fn lemma_widen(z: Seq<u8>, x: Seq<u8>, rr: int)
    requires 0 <= rr < 4, z == vsimd::spec::set1_epi8(0), x.len() == 16,
    ensures
        sw32(vsimd::spec::srai_epi32(vsimd::spec::unpacklo_epi16(z, x), 16), rr) == sw16(x, rr),
        sw32(vsimd::spec::srai_epi32(vsimd::spec::unpackhi_epi16(z, x), 16), rr) == sw16(x, 4 + rr),
{
    vstd::arithmetic::power2::lemma2_to64();
    lemma_widen_lane(z, x, rr);
    lemma_srai32_lane(vsimd::spec::unpacklo_epi16(z, x), 16, rr);
    lemma_srai32_lane(vsimd::spec::unpackhi_epi16(z, x), 16, rr);
    lemma_w16_bounds(x, rr);
    lemma_w16_bounds(x, 4 + rr);
}

/// ms, exactly, in a 16-bit lane.
proof fn lemma_ms_lane(x: Seq<u8>, k2: Seq<u8>, l: int)
    requires 0 <= l < 8, x.len() == 16, k2 == vsimd::spec::set1_epi16(35468),
    ensures sw16(vsimd::spec::add_epi16(vsimd::spec::mulhi_epi16(x, k2), x), l) == ms(sw16(x, l)),
{
    let i = sw16(x, l);
    lemma_w16_bounds(x, l);
    lemma_set1_16_lane(35468, l);
    lemma_mulhi_lane(x, k2, l);
    lemma_add16_lane(vsimd::spec::mulhi_epi16(x, k2), x, l);
    lemma_ms(i);
    lemma_mod_add(i * -30068 / 65536, i);
    lemma_wrap(vsimd::spec::add_epi16(vsimd::spec::mulhi_epi16(x, k2), x), l, ms(i));
}

/// One lane of `cols32`: column c, row rr.
proof fn lemma_cols32_lane(t0: Seq<u8>, t1: Seq<u8>, t2: Seq<u8>, t3: Seq<u8>, x01: Seq<u8>, x23: Seq<u8>, c01: Seq<u8>, c23: Seq<u8>,
    k1: Seq<u8>, k2: Seq<u8>, cv: Seq<u8>, mv: Seq<u8>, hv: Seq<u8>, z: Seq<u8>, c: int, rr: int)
    requires 0 <= c < 4, 0 <= rr < 4, t0.len() == 16, t1.len() == 16, t2.len() == 16, t3.len() == 16,
        x01 == vsimd::spec::unpacklo_epi16(t0, t1), x23 == vsimd::spec::unpacklo_epi16(t2, t3),
        c01 == vsimd::spec::unpacklo_epi32(x01, x23), c23 == vsimd::spec::unpackhi_epi32(x01, x23),
        k1 == vsimd::spec::set1_epi16(20091), k2 == vsimd::spec::set1_epi16(35468), z == vsimd::spec::set1_epi8(0),
        cv == if c < 2 { c01 } else { c23 },
        mv == vsimd::spec::add_epi16(vsimd::spec::mulhi_epi16(cv, k2), cv), hv == vsimd::spec::mulhi_epi16(cv, k1),
    ensures ({
        let tv = sw16(seq![t0, t1, t2, t3][rr], c);
        let pick = |x: Seq<u8>| if c % 2 == 0 { vsimd::spec::srai_epi32(vsimd::spec::unpacklo_epi16(z, x), 16) }
                                else { vsimd::spec::srai_epi32(vsimd::spec::unpackhi_epi16(z, x), 16) };
        &&& sw32(pick(cv), rr) == tv && sw32(pick(mv), rr) == ms(tv) && sw32(pick(hv), rr) == tv * 20091 / 65536
    }),
{
    let l = 4 * (c % 2) + rr;
    assert(l % 4 == rr && l / 4 == c % 2);
    lemma_cols_lane(t0, t1, t2, t3, x01, x23, c01, c23, l);
    assert(sw16(cv, l) == sw16(seq![t0, t1, t2, t3][rr], c));
    lemma_ms_lane(cv, k2, l);
    lemma_mulhi_lane(cv, k1, l);
    lemma_set1_16_lane(20091, l);
    assert(sw16(k1, l) == 20091);
    lemma_widen(z, cv, rr);
    lemma_widen(z, mv, rr);
    lemma_widen(z, hv, rr);
}

/// The transposed first pass in 32-bit lanes (lane rr of vector c is row
/// rr, column c), with ms of each value and its product by 20091 >> 16.
fn cols32(t: &[__m128i; 4]) -> (r: ([__m128i; 4], [__m128i; 4], [__m128i; 4]))
    ensures
        forall|c: int, rr: int| 0 <= c < 4 && 0 <= rr < 4 ==> #[trigger] sw32(v8(r.0@[c]), rr) == sw16(v8(t@[rr]), c),
        forall|c: int, rr: int| 0 <= c < 4 && 0 <= rr < 4 ==> #[trigger] sw32(v8(r.1@[c]), rr) == ms(sw16(v8(t@[rr]), c)),
        forall|c: int, rr: int| 0 <= c < 4 && 0 <= rr < 4 ==> #[trigger] sw32(v8(r.2@[c]), rr) == sw16(v8(t@[rr]), c) * 20091 / 65536,
{
    hide(vsimd::spec::unpacklo_epi16); hide(vsimd::spec::unpackhi_epi16); hide(vsimd::spec::unpacklo_epi32); hide(vsimd::spec::unpackhi_epi32);
    hide(vsimd::spec::mulhi_epi16); hide(vsimd::spec::add_epi16); hide(vsimd::spec::srai_epi32); hide(vsimd::spec::set1_epi16);
    hide(vsimd::spec::set1_epi8); hide(sw16); hide(sw32); hide(w16); hide(w32); hide(ms);
    let x01 = sx::unpacklo_epi16(t[0], t[1]);
    let x23 = sx::unpacklo_epi16(t[2], t[3]);
    let c01 = sx::unpacklo_epi32(x01, x23);
    let c23 = sx::unpackhi_epi32(x01, x23);
    let k1 = sx::set1_epi16(20091);
    let k2 = sx::set1_epi16(35468);
    let m01 = sx::add_epi16(sx::mulhi_epi16(c01, k2), c01);
    let m23 = sx::add_epi16(sx::mulhi_epi16(c23, k2), c23);
    let h01 = sx::mulhi_epi16(c01, k1);
    let h23 = sx::mulhi_epi16(c23, k1);
    let z = sx::setzero();
    let u = [sx::srai_epi32_16(sx::unpacklo_epi16(z, c01)), sx::srai_epi32_16(sx::unpackhi_epi16(z, c01)),
             sx::srai_epi32_16(sx::unpacklo_epi16(z, c23)), sx::srai_epi32_16(sx::unpackhi_epi16(z, c23))];
    let m = [sx::srai_epi32_16(sx::unpacklo_epi16(z, m01)), sx::srai_epi32_16(sx::unpackhi_epi16(z, m01)),
             sx::srai_epi32_16(sx::unpacklo_epi16(z, m23)), sx::srai_epi32_16(sx::unpackhi_epi16(z, m23))];
    let h = [sx::srai_epi32_16(sx::unpacklo_epi16(z, h01)), sx::srai_epi32_16(sx::unpackhi_epi16(z, h01)),
             sx::srai_epi32_16(sx::unpacklo_epi16(z, h23)), sx::srai_epi32_16(sx::unpackhi_epi16(z, h23))];
    proof {
        assert forall|rr: int| 0 <= rr < 4 implies #[trigger] sw32(v8(u@[0]), rr) == sw16(v8(t@[rr]), 0) && sw32(v8(m@[0]), rr) == ms(sw16(v8(t@[rr]), 0))
            && sw32(v8(h@[0]), rr) == sw16(v8(t@[rr]), 0) * 20091 / 65536 by {
            lemma_cols32_lane(v8(t@[0]), v8(t@[1]), v8(t@[2]), v8(t@[3]), v8(x01), v8(x23), v8(c01), v8(c23),
                v8(k1), v8(k2), v8(c01), v8(m01), v8(h01), v8(z), 0, rr);
            assert(seq![v8(t@[0]), v8(t@[1]), v8(t@[2]), v8(t@[3])][rr] == v8(t@[rr]));
        }
        assert forall|rr: int| 0 <= rr < 4 implies #[trigger] sw32(v8(u@[1]), rr) == sw16(v8(t@[rr]), 1) && sw32(v8(m@[1]), rr) == ms(sw16(v8(t@[rr]), 1))
            && sw32(v8(h@[1]), rr) == sw16(v8(t@[rr]), 1) * 20091 / 65536 by {
            lemma_cols32_lane(v8(t@[0]), v8(t@[1]), v8(t@[2]), v8(t@[3]), v8(x01), v8(x23), v8(c01), v8(c23),
                v8(k1), v8(k2), v8(c01), v8(m01), v8(h01), v8(z), 1, rr);
            assert(seq![v8(t@[0]), v8(t@[1]), v8(t@[2]), v8(t@[3])][rr] == v8(t@[rr]));
        }
        assert forall|rr: int| 0 <= rr < 4 implies #[trigger] sw32(v8(u@[2]), rr) == sw16(v8(t@[rr]), 2) && sw32(v8(m@[2]), rr) == ms(sw16(v8(t@[rr]), 2))
            && sw32(v8(h@[2]), rr) == sw16(v8(t@[rr]), 2) * 20091 / 65536 by {
            lemma_cols32_lane(v8(t@[0]), v8(t@[1]), v8(t@[2]), v8(t@[3]), v8(x01), v8(x23), v8(c01), v8(c23),
                v8(k1), v8(k2), v8(c23), v8(m23), v8(h23), v8(z), 2, rr);
            assert(seq![v8(t@[0]), v8(t@[1]), v8(t@[2]), v8(t@[3])][rr] == v8(t@[rr]));
        }
        assert forall|rr: int| 0 <= rr < 4 implies #[trigger] sw32(v8(u@[3]), rr) == sw16(v8(t@[rr]), 3) && sw32(v8(m@[3]), rr) == ms(sw16(v8(t@[rr]), 3))
            && sw32(v8(h@[3]), rr) == sw16(v8(t@[rr]), 3) * 20091 / 65536 by {
            lemma_cols32_lane(v8(t@[0]), v8(t@[1]), v8(t@[2]), v8(t@[3]), v8(x01), v8(x23), v8(c01), v8(c23),
                v8(k1), v8(k2), v8(c23), v8(m23), v8(h23), v8(z), 3, rr);
            assert(seq![v8(t@[0]), v8(t@[1]), v8(t@[2]), v8(t@[3])][rr] == v8(t@[rr]));
        }
        assert forall|c: int, rr: int| 0 <= c < 4 && 0 <= rr < 4 implies
            sw32(v8(u@[c]), rr) == sw16(v8(t@[rr]), c) && sw32(v8(m@[c]), rr) == ms(sw16(v8(t@[rr]), c))
            && sw32(v8(h@[c]), rr) == sw16(v8(t@[rr]), c) * 20091 / 65536 by {
            if c == 0 { assert(sw32(v8(u@[0]), rr) == sw16(v8(t@[rr]), 0)); }
            else if c == 1 { assert(sw32(v8(u@[1]), rr) == sw16(v8(t@[rr]), 1)); }
            else if c == 2 { assert(sw32(v8(u@[2]), rr) == sw16(v8(t@[rr]), 2)); }
            else { assert(sw32(v8(u@[3]), rr) == sw16(v8(t@[rr]), 3)); }
        }
    }
    (u, m, h)
}

// ----------------------------------------------------------- second pass

/// Exact 32-bit sums and differences of small values.
proof fn lemma_add32(a: Seq<u8>, b: Seq<u8>, j: int)
    requires 0 <= j < 4, a.len() == 16, b.len() == 16, -2147483648 <= sw32(a, j) + sw32(b, j) < 2147483648,
    ensures sw32(vsimd::spec::add_epi32(a, b), j) == sw32(a, j) + sw32(b, j),
{
    hide(w32);
    lemma_add32_lane(a, b, j);
    lemma_w32_bounds(a, j);
    lemma_w32_bounds(b, j);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(sw32(a, j), sw32(b, j), 4294967296);
    let r = vsimd::spec::add_epi32(a, b);
    lemma_w32_bounds(r, j);
}

proof fn lemma_sub32(a: Seq<u8>, b: Seq<u8>, j: int)
    requires 0 <= j < 4, a.len() == 16, b.len() == 16, -2147483648 <= sw32(a, j) - sw32(b, j) < 2147483648,
    ensures sw32(vsimd::spec::sub_epi32(a, b), j) == sw32(a, j) - sw32(b, j),
{
    hide(w32);
    lemma_sub32_lane(a, b, j);
    lemma_w32_bounds(a, j);
    lemma_w32_bounds(b, j);
    vstd::arithmetic::div_mod::lemma_sub_mod_noop(sw32(a, j), sw32(b, j), 4294967296);
    let r = vsimd::spec::sub_epi32(a, b);
    lemma_w32_bounds(r, j);
}

/// The second pass of one row, from its four values, their products.
pub open spec fn p2(u0: int, u1: int, u2: int, u3: int, m1: int, m3: int, h1: int, h3: int, c: int) -> int {
    let a1 = u0 + u2;
    let b1 = u0 - u2;
    let c1 = m1 - (u3 + h3);
    let d1 = (u1 + h1) + m3;
    let v = if c == 0 { a1 + d1 } else if c == 1 { b1 + c1 } else if c == 2 { b1 - c1 } else { a1 - d1 };
    (v + 4) / 8
}

/// One lane of the second pass.
proof fn lemma_pass2_lane(u0: Seq<u8>, u1: Seq<u8>, u2: Seq<u8>, u3: Seq<u8>, m1: Seq<u8>, m3: Seq<u8>, h1: Seq<u8>, h3: Seq<u8>,
    four: Seq<u8>, a1: Seq<u8>, b1: Seq<u8>, mc1: Seq<u8>, mc3: Seq<u8>, c1: Seq<u8>, d1: Seq<u8>,
    s0: Seq<u8>, s1: Seq<u8>, s2: Seq<u8>, s3: Seq<u8>, v0: Seq<u8>, v1: Seq<u8>, v2: Seq<u8>, v3: Seq<u8>,
    o0: Seq<u8>, o1: Seq<u8>, o2: Seq<u8>, o3: Seq<u8>, rr: int)
    requires 0 <= rr < 4,
        u0.len() == 16, u1.len() == 16, u2.len() == 16, u3.len() == 16, m1.len() == 16, m3.len() == 16, h1.len() == 16, h3.len() == 16,
        four.len() == 16,
        -32768 <= sw32(u0, rr) < 32768, -32768 <= sw32(u1, rr) < 32768, -32768 <= sw32(u2, rr) < 32768, -32768 <= sw32(u3, rr) < 32768,
        -17734 <= sw32(m1, rr) <= 17734, -17734 <= sw32(m3, rr) <= 17734,
        -10046 <= sw32(h1, rr) <= 10045, -10046 <= sw32(h3, rr) <= 10045, sw32(four, rr) == 4,
        a1 == vsimd::spec::add_epi32(u0, u2), b1 == vsimd::spec::sub_epi32(u0, u2),
        mc1 == vsimd::spec::add_epi32(u1, h1), mc3 == vsimd::spec::add_epi32(u3, h3),
        c1 == vsimd::spec::sub_epi32(m1, mc3), d1 == vsimd::spec::add_epi32(mc1, m3),
        s0 == vsimd::spec::add_epi32(a1, d1), s1 == vsimd::spec::add_epi32(b1, c1),
        s2 == vsimd::spec::sub_epi32(b1, c1), s3 == vsimd::spec::sub_epi32(a1, d1),
        v0 == vsimd::spec::add_epi32(s0, four), v1 == vsimd::spec::add_epi32(s1, four),
        v2 == vsimd::spec::add_epi32(s2, four), v3 == vsimd::spec::add_epi32(s3, four),
        o0 == vsimd::spec::srai_epi32(v0, 3), o1 == vsimd::spec::srai_epi32(v1, 3),
        o2 == vsimd::spec::srai_epi32(v2, 3), o3 == vsimd::spec::srai_epi32(v3, 3),
    ensures ({
        let (x0, x1, x2, x3) = (sw32(u0, rr), sw32(u1, rr), sw32(u2, rr), sw32(u3, rr));
        let (y1, y3, z1, z3) = (sw32(m1, rr), sw32(m3, rr), sw32(h1, rr), sw32(h3, rr));
        &&& sw32(o0, rr) == p2(x0, x1, x2, x3, y1, y3, z1, z3, 0) && sw32(o1, rr) == p2(x0, x1, x2, x3, y1, y3, z1, z3, 1)
        &&& sw32(o2, rr) == p2(x0, x1, x2, x3, y1, y3, z1, z3, 2) && sw32(o3, rr) == p2(x0, x1, x2, x3, y1, y3, z1, z3, 3)
        &&& -16384 <= sw32(o0, rr) <= 16384 && -16384 <= sw32(o1, rr) <= 16384
        &&& -16384 <= sw32(o2, rr) <= 16384 && -16384 <= sw32(o3, rr) <= 16384
    }),
{
    hide(w32); hide(sw32);
    vstd::arithmetic::power2::lemma2_to64();
    lemma_add32(u0, u2, rr);
    lemma_sub32(u0, u2, rr);
    lemma_add32(u1, h1, rr);
    lemma_add32(u3, h3, rr);
    lemma_sub32(m1, mc3, rr);
    lemma_add32(mc1, m3, rr);
    lemma_add32(a1, d1, rr);
    lemma_add32(b1, c1, rr);
    lemma_sub32(b1, c1, rr);
    lemma_sub32(a1, d1, rr);
    lemma_add32(s0, four, rr);
    lemma_add32(s1, four, rr);
    lemma_add32(s2, four, rr);
    lemma_add32(s3, four, rr);
    lemma_srai32_lane(v0, 3, rr);
    lemma_srai32_lane(v1, 3, rr);
    lemma_srai32_lane(v2, 3, rr);
    lemma_srai32_lane(v3, 3, rr);
}

/// The second pass, in 32-bit lanes: lane rr of output c is row rr's
/// column c.
fn pass2(u: &[__m128i; 4], m: &[__m128i; 4], h: &[__m128i; 4]) -> (o: [__m128i; 4])
    requires
        forall|c: int, rr: int| 0 <= c < 4 && 0 <= rr < 4 ==> -32768 <= #[trigger] sw32(v8(u@[c]), rr) < 32768,
        forall|c: int, rr: int| 0 <= c < 4 && 0 <= rr < 4 ==> -17734 <= #[trigger] sw32(v8(m@[c]), rr) <= 17734,
        forall|c: int, rr: int| 0 <= c < 4 && 0 <= rr < 4 ==> -10046 <= #[trigger] sw32(v8(h@[c]), rr) <= 10045,
    ensures forall|c: int, rr: int| 0 <= c < 4 && 0 <= rr < 4 ==> #[trigger] sw32(v8(o@[c]), rr) == p2(
        sw32(v8(u@[0]), rr), sw32(v8(u@[1]), rr), sw32(v8(u@[2]), rr), sw32(v8(u@[3]), rr),
        sw32(v8(m@[1]), rr), sw32(v8(m@[3]), rr), sw32(v8(h@[1]), rr), sw32(v8(h@[3]), rr), c)
        && -16384 <= sw32(v8(o@[c]), rr) <= 16384,
{
    let four = sx::from_bytes([4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0]);
    let a1 = sx::add_epi32(u[0], u[2]);
    let b1 = sx::sub_epi32(u[0], u[2]);
    let mc1 = sx::add_epi32(u[1], h[1]);
    let mc3 = sx::add_epi32(u[3], h[3]);
    let c1 = sx::sub_epi32(m[1], mc3);
    let d1 = sx::add_epi32(mc1, m[3]);
    let (s0, s1, s2, s3) = (sx::add_epi32(a1, d1), sx::add_epi32(b1, c1), sx::sub_epi32(b1, c1), sx::sub_epi32(a1, d1));
    let v0 = sx::add_epi32(s0, four);
    let v1 = sx::add_epi32(s1, four);
    let v2 = sx::add_epi32(s2, four);
    let v3 = sx::add_epi32(s3, four);
    let o = [sx::srai_epi32_3(v0), sx::srai_epi32_3(v1), sx::srai_epi32_3(v2), sx::srai_epi32_3(v3)];
    proof {
        assert forall|c: int, rr: int| 0 <= c < 4 && 0 <= rr < 4 implies #[trigger] sw32(v8(o@[c]), rr) == p2(
            sw32(v8(u@[0]), rr), sw32(v8(u@[1]), rr), sw32(v8(u@[2]), rr), sw32(v8(u@[3]), rr),
            sw32(v8(m@[1]), rr), sw32(v8(m@[3]), rr), sw32(v8(h@[1]), rr), sw32(v8(h@[3]), rr), c)
            && -16384 <= sw32(v8(o@[c]), rr) <= 16384 by {
            assert(-32768 <= sw32(v8(u@[0]), rr) < 32768 && -32768 <= sw32(v8(u@[1]), rr) < 32768);
            assert(-32768 <= sw32(v8(u@[2]), rr) < 32768 && -32768 <= sw32(v8(u@[3]), rr) < 32768);
            assert(-17734 <= sw32(v8(m@[1]), rr) <= 17734 && -17734 <= sw32(v8(m@[3]), rr) <= 17734);
            assert(-10046 <= sw32(v8(h@[1]), rr) <= 10045 && -10046 <= sw32(v8(h@[3]), rr) <= 10045);
            assert(sw32(v8(four), rr) == 4);
            lemma_pass2_lane(v8(u@[0]), v8(u@[1]), v8(u@[2]), v8(u@[3]), v8(m@[1]), v8(m@[3]), v8(h@[1]), v8(h@[3]),
                v8(four), v8(a1), v8(b1), v8(mc1), v8(mc3), v8(c1), v8(d1), v8(s0), v8(s1), v8(s2), v8(s3),
                v8(v0), v8(v1), v8(v2), v8(v3), v8(o@[0]), v8(o@[1]), v8(o@[2]), v8(o@[3]), rr);
        }
    }
    o
}

// ----------------------------------------------------------------- output

/// A packed lane: 16-bit lane m of packs(o_a, o_b) is lane m of o_a
/// (m < 4) or m - 4 of o_b, the values being in range.
proof fn lemma_pack_in(oa: Seq<u8>, ob: Seq<u8>, m: int)
    requires 0 <= m < 8, oa.len() == 16, ob.len() == 16,
        m < 4 ==> -32768 <= sw32(oa, m) < 32768, m >= 4 ==> -32768 <= sw32(ob, m - 4) < 32768,
    ensures sw16(vsimd::spec::packs_epi32(oa, ob), m) == if m < 4 { sw32(oa, m) } else { sw32(ob, m - 4) },
{
    hide(w32);
    lemma_packs32_lane(oa, ob, m);
}

proof fn lemma_rows_lane(o0: Seq<u8>, o1: Seq<u8>, o2: Seq<u8>, o3: Seq<u8>, p01: Seq<u8>, p23: Seq<u8>,
    lo: Seq<u8>, hi: Seq<u8>, q01: Seq<u8>, q23: Seq<u8>, r: int, c: int)
    requires 0 <= r < 2, 0 <= c < 4, o0.len() == 16, o1.len() == 16, o2.len() == 16, o3.len() == 16,
        p01.len() == 16, p23.len() == 16, lo.len() == 16, hi.len() == 16,
        forall|rr: int| 0 <= rr < 4 ==> -32768 <= #[trigger] sw32(o0, rr) < 32768,
        forall|rr: int| 0 <= rr < 4 ==> -32768 <= #[trigger] sw32(o1, rr) < 32768,
        forall|rr: int| 0 <= rr < 4 ==> -32768 <= #[trigger] sw32(o2, rr) < 32768,
        forall|rr: int| 0 <= rr < 4 ==> -32768 <= #[trigger] sw32(o3, rr) < 32768,
        p01 == vsimd::spec::packs_epi32(o0, o1), p23 == vsimd::spec::packs_epi32(o2, o3),
        lo == vsimd::spec::unpacklo_epi16(p01, p23), hi == vsimd::spec::unpackhi_epi16(p01, p23),
        q01 == vsimd::spec::unpacklo_epi16(lo, hi), q23 == vsimd::spec::unpackhi_epi16(lo, hi),
    ensures
        sw16(q01, 4 * r + c) == sw32(seq![o0, o1, o2, o3][c], r),
        sw16(q23, 4 * r + c) == sw32(seq![o0, o1, o2, o3][c], 2 + r),
{
    hide(w32); hide(sw32);
    hide(vsimd::spec::unpacklo_epi16); hide(vsimd::spec::unpackhi_epi16); hide(vsimd::spec::packs_epi32);
    let l = 4 * r + c;
    lemma_unpack16_lane(lo, hi, l);
    // q01 lane l is lane l / 2 = 2r + c / 2 of lo (c even) or hi (c odd);
    // that is lane r or 4 + r of p01 (c / 2 = 0) or p23 (c / 2 = 1).
    lemma_unpack16_lane(p01, p23, 2 * r + c / 2);
    lemma_unpack16_lane(p01, p23, 4 + 2 * r + c / 2);
    assert(l / 2 == 2 * r + c / 2 && l % 2 == c % 2 && (2 * r + c / 2) / 2 == r && (2 * r + c / 2) % 2 == c / 2);
    assert((4 + 2 * r + c / 2) / 2 == 2 + r && (4 + 2 * r + c / 2) % 2 == c / 2);
    assert(-32768 <= sw32(o0, r) < 32768 && -32768 <= sw32(o1, r) < 32768 && -32768 <= sw32(o2, r) < 32768 && -32768 <= sw32(o3, r) < 32768);
    assert(-32768 <= sw32(o0, 2 + r) < 32768 && -32768 <= sw32(o1, 2 + r) < 32768 && -32768 <= sw32(o2, 2 + r) < 32768 && -32768 <= sw32(o3, 2 + r) < 32768);
    lemma_pack_in(o0, o1, r); lemma_pack_in(o0, o1, 4 + r); lemma_pack_in(o0, o1, 2 + r); lemma_pack_in(o0, o1, 6 + r);
    lemma_pack_in(o2, o3, r); lemma_pack_in(o2, o3, 4 + r); lemma_pack_in(o2, o3, 2 + r); lemma_pack_in(o2, o3, 6 + r);
    reveal(sw16);
}

/// The four output columns (32-bit lanes are rows) as rows in 16-bit
/// lanes: rows 0 and 1 in q01, rows 2 and 3 in q23, lane 4 * row + column.
fn rows_out(o: &[__m128i; 4]) -> (q: (__m128i, __m128i))
    requires forall|c: int, rr: int| 0 <= c < 4 && 0 <= rr < 4 ==> -16384 <= #[trigger] sw32(v8(o@[c]), rr) <= 16384,
    ensures
        forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(v8(q.0), l) == sw32(v8(o@[l % 4]), l / 4),
        forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(v8(q.1), l) == sw32(v8(o@[l % 4]), 2 + l / 4),
{
    let p01 = sx::packs_epi32(o[0], o[1]);
    let p23 = sx::packs_epi32(o[2], o[3]);
    let lo = sx::unpacklo_epi16(p01, p23);
    let hi = sx::unpackhi_epi16(p01, p23);
    let q01 = sx::unpacklo_epi16(lo, hi);
    let q23 = sx::unpackhi_epi16(lo, hi);
    proof {
        assert forall|rr: int| 0 <= rr < 4 implies -32768 <= #[trigger] sw32(v8(o@[0]), rr) < 32768 by { assert(-16384 <= sw32(v8(o@[0]), rr)); }
        assert forall|rr: int| 0 <= rr < 4 implies -32768 <= #[trigger] sw32(v8(o@[1]), rr) < 32768 by { assert(-16384 <= sw32(v8(o@[1]), rr)); }
        assert forall|rr: int| 0 <= rr < 4 implies -32768 <= #[trigger] sw32(v8(o@[2]), rr) < 32768 by { assert(-16384 <= sw32(v8(o@[2]), rr)); }
        assert forall|rr: int| 0 <= rr < 4 implies -32768 <= #[trigger] sw32(v8(o@[3]), rr) < 32768 by { assert(-16384 <= sw32(v8(o@[3]), rr)); }
        assert forall|l: int| 0 <= l < 8 implies sw16(v8(q01), l) == sw32(v8(o@[l % 4]), l / 4)
            && sw16(v8(q23), l) == sw32(v8(o@[l % 4]), 2 + l / 4) by {
            lemma_rows_lane(v8(o@[0]), v8(o@[1]), v8(o@[2]), v8(o@[3]), v8(p01), v8(p23), v8(lo), v8(hi), v8(q01), v8(q23), l / 4, l % 4);
            assert(4 * (l / 4) + l % 4 == l);
            assert(seq![v8(o@[0]), v8(o@[1]), v8(o@[2]), v8(o@[3])][l % 4] == v8(o@[l % 4]));
        }
    }
    (q01, q23)
}

// ------------------------------------------------- prediction and store

/// Row r's 4 pixels at x .. x + 4, in bytes 0 .. 4.
fn load4_row(v: &Vec<u8>, w: usize, x: usize, r: usize, Ghost(pl): Ghost<Plane>) -> (a: __m128i)
    requires holds(v@, w as nat, pl), r < pl.len(), x + 4 <= w,
    ensures forall|k: int| 0 <= k < 16 ==> #[trigger] v8(a)[k] == if k < 4 { pl[r as int][x + k] } else { 0u8 },
{
    let n = v.len();
    proof { lemma_idx(w as nat, pl.len(), (x + 3) as int, r as int); }
    let a = sx::load4(v.as_slice(), r * w + x);
    proof {
        assert forall|k: int| 0 <= k < 16 implies #[trigger] v8(a)[k] == if k < 4 { pl[r as int][x + k] } else { 0u8 } by {
            if k < 4 { lemma_idx(w as nat, pl.len(), x + k, r as int); }
        }
    }
    a
}

/// The plane with row r's pixels x .. x + 4 set to `t`.
pub open spec fn set4(p: Plane, x: int, r: int, t: Seq<u8>) -> Plane {
    p.update(r, Seq::new(p[r].len(), |cc: int| if x <= cc < x + 4 { t[cc - x] } else { p[r][cc] }))
}

proof fn lemma_outside4(w: nat, r: int, x: int, yy: int, xx: int)
    requires 0 <= xx < w, 0 <= yy, 0 <= r, 0 <= x, x + 4 <= w, yy != r,
    ensures !(r * w + x <= yy * w + xx < r * w + x + 4),
{
    if yy < r {
        assert(yy * w + xx < r * w) by (nonlinear_arith) requires yy < r, 0 <= xx < w;
    } else {
        assert(yy * w >= r * w + w) by (nonlinear_arith) requires yy > r, w >= 0;
    }
}

/// Write bytes 4 * lane .. 4 * lane + 4 of `a` at pixels x .. x + 4 of row r.
fn put4(v: &mut Vec<u8>, w: usize, x: usize, r: usize, a: __m128i, lane: usize, Ghost(pl): Ghost<Plane>, Ghost(t): Ghost<Seq<u8>>)
    requires holds(old(v)@, w as nat, pl), r < pl.len(), x + 4 <= w, lane < 4, t.len() == 4,
        forall|m: int| 0 <= m < 4 ==> #[trigger] t[m] == v8(a)[4 * lane + m],
    ensures holds(final(v)@, w as nat, set4(pl, x as int, r as int, t)),
{
    let n = v.len();
    proof { lemma_idx(w as nat, pl.len(), (x + 3) as int, r as int); }
    let off = r * w + x;
    sx::store4(v, off, a, lane);
    proof {
        let p2 = set4(pl, x as int, r as int, t);
        assert forall|yy: int, xx: int| 0 <= yy < p2.len() && 0 <= xx < w implies v@[yy * w + xx] == #[trigger] p2[yy][xx] by {
            lemma_idx(w as nat, pl.len(), xx, yy);
            if yy == r && x <= xx < x + 4 {
                assert(t[xx - x] == v8(a)[4 * lane + (yy * w + xx - off)]);
            } else if yy != r {
                lemma_outside4(w as nat, r as int, x as int, yy, xx);
            }
        }
    }
}

/// One output byte: prediction plus residual, saturated.
proof fn lemma_out_lane(q: Seq<u8>, pr: Seq<u8>, z: Seq<u8>, wv: Seq<u8>, sv: Seq<u8>, l: int, res: int)
    requires 0 <= l < 8, q.len() == 16, pr.len() == 16, z == vsimd::spec::set1_epi8(0),
        wv == vsimd::spec::unpacklo_epi8(pr, z), sv == vsimd::spec::add_epi16(q, wv),
        sw16(q, l) == res, -16384 <= res <= 16384,
    ensures sw16(sv, l) == res + pr[l] as int,
{
    lemma_zext_lane(pr, z, l);
    lemma_add16_lane(q, wv, l);
    lemma_w16_bounds(q, l);
    lemma_mod_add(res, pr[l] as int);
    lemma_wrap(sv, l, res + pr[l] as int);
}

/// The prediction's 4 x 4 pixels: rows 0 and 1 in bytes 0 .. 8 of the
/// first vector, rows 2 and 3 in the second.
fn pred_bytes(v: &Vec<u8>, w: usize, x: usize, y: usize, Ghost(pl): Ghost<Plane>) -> (p: (__m128i, __m128i))
    requires holds(v@, w as nat, pl), x + 4 <= w, y + 4 <= pl.len(),
    ensures
        forall|l: int| 0 <= l < 8 ==> #[trigger] v8(p.0)[l] == pl[y + l / 4][x + l % 4],
        forall|l: int| 0 <= l < 8 ==> #[trigger] v8(p.1)[l] == pl[y + 2 + l / 4][x + l % 4],
{
    let pr0 = load4_row(v, w, x, y, Ghost(pl));
    let pr1 = load4_row(v, w, x, y + 1, Ghost(pl));
    let pr2 = load4_row(v, w, x, y + 2, Ghost(pl));
    let pr3 = load4_row(v, w, x, y + 3, Ghost(pl));
    let p01 = sx::unpacklo_epi32(pr0, pr1);
    let p23 = sx::unpacklo_epi32(pr2, pr3);
    proof {
        assert forall|l: int| 0 <= l < 8 implies #[trigger] v8(p01)[l] == pl[y + l / 4][x + l % 4] && v8(p23)[l] == pl[y + 2 + l / 4][x + l % 4] by {
            assert((l / 4) % 2 == l / 4 && (l / 4 / 2) * 4 + l % 4 == l % 4);
            assert(v8(pr0)[l % 4] == pl[y as int][x + l % 4] && v8(pr1)[l % 4] == pl[y + 1][x + l % 4]);
            assert(v8(pr2)[l % 4] == pl[y + 2][x + l % 4] && v8(pr3)[l % 4] == pl[y + 3][x + l % 4]);
        }
    }
    (p01, p23)
}

/// The residual of the coefficients, rows 0 and 1 in the 16-bit lanes of
/// the first vector, rows 2 and 3 in the second (lane 4 * row + column).
fn residual(c: &[i32; 16]) -> (q: (__m128i, __m128i))
    requires c16(c@),
    ensures
        forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(v8(q.0), l) == idct(ints(c@))[l] && -16384 <= idct(ints(c@))[l] <= 16384,
        forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(v8(q.1), l) == idct(ints(c@))[8 + l] && -16384 <= idct(ints(c@))[8 + l] <= 16384,
{
    hide(sw16); hide(sw32); hide(w16); hide(w32); hide(ms); hide(idct_col); hide(p2);
    let ghost iv = ints(c@);
    let ghost res = idct(iv);
    let r0 = row_in(c, 0);
    let r1 = row_in(c, 1);
    let r2 = row_in(c, 2);
    let r3 = row_in(c, 3);
    proof {
        assert forall|k: int| 0 <= k < 4 implies #[trigger] sw16(v8(r0), k) == iv[k] by { assert(c@[4 * 0 + k] as int == iv[k]); }
        assert forall|k: int| 0 <= k < 4 implies #[trigger] sw16(v8(r1), k) == iv[4 + k] by { assert(c@[4 * 1 + k] as int == iv[4 + k]); }
        assert forall|k: int| 0 <= k < 4 implies #[trigger] sw16(v8(r2), k) == iv[8 + k] by { assert(c@[4 * 2 + k] as int == iv[8 + k]); }
        assert forall|k: int| 0 <= k < 4 implies #[trigger] sw16(v8(r3), k) == iv[12 + k] by { assert(c@[4 * 3 + k] as int == iv[12 + k]); }
    }
    let t = pass1(r0, r1, r2, r3, Ghost(iv));
    let (u, m, h) = cols32(&t);
    proof {
        assert forall|cc: int, rr: int| 0 <= cc < 4 && 0 <= rr < 4 implies
            -32768 <= #[trigger] sw32(v8(u@[cc]), rr) < 32768 && -17734 <= sw32(v8(m@[cc]), rr) <= 17734
            && -10046 <= sw32(v8(h@[cc]), rr) <= 10045 by {
            lemma_w16_bounds(v8(t@[rr]), cc);
            lemma_ms(sw16(v8(t@[rr]), cc));
        }
        assert forall|cc: int, rr: int| 0 <= cc < 4 && 0 <= rr < 4 implies -32768 <= #[trigger] sw32(v8(u@[cc]), rr) < 32768 by {
            assert(-32768 <= sw32(v8(u@[cc]), rr) < 32768 && -17734 <= sw32(v8(m@[cc]), rr) <= 17734);
        }
        assert forall|cc: int, rr: int| 0 <= cc < 4 && 0 <= rr < 4 implies -17734 <= #[trigger] sw32(v8(m@[cc]), rr) <= 17734 by {
            assert(-32768 <= sw32(v8(u@[cc]), rr) < 32768 && -17734 <= sw32(v8(m@[cc]), rr) <= 17734);
        }
        assert forall|cc: int, rr: int| 0 <= cc < 4 && 0 <= rr < 4 implies -10046 <= #[trigger] sw32(v8(h@[cc]), rr) <= 10045 by {
            assert(-32768 <= sw32(v8(u@[cc]), rr) < 32768 && -10046 <= sw32(v8(h@[cc]), rr) <= 10045);
        }
    }
    let o = pass2(&u, &m, &h);
    proof {
        assert forall|cc: int, rr: int| 0 <= cc < 4 && 0 <= rr < 4 implies -16384 <= #[trigger] sw32(v8(o@[cc]), rr) <= 16384 by {
            assert(-16384 <= sw32(v8(o@[cc]), rr) <= 16384);
        }
    }
    let (q01, q23) = rows_out(&o);
    proof {
        assert forall|cc: int, rr: int| 0 <= cc < 4 && 0 <= rr < 4 implies #[trigger] sw32(v8(o@[cc]), rr) == res[4 * rr + cc] by {
            let ts = seq![v8(t@[0]), v8(t@[1]), v8(t@[2]), v8(t@[3])];
            assert forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 implies #[trigger] sw16(ts[r], c) == idct_col(iv, c)[r] by {
                assert(ts[r] == v8(t@[r]));
            }
            assert(ts[rr] == v8(t@[rr]));
            lemma_res_lane(iv, ts, v8(u@[0]), v8(u@[1]), v8(u@[2]), v8(u@[3]),
                v8(m@[1]), v8(m@[3]), v8(h@[1]), v8(h@[3]), rr, cc);
            assert(sw32(v8(o@[cc]), rr) == p2(sw32(v8(u@[0]), rr), sw32(v8(u@[1]), rr), sw32(v8(u@[2]), rr), sw32(v8(u@[3]), rr),
                sw32(v8(m@[1]), rr), sw32(v8(m@[3]), rr), sw32(v8(h@[1]), rr), sw32(v8(h@[3]), rr), cc));
        }
        assert forall|l: int| 0 <= l < 8 implies #[trigger] sw16(v8(q01), l) == res[l] && -16384 <= res[l] <= 16384 by {
            assert(sw32(v8(o@[l % 4]), l / 4) == res[4 * (l / 4) + l % 4]);
            assert(-16384 <= sw32(v8(o@[l % 4]), l / 4) <= 16384);
        }
        assert forall|l: int| 0 <= l < 8 implies #[trigger] sw16(v8(q23), l) == res[8 + l] && -16384 <= res[8 + l] <= 16384 by {
            assert(sw32(v8(o@[l % 4]), 2 + l / 4) == res[4 * (2 + l / 4) + l % 4]);
            assert(-16384 <= sw32(v8(o@[l % 4]), 2 + l / 4) <= 16384);
        }
    }
    (q01, q23)
}

/// The second pass's inputs are the first pass's, and its output `idct`.
proof fn lemma_res_lane(iv: Seq<int>, ts: Seq<Seq<u8>>,
    u0: Seq<u8>, u1: Seq<u8>, u2: Seq<u8>, u3: Seq<u8>, m1: Seq<u8>, m3: Seq<u8>, h1: Seq<u8>, h3: Seq<u8>, rr: int, cc: int)
    requires iv.len() == 16, 0 <= rr < 4, 0 <= cc < 4, ts.len() == 4,
        forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 ==> #[trigger] sw16(ts[r], c) == idct_col(iv, c)[r],
        sw32(u0, rr) == sw16(ts[rr], 0), sw32(u1, rr) == sw16(ts[rr], 1),
        sw32(u2, rr) == sw16(ts[rr], 2), sw32(u3, rr) == sw16(ts[rr], 3),
        sw32(m1, rr) == ms(sw16(ts[rr], 1)), sw32(m3, rr) == ms(sw16(ts[rr], 3)),
        sw32(h1, rr) == sw16(ts[rr], 1) * 20091 / 65536, sw32(h3, rr) == sw16(ts[rr], 3) * 20091 / 65536,
    ensures p2(sw32(u0, rr), sw32(u1, rr), sw32(u2, rr), sw32(u3, rr), sw32(m1, rr), sw32(m3, rr), sw32(h1, rr), sw32(h3, rr), cc)
        == idct(iv)[4 * rr + cc],
{
    hide(sw16); hide(sw32); hide(w16); hide(w32); hide(ms);
    reveal(idct);
    let tt = idct1(iv);
    assert(sw16(ts[rr], 0) == tt[4 * rr]) by { assert((4 * rr) % 4 == 0 && (4 * rr) / 4 == rr); }
    assert(sw16(ts[rr], 1) == tt[4 * rr + 1]) by { assert((4 * rr + 1) % 4 == 1 && (4 * rr + 1) / 4 == rr); }
    assert(sw16(ts[rr], 2) == tt[4 * rr + 2]) by { assert((4 * rr + 2) % 4 == 2 && (4 * rr + 2) / 4 == rr); }
    assert(sw16(ts[rr], 3) == tt[4 * rr + 3]) by { assert((4 * rr + 3) % 4 == 3 && (4 * rr + 3) / 4 == rr); }
    assert((4 * rr + cc) / 4 == rr && (4 * rr + cc) % 4 == cc);
}

/// Prediction plus residual, each saturated to a byte.
fn add_sat(q01: __m128i, q23: __m128i, p01: __m128i, p23: __m128i) -> (out: __m128i)
    requires
        forall|l: int| 0 <= l < 8 ==> -16384 <= #[trigger] sw16(v8(q01), l) <= 16384,
        forall|l: int| 0 <= l < 8 ==> -16384 <= #[trigger] sw16(v8(q23), l) <= 16384,
    ensures forall|k: int| 0 <= k < 16 ==> #[trigger] v8(out)[k] == if k < 8 { clamp255(sw16(v8(q01), k) + v8(p01)[k] as int) }
        else { clamp255(sw16(v8(q23), k - 8) + v8(p23)[k - 8] as int) },
{
    let z = sx::setzero();
    let w01 = sx::unpacklo_epi8(p01, z);
    let w23 = sx::unpacklo_epi8(p23, z);
    let s01 = sx::add_epi16(q01, w01);
    let s23 = sx::add_epi16(q23, w23);
    let out = sx::packus_epi16(s01, s23);
    proof {
        assert forall|k: int| 0 <= k < 16 implies #[trigger] v8(out)[k] == if k < 8 { clamp255(sw16(v8(q01), k) + v8(p01)[k] as int) }
            else { clamp255(sw16(v8(q23), k - 8) + v8(p23)[k - 8] as int) } by {
            if k < 8 {
                lemma_out_lane(v8(q01), v8(p01), v8(z), v8(w01), v8(s01), k, sw16(v8(q01), k));
            } else {
                lemma_out_lane(v8(q23), v8(p23), v8(z), v8(w23), v8(s23), k - 8, sw16(v8(q23), k - 8));
            }
        }
    }
    out
}

/// The residual of the coefficients `c` added to the 4 x 4 block at
/// (x, y), in SSE2 (`add_block` of `idct`).
pub fn idct_add_x(v: &mut Vec<u8>, w: usize, x: usize, y: usize, c: &[i32; 16], Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), x + 4 <= w, y + 4 <= pl.len(), c16(c@),
    ensures holds(final(v)@, w as nat, add_block(pl, x as int, y as int, idct(ints(c@)))),
{
    let ghost res = idct(ints(c@));
    let (p01, p23) = pred_bytes(v, w, x, y, Ghost(pl));
    let (q01, q23) = residual(c);
    let out = add_sat(q01, q23, p01, p23);
    proof {
        assert forall|k: int| 0 <= k < 16 implies #[trigger] v8(out)[k] == add_px(pl, x as int, y as int, res, k / 4, k % 4) by {
            if k < 8 {
                assert(sw16(v8(q01), k) == res[k] && v8(p01)[k] == pl[y + k / 4][x + k % 4]);
            } else {
                assert(sw16(v8(q23), k - 8) == res[8 + (k - 8)] && v8(p23)[k - 8] == pl[y + 2 + (k - 8) / 4][x + (k - 8) % 4]);
            }
            assert(4 * (k / 4) + k % 4 == k);
        }
    }
    let ghost t0 = Seq::new(4, |cc: int| add_px(pl, x as int, y as int, res, 0, cc));
    let ghost t1 = Seq::new(4, |cc: int| add_px(pl, x as int, y as int, res, 1, cc));
    let ghost t2 = Seq::new(4, |cc: int| add_px(pl, x as int, y as int, res, 2, cc));
    let ghost t3 = Seq::new(4, |cc: int| add_px(pl, x as int, y as int, res, 3, cc));
    proof {
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t0[mm] == v8(out)[4 * 0 + mm] by { assert((4 * 0 + mm) / 4 == 0 && (4 * 0 + mm) % 4 == mm); }
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t1[mm] == v8(out)[4 * 1 + mm] by { assert((4 * 1 + mm) / 4 == 1 && (4 * 1 + mm) % 4 == mm); }
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t2[mm] == v8(out)[4 * 2 + mm] by { assert((4 * 2 + mm) / 4 == 2 && (4 * 2 + mm) % 4 == mm); }
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t3[mm] == v8(out)[4 * 3 + mm] by { assert((4 * 3 + mm) / 4 == 3 && (4 * 3 + mm) % 4 == mm); }
    }
    put4(v, w, x, y, out, 0, Ghost(pl), Ghost(t0));
    let ghost g1 = set4(pl, x as int, y as int, t0);
    put4(v, w, x, y + 1, out, 1, Ghost(g1), Ghost(t1));
    let ghost g2 = set4(g1, x as int, y + 1, t1);
    put4(v, w, x, y + 2, out, 2, Ghost(g2), Ghost(t2));
    let ghost g3 = set4(g2, x as int, y + 2, t2);
    put4(v, w, x, y + 3, out, 3, Ghost(g3), Ghost(t3));
    proof {
        reveal(add_block);
        let g4 = set4(g3, x as int, y + 3, t3);
        assert(g4 =~~= add_block(pl, x as int, y as int, res));
    }
}

/// The 4 x 4 block at (x, y) set to `pred` (row-major).
pub open spec fn set_pred(p: Plane, x: int, y: int, pred: Seq<u8>) -> Plane {
    set_block(p, x, y, 4, |r: int, c: int| pred[4 * r + c])
}

/// The residual of `c` added to the prediction `pred` of the 4 x 4 block
/// at (x, y), the prediction given as bytes rather than read back from
/// the plane.
pub fn idct_add_pred_x(v: &mut Vec<u8>, w: usize, x: usize, y: usize, pred: &[u8; 16], c: &[i32; 16], Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), x + 4 <= w, y + 4 <= pl.len(), c16(c@),
    ensures holds(final(v)@, w as nat, add_block(set_pred(pl, x as int, y as int, pred@), x as int, y as int, idct(ints(c@)))),
{
    let ghost res = idct(ints(c@));
    let ghost pp = set_pred(pl, x as int, y as int, pred@);
    let pa = sx::from_bytes(*pred);
    let pb = sx::unpackhi_epi64(pa, pa);
    let (q01, q23) = residual(c);
    let out = add_sat(q01, q23, pa, pb);
    proof {
        assert forall|k: int| 0 <= k < 16 implies #[trigger] v8(out)[k] == add_px(pp, x as int, y as int, res, k / 4, k % 4) by {
            assert(4 * (k / 4) + k % 4 == k);
            assert(pp[y + k / 4][x + k % 4] == pred@[k]);
            if k < 8 {
                assert(sw16(v8(q01), k) == res[k]);
            } else {
                assert(sw16(v8(q23), k - 8) == res[8 + (k - 8)]);
                assert(v8(pb)[k - 8] == v8(pa)[8 + (k - 8)]);
            }
        }
    }
    let ghost t0 = Seq::new(4, |cc: int| add_px(pp, x as int, y as int, res, 0, cc));
    let ghost t1 = Seq::new(4, |cc: int| add_px(pp, x as int, y as int, res, 1, cc));
    let ghost t2 = Seq::new(4, |cc: int| add_px(pp, x as int, y as int, res, 2, cc));
    let ghost t3 = Seq::new(4, |cc: int| add_px(pp, x as int, y as int, res, 3, cc));
    proof {
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t0[mm] == v8(out)[4 * 0 + mm] by { assert((4 * 0 + mm) / 4 == 0 && (4 * 0 + mm) % 4 == mm); }
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t1[mm] == v8(out)[4 * 1 + mm] by { assert((4 * 1 + mm) / 4 == 1 && (4 * 1 + mm) % 4 == mm); }
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t2[mm] == v8(out)[4 * 2 + mm] by { assert((4 * 2 + mm) / 4 == 2 && (4 * 2 + mm) % 4 == mm); }
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t3[mm] == v8(out)[4 * 3 + mm] by { assert((4 * 3 + mm) / 4 == 3 && (4 * 3 + mm) % 4 == mm); }
    }
    put4(v, w, x, y, out, 0, Ghost(pl), Ghost(t0));
    let ghost g1 = set4(pl, x as int, y as int, t0);
    put4(v, w, x, y + 1, out, 1, Ghost(g1), Ghost(t1));
    let ghost g2 = set4(g1, x as int, y + 1, t1);
    put4(v, w, x, y + 2, out, 2, Ghost(g2), Ghost(t2));
    let ghost g3 = set4(g2, x as int, y + 2, t2);
    put4(v, w, x, y + 3, out, 3, Ghost(g3), Ghost(t3));
    proof {
        reveal(add_block);
        let g4 = set4(g3, x as int, y + 3, t3);
        assert(g4 =~~= add_block(pp, x as int, y as int, res));
    }
}

// ------------------------------------------------- blocks with only a DC

/// A block's coefficients past the first are all zero.
pub open spec fn dc_only(c: Seq<i32>) -> bool { forall|k: int| 1 <= k < 16 ==> #[trigger] c[k] == 0 }

/// The inverse DCT of a DC alone is (DC + 4) >> 3 everywhere.
pub proof fn lemma_idct_dc(c: Seq<i32>)
    requires c.len() == 16, c16(c), dc_only(c),
    ensures forall|j: int| 0 <= j < 16 ==> #[trigger] idct(ints(c))[j] == (c[0] + 4) / 8,
{
    reveal(idct);
    let iv = ints(c);
    assert(ms(0) == 0 && mc(0) == 0);
    let t = idct1(iv);
    assert forall|j: int| 0 <= j < 16 implies #[trigger] t[j] == if j % 4 == 0 { c[0] as int } else { 0 } by {
        assert(iv[4 + j % 4] == 0 && iv[12 + j % 4] == 0);
        if j % 4 != 0 { assert(iv[j % 4] == 0 && iv[8 + j % 4] == 0); } else { assert(iv[8] == 0); }
    }
    assert forall|j: int| 0 <= j < 16 implies #[trigger] idct(iv)[j] == (c[0] + 4) / 8 by {
        let r = j / 4;
        assert(t[4 * r] == c[0] as int && t[4 * r + 1] == 0 && t[4 * r + 2] == 0 && t[4 * r + 3] == 0) by {
            assert((4 * r) % 4 == 0 && (4 * r + 1) % 4 == 1 && (4 * r + 2) % 4 == 2 && (4 * r + 3) % 4 == 3);
        }
    }
}

/// Whether the coefficients past the first are zero.
pub fn is_dc_only(c: &[i32; 16]) -> (r: bool)
    ensures r == dc_only(c@),
{
    let o = c[1] | c[2] | c[3] | c[4] | c[5] | c[6] | c[7] | c[8] | c[9] | c[10] | c[11] | c[12] | c[13] | c[14] | c[15];
    proof {
        let (x1, x2, x3, x4, x5, x6, x7, x8) = (c[1], c[2], c[3], c[4], c[5], c[6], c[7], c[8]);
        let (x9, x10, x11, x12, x13, x14, x15) = (c[9], c[10], c[11], c[12], c[13], c[14], c[15]);
        assert((x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15 == 0) ==
            (x1 == 0 && x2 == 0 && x3 == 0 && x4 == 0 && x5 == 0 && x6 == 0 && x7 == 0 && x8 == 0
             && x9 == 0 && x10 == 0 && x11 == 0 && x12 == 0 && x13 == 0 && x14 == 0 && x15 == 0)) by (bit_vector);
        if o == 0 {
            assert forall|k: int| 1 <= k < 16 implies #[trigger] c@[k] == 0 by {}
        }
    }
    o == 0
}

/// The residual of a DC alone, in all 16-bit lanes.
fn dc_residual(c: &[i32; 16]) -> (q: __m128i)
    requires c16(c@), dc_only(c@),
    ensures forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(v8(q), l) == idct(ints(c@))[l] && sw16(v8(q), l) == idct(ints(c@))[8 + l]
        && -16384 <= idct(ints(c@))[l] <= 16384 && -16384 <= idct(ints(c@))[8 + l] <= 16384,
{
    let t = c[0] + 4;
    let d = t >> 3u32;
    proof {
        assert(d as int == (t as int) / 8) by (bit_vector) requires d == t >> 3u32;
        lemma_idct_dc(c@);
    }
    let du: u16 = if d < 0 { (d + 65536) as u16 } else { d as u16 };
    let q = sx::set1_epi16(du);
    proof {
        assert forall|l: int| 0 <= l < 8 implies #[trigger] sw16(v8(q), l) == d as int by {
            lemma_set1_16_lane(du, l);
        }
    }
    q
}

/// A DC-only block's residual added to the prediction `pred`.
pub fn dc_add_pred_x(v: &mut Vec<u8>, w: usize, x: usize, y: usize, pred: &[u8; 16], c: &[i32; 16], Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), x + 4 <= w, y + 4 <= pl.len(), c16(c@), dc_only(c@),
    ensures holds(final(v)@, w as nat, add_block(set_pred(pl, x as int, y as int, pred@), x as int, y as int, idct(ints(c@)))),
{
    let ghost res = idct(ints(c@));
    let ghost pp = set_pred(pl, x as int, y as int, pred@);
    let pa = sx::from_bytes(*pred);
    let pb = sx::unpackhi_epi64(pa, pa);
    let q = dc_residual(c);
    let out = add_sat(q, q, pa, pb);
    proof {
        assert forall|k: int| 0 <= k < 16 implies #[trigger] v8(out)[k] == add_px(pp, x as int, y as int, res, k / 4, k % 4) by {
            assert(4 * (k / 4) + k % 4 == k);
            assert(pp[y + k / 4][x + k % 4] == pred@[k]);
            if k < 8 {
                assert(sw16(v8(q), k) == res[k]);
            } else {
                assert(sw16(v8(q), k - 8) == res[8 + (k - 8)]);
                assert(v8(pb)[k - 8] == v8(pa)[8 + (k - 8)]);
            }
        }
    }
    let ghost t0 = Seq::new(4, |cc: int| add_px(pp, x as int, y as int, res, 0, cc));
    let ghost t1 = Seq::new(4, |cc: int| add_px(pp, x as int, y as int, res, 1, cc));
    let ghost t2 = Seq::new(4, |cc: int| add_px(pp, x as int, y as int, res, 2, cc));
    let ghost t3 = Seq::new(4, |cc: int| add_px(pp, x as int, y as int, res, 3, cc));
    proof {
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t0[mm] == v8(out)[4 * 0 + mm] by { assert((4 * 0 + mm) / 4 == 0 && (4 * 0 + mm) % 4 == mm); }
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t1[mm] == v8(out)[4 * 1 + mm] by { assert((4 * 1 + mm) / 4 == 1 && (4 * 1 + mm) % 4 == mm); }
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t2[mm] == v8(out)[4 * 2 + mm] by { assert((4 * 2 + mm) / 4 == 2 && (4 * 2 + mm) % 4 == mm); }
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t3[mm] == v8(out)[4 * 3 + mm] by { assert((4 * 3 + mm) / 4 == 3 && (4 * 3 + mm) % 4 == mm); }
    }
    put4(v, w, x, y, out, 0, Ghost(pl), Ghost(t0));
    let ghost g1 = set4(pl, x as int, y as int, t0);
    put4(v, w, x, y + 1, out, 1, Ghost(g1), Ghost(t1));
    let ghost g2 = set4(g1, x as int, y + 1, t1);
    put4(v, w, x, y + 2, out, 2, Ghost(g2), Ghost(t2));
    let ghost g3 = set4(g2, x as int, y + 2, t2);
    put4(v, w, x, y + 3, out, 3, Ghost(g3), Ghost(t3));
    proof {
        reveal(add_block);
        let g4 = set4(g3, x as int, y + 3, t3);
        assert(g4 =~~= add_block(pp, x as int, y as int, res));
    }
}

/// A DC-only block's residual added to the plane's own prediction.
pub fn dc_add_x(v: &mut Vec<u8>, w: usize, x: usize, y: usize, c: &[i32; 16], Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), x + 4 <= w, y + 4 <= pl.len(), c16(c@), dc_only(c@),
    ensures holds(final(v)@, w as nat, add_block(pl, x as int, y as int, idct(ints(c@)))),
{
    let ghost res = idct(ints(c@));
    let (p01, p23) = pred_bytes(v, w, x, y, Ghost(pl));
    let q = dc_residual(c);
    let out = add_sat(q, q, p01, p23);
    proof {
        assert forall|k: int| 0 <= k < 16 implies #[trigger] v8(out)[k] == add_px(pl, x as int, y as int, res, k / 4, k % 4) by {
            if k < 8 {
                assert(sw16(v8(q), k) == res[k] && v8(p01)[k] == pl[y + k / 4][x + k % 4]);
            } else {
                assert(sw16(v8(q), k - 8) == res[8 + (k - 8)] && v8(p23)[k - 8] == pl[y + 2 + (k - 8) / 4][x + (k - 8) % 4]);
            }
            assert(4 * (k / 4) + k % 4 == k);
        }
    }
    let ghost t0 = Seq::new(4, |cc: int| add_px(pl, x as int, y as int, res, 0, cc));
    let ghost t1 = Seq::new(4, |cc: int| add_px(pl, x as int, y as int, res, 1, cc));
    let ghost t2 = Seq::new(4, |cc: int| add_px(pl, x as int, y as int, res, 2, cc));
    let ghost t3 = Seq::new(4, |cc: int| add_px(pl, x as int, y as int, res, 3, cc));
    proof {
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t0[mm] == v8(out)[4 * 0 + mm] by { assert((4 * 0 + mm) / 4 == 0 && (4 * 0 + mm) % 4 == mm); }
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t1[mm] == v8(out)[4 * 1 + mm] by { assert((4 * 1 + mm) / 4 == 1 && (4 * 1 + mm) % 4 == mm); }
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t2[mm] == v8(out)[4 * 2 + mm] by { assert((4 * 2 + mm) / 4 == 2 && (4 * 2 + mm) % 4 == mm); }
        assert forall|mm: int| 0 <= mm < 4 implies #[trigger] t3[mm] == v8(out)[4 * 3 + mm] by { assert((4 * 3 + mm) / 4 == 3 && (4 * 3 + mm) % 4 == mm); }
    }
    put4(v, w, x, y, out, 0, Ghost(pl), Ghost(t0));
    let ghost g1 = set4(pl, x as int, y as int, t0);
    put4(v, w, x, y + 1, out, 1, Ghost(g1), Ghost(t1));
    let ghost g2 = set4(g1, x as int, y + 1, t1);
    put4(v, w, x, y + 2, out, 2, Ghost(g2), Ghost(t2));
    let ghost g3 = set4(g2, x as int, y + 2, t2);
    put4(v, w, x, y + 3, out, 3, Ghost(g3), Ghost(t3));
    proof {
        reveal(add_block);
        let g4 = set4(g3, x as int, y + 3, t3);
        assert(g4 =~~= add_block(pl, x as int, y as int, res));
    }
}

/// A zero residual leaves the block as it is.
pub proof fn lemma_add_zero(pl: Plane, w: nat, x: int, y: int, c: Seq<i32>)
    requires c.len() == 16, c16(c), dc_only(c), c[0] == 0, rows_w(pl, w), 0 <= x, x + 4 <= w, 0 <= y, y + 4 <= pl.len(),
    ensures add_block(pl, x, y, idct(ints(c))) == pl,
{
    lemma_idct_dc(c);
    reveal(add_block);
    assert(add_block(pl, x, y, idct(ints(c))) =~~= pl);
}

} // verus!
