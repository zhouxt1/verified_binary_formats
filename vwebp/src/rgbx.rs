//! `rgb::render`'s pixels, eight at a time in SSE2 (vsimd), for the 4-byte
//! modes without premultiplication (RGBA, BGRA, ARGB): libwebp's
//! `yuv_sse2.c` way, `_mm_mulhi_epu16` of the sample shifted up 8 bits for
//! `MultHi`, 16-bit sums, an arithmetic shift by 6 and `packus` for
//! `VP8Clip8`, and saturating unsigned arithmetic for blue, whose sum
//! leaves 16 signed bits. Proved lane by lane to be `rgb::yuv_r/g/b`.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
#[cfg(verus_keep_ghost)]
use vsimd::spec::{w16, sw16, clamp, lemma_sw16_of, lemma_mulhiu_lane, lemma_addsu_lane, lemma_subsu_lane,
    lemma_srai16_lane, lemma_srli16_lane, lemma_hi8_lane, lemma_zext_lane, lemma_set1_16_lane, lemma_add16_lane,
    lemma_sub16_lane, lemma_w16_bounds, lo8};
#[cfg(verus_keep_ghost)]
use vsimd::x86::{byte, v8, lemma_byte};
use vsimd::x86::__m128i;
use vsimd::x86 as sx;
use crate::rgb::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::pow2;
use crate::vp8::dec::FrameX;
#[cfg(verus_keep_ghost)]
use crate::vp8::plane::{holds, lemma_idx};

verus! {

broadcast use lemma_byte;

/// (R, G, B, A) of lane `m` of the Y', U, V and alpha vectors.
pub open spec fn tup(yb: Seq<u8>, ub: Seq<u8>, vb: Seq<u8>, ab: Seq<u8>, m: int) -> (u8, u8, u8, u8) {
    (yuv_r(yb[m], vb[m]), yuv_g(yb[m], ub[m], vb[m]), yuv_b(yb[m], ub[m]), ab[m])
}

/// Byte `i` of the 32 the pair holds.
pub open spec fn out32(r: (__m128i, __m128i), i: int) -> u8 {
    if i < 16 { v8(r.0)[i] } else { v8(r.1)[i - 16] }
}

/// `packus` after an arithmetic shift by 6 is `VP8Clip8`.
proof fn lemma_clip(x: int)
    requires -32768 <= x < 32768,
    ensures clamp(x / 64, 0, 255) == clip8(x) as int,
{
    if x < 0 { assert(x / 64 < 0); }
    else if x >= 16384 { assert(x / 64 >= 256); }
    else { assert(0 <= x / 64 < 256); }
}

/// `MultHi` of a byte put in the high half of a 16-bit lane.
proof fn lemma_mh(a: int, k: int)
    requires 0 <= a < 256, 0 <= k < 65536,
    ensures (256 * a) * k / 65536 == mult_hi(a, k), 0 <= mult_hi(a, k) <= (255 * k) / 256,
{
    let x = a * k;
    assert(x >= 0) by (nonlinear_arith) requires a >= 0, k >= 0, x == a * k;
    assert(x <= 255 * k) by (nonlinear_arith) requires 0 <= a < 256, k >= 0, x == a * k;
    lemma_fundamental_div_mod(x, 256);
    assert((256 * a) * k == 65536 * (x / 256) + 256 * (x % 256)) by (nonlinear_arith)
        requires x == a * k, x == 256 * (x / 256) + x % 256;
    lemma_fundamental_div_mod_converse((256 * a) * k, 65536, x / 256, 256 * (x % 256));
    vstd::arithmetic::div_mod::lemma_div_is_ordered(x, 255 * k, 256);
}

proof fn lemma_p64()
    ensures vstd::arithmetic::power2::pow2(6) == 64,
{
    vstd::arithmetic::power2::lemma2_to64();
}

// The kernel's lanes, as functions of the input vectors' bytes.

pub open spec fn zero() -> Seq<u8> { vsimd::spec::set1_epi8(0) }
pub open spec fn mh(a: Seq<u8>, k: u16) -> Seq<u8> { vsimd::spec::mulhi_epu16(vsimd::spec::unpacklo_epi8(zero(), a), vsimd::spec::set1_epi16(k)) }
pub open spec fn red(ys: Seq<u8>, vs: Seq<u8>) -> Seq<u8> {
    vsimd::spec::srai_epi16(vsimd::spec::sub_epi16(vsimd::spec::add_epi16(mh(ys, 19077), mh(vs, 26149)), vsimd::spec::set1_epi16(14234)), 6)
}
pub open spec fn green(ys: Seq<u8>, us: Seq<u8>, vs: Seq<u8>) -> Seq<u8> {
    vsimd::spec::srai_epi16(vsimd::spec::sub_epi16(vsimd::spec::sub_epi16(vsimd::spec::add_epi16(mh(ys, 19077),
        vsimd::spec::set1_epi16(8708)), mh(us, 6419)), mh(vs, 13320)), 6)
}
pub open spec fn blue(ys: Seq<u8>, us: Seq<u8>) -> Seq<u8> {
    vsimd::spec::srli_epi16(vsimd::spec::subs_epu16(vsimd::spec::adds_epu16(mh(ys, 19077), mh(us, 33050)), vsimd::spec::set1_epi16(17685)), 6)
}
pub open spec fn alpha16(als: Seq<u8>) -> Seq<u8> { vsimd::spec::unpacklo_epi8(als, zero()) }

/// The four channel vectors packed and interleaved: bytes `4m + k` are
/// lane m of channel k, saturated to a byte.
pub open spec fn il(c0: Seq<u8>, c1: Seq<u8>, c2: Seq<u8>, c3: Seq<u8>, i: int) -> u8 {
    let p = vsimd::spec::packus_epi16(c0, c2);
    let q = vsimd::spec::packus_epi16(c1, c3);
    let lo = vsimd::spec::unpacklo_epi8(p, q);
    let hi = vsimd::spec::unpackhi_epi8(p, q);
    if i < 16 { vsimd::spec::unpacklo_epi16(lo, hi)[i] } else { vsimd::spec::unpackhi_epi16(lo, hi)[i - 16] }
}

proof fn lemma_mh_lane(a: Seq<u8>, k: u16, j: int)
    requires a.len() == 16, 0 <= j < 8,
    ensures w16(mh(a, k), j) == mult_hi(a[j] as int, k as int), 0 <= mult_hi(a[j] as int, k as int) <= (255 * k) / 256,
{
    assert forall|q: int| 0 <= q < 16 implies #[trigger] zero()[q] == 0 by {}
    lemma_hi8_lane(zero(), a, j);
    lemma_set1_16_lane(k, j);
    lemma_mulhiu_lane(vsimd::spec::unpacklo_epi8(zero(), a), vsimd::spec::set1_epi16(k), j);
    lemma_mh(a[j] as int, k as int);
}

/// The lengths of the kernel's intermediate vectors.
proof fn lemma_lens(ys: Seq<u8>, us: Seq<u8>, vs: Seq<u8>)
    ensures
        mh(ys, 19077).len() == 16, mh(us, 6419).len() == 16, mh(us, 33050).len() == 16, mh(vs, 13320).len() == 16, mh(vs, 26149).len() == 16,
        vsimd::spec::set1_epi16(14234).len() == 16, vsimd::spec::set1_epi16(8708).len() == 16, vsimd::spec::set1_epi16(17685).len() == 16,
        vsimd::spec::add_epi16(mh(ys, 19077), mh(vs, 26149)).len() == 16,
        vsimd::spec::sub_epi16(vsimd::spec::add_epi16(mh(ys, 19077), mh(vs, 26149)), vsimd::spec::set1_epi16(14234)).len() == 16,
        red(ys, vs).len() == 16,
        vsimd::spec::add_epi16(mh(ys, 19077), vsimd::spec::set1_epi16(8708)).len() == 16,
        vsimd::spec::sub_epi16(vsimd::spec::add_epi16(mh(ys, 19077), vsimd::spec::set1_epi16(8708)), mh(us, 6419)).len() == 16,
        vsimd::spec::sub_epi16(vsimd::spec::sub_epi16(vsimd::spec::add_epi16(mh(ys, 19077), vsimd::spec::set1_epi16(8708)), mh(us, 6419)), mh(vs, 13320)).len() == 16,
        green(ys, us, vs).len() == 16,
        vsimd::spec::adds_epu16(mh(ys, 19077), mh(us, 33050)).len() == 16,
        vsimd::spec::subs_epu16(vsimd::spec::adds_epu16(mh(ys, 19077), mh(us, 33050)), vsimd::spec::set1_epi16(17685)).len() == 16,
        blue(ys, us).len() == 16,
{}

proof fn lemma_red(ys: Seq<u8>, vs: Seq<u8>, j: int)
    requires ys.len() == 16, vs.len() == 16, 0 <= j < 8,
    ensures clamp(sw16(red(ys, vs), j), 0, 255) == yuv_r(ys[j], vs[j]) as int,
{
    hide(vsimd::spec::add_epi16); hide(vsimd::spec::sub_epi16); hide(vsimd::spec::adds_epu16); hide(vsimd::spec::subs_epu16);
    hide(vsimd::spec::mulhi_epu16); hide(vsimd::spec::set1_epi16); hide(vsimd::spec::srai_epi16); hide(vsimd::spec::srli_epi16);
    hide(vsimd::spec::unpacklo_epi8); hide(vsimd::spec::set1_epi8); hide(mult_hi); hide(w16); hide(sw16);
    lemma_lens(ys, vs, vs);
    lemma_mh_lane(ys, 19077, j);
    lemma_mh_lane(vs, 26149, j);
    let (yy, vr) = (mult_hi(ys[j] as int, 19077), mult_hi(vs[j] as int, 26149));
    assert(yy <= 19002 && vr <= 26046);
    let s = vsimd::spec::add_epi16(mh(ys, 19077), mh(vs, 26149));
    let d = vsimd::spec::sub_epi16(s, vsimd::spec::set1_epi16(14234));
    lemma_add16_lane(mh(ys, 19077), mh(vs, 26149), j);
    lemma_set1_16_lane(14234, j);
    lemma_sub16_lane(s, vsimd::spec::set1_epi16(14234), j);
    lemma_sw16_of(d, j, yy + vr - 14234);
    lemma_p64();
    lemma_srai16_lane(d, 6, j);
    lemma_clip(yy + vr - 14234);
}

#[verifier::rlimit(60)]
proof fn lemma_green(ys: Seq<u8>, us: Seq<u8>, vs: Seq<u8>, j: int)
    requires ys.len() == 16, us.len() == 16, vs.len() == 16, 0 <= j < 8,
    ensures clamp(sw16(green(ys, us, vs), j), 0, 255) == yuv_g(ys[j], us[j], vs[j]) as int,
{
    hide(vsimd::spec::add_epi16); hide(vsimd::spec::sub_epi16); hide(vsimd::spec::adds_epu16); hide(vsimd::spec::subs_epu16);
    hide(vsimd::spec::mulhi_epu16); hide(vsimd::spec::set1_epi16); hide(vsimd::spec::srai_epi16); hide(vsimd::spec::srli_epi16);
    hide(vsimd::spec::unpacklo_epi8); hide(vsimd::spec::set1_epi8); hide(mult_hi); hide(w16); hide(sw16);
    lemma_lens(ys, us, vs);
    lemma_mh_lane(ys, 19077, j);
    lemma_mh_lane(us, 6419, j);
    lemma_mh_lane(vs, 13320, j);
    let (yy, ur, vg) = (mult_hi(ys[j] as int, 19077), mult_hi(us[j] as int, 6419), mult_hi(vs[j] as int, 13320));
    assert(yy <= 19002 && ur <= 6393 && vg <= 13267);
    let s = vsimd::spec::add_epi16(mh(ys, 19077), vsimd::spec::set1_epi16(8708));
    let d = vsimd::spec::sub_epi16(s, mh(us, 6419));
    let e = vsimd::spec::sub_epi16(d, mh(vs, 13320));
    lemma_set1_16_lane(8708, j);
    lemma_add16_lane(mh(ys, 19077), vsimd::spec::set1_epi16(8708), j);
    lemma_sub16_lane(s, mh(us, 6419), j);
    lemma_sub16_lane(d, mh(vs, 13320), j);
    assert(w16(s, j) == yy + 8708);
    assert(w16(d, j) == yy + 8708 - ur);
    lemma_sw16_of(e, j, yy - ur - vg + 8708);
    lemma_p64();
    lemma_srai16_lane(e, 6, j);
    lemma_clip(yy - ur - vg + 8708);
}

#[verifier::rlimit(60)]
proof fn lemma_blue(ys: Seq<u8>, us: Seq<u8>, j: int)
    requires ys.len() == 16, us.len() == 16, 0 <= j < 8,
    ensures clamp(sw16(blue(ys, us), j), 0, 255) == yuv_b(ys[j], us[j]) as int,
{
    hide(vsimd::spec::add_epi16); hide(vsimd::spec::sub_epi16); hide(vsimd::spec::adds_epu16); hide(vsimd::spec::subs_epu16);
    hide(vsimd::spec::mulhi_epu16); hide(vsimd::spec::set1_epi16); hide(vsimd::spec::srai_epi16); hide(vsimd::spec::srli_epi16);
    hide(vsimd::spec::unpacklo_epi8); hide(vsimd::spec::set1_epi8); hide(mult_hi); hide(w16); hide(sw16);
    lemma_lens(ys, us, us);
    lemma_mh_lane(ys, 19077, j);
    lemma_mh_lane(us, 33050, j);
    let (yy, ub) = (mult_hi(ys[j] as int, 19077), mult_hi(us[j] as int, 33050));
    assert(yy <= 19002 && ub <= 32921);
    let s = vsimd::spec::adds_epu16(mh(ys, 19077), mh(us, 33050));
    let d = vsimd::spec::subs_epu16(s, vsimd::spec::set1_epi16(17685));
    lemma_addsu_lane(mh(ys, 19077), mh(us, 33050), j);
    lemma_set1_16_lane(17685, j);
    lemma_subsu_lane(s, vsimd::spec::set1_epi16(17685), j);
    lemma_p64();
    lemma_srli16_lane(d, 6, j);
    let xb = yy + ub - 17685;
    let mb = if xb < 0 { 0 } else { xb };
    assert(w16(d, j) == mb);
    let bb = blue(ys, us);
    assert(w16(bb, j) == mb / 64);
    lemma_w16_bounds(bb, j);
    assert(sw16(bb, j) == mb / 64);
    if xb < 0 { assert(clip8(xb) == 0); }
    else if xb >= 16384 { assert(mb / 64 >= 256); assert(clip8(xb) == 255); }
    else { assert(clip8(xb) as int == xb / 64); }
}

proof fn lemma_alpha(als: Seq<u8>, j: int)
    requires als.len() == 16, 0 <= j < 8,
    ensures clamp(sw16(alpha16(als), j), 0, 255) == als[j] as int,
{
    assert forall|q: int| 0 <= q < 16 implies #[trigger] zero()[q] == 0 by {}
    lemma_zext_lane(als, zero(), j);
}

proof fn lemma_il(c0: Seq<u8>, c1: Seq<u8>, c2: Seq<u8>, c3: Seq<u8>, i: int)
    requires c0.len() == 16, c1.len() == 16, c2.len() == 16, c3.len() == 16, 0 <= i < 32,
    ensures il(c0, c1, c2, c3, i) as int == clamp(sw16(if i % 4 == 0 { c0 } else if i % 4 == 1 { c1 } else if i % 4 == 2 { c2 } else { c3 }, i / 4), 0, 255),
{
    let m = i / 4;
    let k = i % 4;
    let p = vsimd::spec::packus_epi16(c0, c2);
    let q = vsimd::spec::packus_epi16(c1, c3);
    let lo = vsimd::spec::unpacklo_epi8(p, q);
    let hi = vsimd::spec::unpackhi_epi8(p, q);
    let e = if i < 16 { i } else { i - 16 };
    assert(e / 2 == 2 * (m % 4) + k / 2 && e % 2 == k % 2 && (e / 2) % 2 == k / 2 && e / 2 / 2 == m % 4);
    let src = (m % 4) * 2 + k % 2 + if i < 16 { 0int } else { 8int };
    assert(src == 2 * m + k % 2);
    assert(il(c0, c1, c2, c3, i) == if k / 2 == 0 { lo[src] } else { hi[src] });
    assert(src / 2 == m && src % 2 == k % 2);
}

/// The eight pixels' 32 bytes in `mode`: RGBA, BGRA or ARGB.
#[inline(always)]
pub fn rgba8_x(yb: __m128i, ub: __m128i, vb: __m128i, ab: __m128i, mode: u8) -> (r: (__m128i, __m128i))
    requires mode == 1 || mode == 3 || mode == 4,
    ensures
        forall|i: int| 0 <= i < 32 ==> #[trigger] out32(r, i) == px_byte(mode, tup(v8(yb), v8(ub), v8(vb), v8(ab), i / 4), i % 4),
{
    hide(vsimd::spec::add_epi16); hide(vsimd::spec::sub_epi16); hide(vsimd::spec::adds_epu16); hide(vsimd::spec::subs_epu16);
    hide(vsimd::spec::mulhi_epu16); hide(vsimd::spec::set1_epi16); hide(vsimd::spec::srai_epi16); hide(vsimd::spec::srli_epi16);
    hide(vsimd::spec::unpacklo_epi8); hide(vsimd::spec::set1_epi8); hide(mult_hi); 
    let z = sx::setzero();
    let yw = sx::unpacklo_epi8(z, yb);
    let uw = sx::unpacklo_epi8(z, ub);
    let vw = sx::unpacklo_epi8(z, vb);
    let y1 = sx::mulhi_epu16(yw, sx::set1_epi16(19077));
    let u1 = sx::mulhi_epu16(uw, sx::set1_epi16(6419));
    let u2 = sx::mulhi_epu16(uw, sx::set1_epi16(33050));
    let v1 = sx::mulhi_epu16(vw, sx::set1_epi16(13320));
    let v2 = sx::mulhi_epu16(vw, sx::set1_epi16(26149));
    let r = sx::srai_epi16_6(sx::sub_epi16(sx::add_epi16(y1, v2), sx::set1_epi16(14234)));
    let g = sx::srai_epi16_6(sx::sub_epi16(sx::sub_epi16(sx::add_epi16(y1, sx::set1_epi16(8708)), u1), v1));
    let b = sx::srli_epi16_6(sx::subs_epu16(sx::adds_epu16(y1, u2), sx::set1_epi16(17685)));
    let a = sx::unpacklo_epi8(ab, z);
    let ghost (ys, us, vs, als) = (v8(yb), v8(ub), v8(vb), v8(ab));
    proof {
        assert(v8(r) == red(ys, vs));
        assert(v8(g) == green(ys, us, vs));
        assert(v8(b) == blue(ys, us));
        assert(v8(a) == alpha16(als));
    }
    let (c0, c1, c2, c3) = if mode == 1 { (r, g, b, a) } else if mode == 3 { (b, g, r, a) } else { (a, r, g, b) };
    let p = sx::packus_epi16(c0, c2);
    let q = sx::packus_epi16(c1, c3);
    let lo = sx::unpacklo_epi8(p, q);
    let hi = sx::unpackhi_epi8(p, q);
    let o1 = sx::unpacklo_epi16(lo, hi);
    let o2 = sx::unpackhi_epi16(lo, hi);
    proof {
        assert forall|m: int| 0 <= m < 8 implies #[trigger] clamp(sw16(v8(r), m), 0, 255) == yuv_r(ys[m], vs[m]) as int by { lemma_red(ys, vs, m); }
        assert forall|m: int| 0 <= m < 8 implies #[trigger] clamp(sw16(v8(g), m), 0, 255) == yuv_g(ys[m], us[m], vs[m]) as int by { lemma_green(ys, us, vs, m); }
        assert forall|m: int| 0 <= m < 8 implies #[trigger] clamp(sw16(v8(b), m), 0, 255) == yuv_b(ys[m], us[m]) as int by { lemma_blue(ys, us, m); }
        assert forall|m: int| 0 <= m < 8 implies #[trigger] clamp(sw16(v8(a), m), 0, 255) == als[m] as int by { lemma_alpha(als, m); }
        assert forall|i: int| 0 <= i < 32 implies #[trigger] out32((o1, o2), i) == px_byte(mode, tup(ys, us, vs, als, i / 4), i % 4) by {
            assert(out32((o1, o2), i) == il(v8(c0), v8(c1), v8(c2), v8(c3), i));
            lemma_il(v8(c0), v8(c1), v8(c2), v8(c3), i);
        }
    }
    (o1, o2)
}

// ---------------------------------------------------------------------------
// The chroma upsampler, eight chroma columns (sixteen outputs) at a time.

/// Eight bytes of `s` from `i`, zero-extended to 16-bit lanes.
pub open spec fn zx(s: Seq<u8>, i: int) -> Seq<u8> {
    vsimd::spec::unpacklo_epi8(lo8(s.subrange(i, i + 8)), zero())
}

/// `3 * n + f`, lane by lane.
pub open spec fn tri(n: Seq<u8>, f: Seq<u8>) -> Seq<u8> {
    vsimd::spec::add_epi16(vsimd::spec::add_epi16(vsimd::spec::add_epi16(n, n), n), f)
}

/// `(3 * c + s + 8) >> 4`, lane by lane.
pub open spec fn mix(c: Seq<u8>, s: Seq<u8>) -> Seq<u8> {
    vsimd::spec::srli_epi16(vsimd::spec::add_epi16(vsimd::spec::add_epi16(vsimd::spec::add_epi16(
        vsimd::spec::add_epi16(c, c), c), s), vsimd::spec::set1_epi16(8)), 4)
}

proof fn lemma_zx_lane(s: Seq<u8>, i: int, l: int)
    requires 0 <= i, i + 8 <= s.len(), 0 <= l < 8,
    ensures w16(zx(s, i), l) == s[i + l] as int, zx(s, i).len() == 16,
{
    assert forall|q: int| 0 <= q < 16 implies #[trigger] zero()[q] == 0 by {}
    lemma_zext_lane(lo8(s.subrange(i, i + 8)), zero(), l);
}

proof fn lemma_len_add(a: Seq<u8>, b: Seq<u8>) ensures vsimd::spec::add_epi16(a, b).len() == 16 {}
proof fn lemma_len_set8() ensures vsimd::spec::set1_epi16(8).len() == 16 {}
proof fn lemma_len_srl4(a: Seq<u8>) ensures vsimd::spec::srli_epi16(a, 4).len() == 16 {}

#[verifier::rlimit(40)]
proof fn lemma_tri_lane(n: Seq<u8>, f: Seq<u8>, l: int)
    requires n.len() == 16, f.len() == 16, 0 <= l < 8, w16(n, l) < 256, w16(f, l) < 256,
    ensures w16(tri(n, f), l) == 3 * w16(n, l) + w16(f, l), tri(n, f).len() == 16,
{
    hide(vsimd::spec::add_epi16); hide(w16);
    let n2 = vsimd::spec::add_epi16(n, n);
    let n3 = vsimd::spec::add_epi16(n2, n);
    lemma_len_add(n, n); lemma_len_add(n2, n); lemma_len_add(n3, f);
    lemma_w16_bounds(n, l);
    lemma_w16_bounds(f, l);
    lemma_add16_lane(n, n, l);
    lemma_add16_lane(n2, n, l);
    lemma_add16_lane(n3, f, l);
}

#[verifier::rlimit(40)]
proof fn lemma_mix_lane(c: Seq<u8>, t: Seq<u8>, l: int)
    requires c.len() == 16, t.len() == 16, 0 <= l < 8, w16(c, l) <= 1020, w16(t, l) <= 1020,
    ensures w16(mix(c, t), l) == (3 * w16(c, l) + w16(t, l) + 8) / 16,
        sw16(mix(c, t), l) == (3 * w16(c, l) + w16(t, l) + 8) / 16,
        (3 * w16(c, l) + w16(t, l) + 8) / 16 <= 255,
{
    hide(vsimd::spec::add_epi16); hide(vsimd::spec::srli_epi16); hide(vsimd::spec::set1_epi16); hide(w16); hide(sw16);
    let c2 = vsimd::spec::add_epi16(c, c);
    let c3 = vsimd::spec::add_epi16(c2, c);
    let s1 = vsimd::spec::add_epi16(c3, t);
    let k8 = vsimd::spec::set1_epi16(8);
    let s2 = vsimd::spec::add_epi16(s1, k8);
    lemma_len_add(c, c); lemma_len_add(c2, c); lemma_len_add(c3, t); lemma_len_set8(); lemma_len_add(s1, k8);
    lemma_w16_bounds(c, l);
    lemma_w16_bounds(t, l);
    lemma_add16_lane(c, c, l);
    lemma_add16_lane(c2, c, l);
    lemma_add16_lane(c3, t, l);
    lemma_set1_16_lane(8, l);
    lemma_add16_lane(s1, k8, l);
    vstd::arithmetic::power2::lemma2_to64();
    lemma_srli16_lane(s2, 4, l);
    let m = mix(c, t);
    lemma_len_srl4(s2);
    lemma_w16_bounds(m, l);
}

/// `3 * s[a + l] + s[b + l]` in 16-bit lane `l`, for eight lanes.
#[inline(always)]
fn tri8_x(cv: &[u8], a: usize, b: usize) -> (t: __m128i)
    requires a + 8 <= cv@.len(), b + 8 <= cv@.len(),
    ensures forall|l: int| 0 <= l < 8 ==> #[trigger] w16(v8(t), l) == 3 * cv@[a + l] + cv@[b + l] && w16(v8(t), l) <= 1020,
{
    let z = sx::setzero();
    let n = sx::unpacklo_epi8(sx::loadl(cv, a), z);
    let f = sx::unpacklo_epi8(sx::loadl(cv, b), z);
    let t = sx::add_epi16(sx::add_epi16(sx::add_epi16(n, n), n), f);
    proof {
        assert(v8(n) == zx(cv@, a as int) && v8(f) == zx(cv@, b as int));
        assert(v8(t) == tri(v8(n), v8(f)));
        assert forall|l: int| 0 <= l < 8 implies #[trigger] w16(v8(t), l) == 3 * cv@[a + l] + cv@[b + l] && w16(v8(t), l) <= 1020 by {
            lemma_zx_lane(cv@, a as int, l);
            lemma_zx_lane(cv@, b as int, l);
            lemma_tri_lane(v8(n), v8(f), l);
        }
    }
    t
}

/// `(3 * c + s + 8) >> 4` in each of eight lanes, a byte's value.
#[inline(always)]
fn mix8_x(c: __m128i, t: __m128i) -> (e: __m128i)
    requires forall|l: int| 0 <= l < 8 ==> #[trigger] w16(v8(c), l) <= 1020 && w16(v8(t), l) <= 1020,
    ensures forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(v8(e), l) == (3 * w16(v8(c), l) + w16(v8(t), l) + 8) / 16
        && 0 <= sw16(v8(e), l) <= 255,
{
    let e = sx::srli_epi16_4(sx::add_epi16(sx::add_epi16(sx::add_epi16(sx::add_epi16(c, c), c), t), sx::set1_epi16(8)));
    proof {
        assert(v8(e) == mix(v8(c), v8(t)));
        assert forall|l: int| 0 <= l < 8 implies #[trigger] sw16(v8(e), l) == (3 * w16(v8(c), l) + w16(v8(t), l) + 8) / 16
            && 0 <= sw16(v8(e), l) <= 255 by {
            lemma_mix_lane(v8(c), v8(t), l);
        }
    }
    e
}

/// Chroma columns `i .. i + 8` of a row upsampled: output byte `m` is
/// `fancy`'s value for output column `2i + m`, from the near row at `rn`
/// and the far row at `rf` (`rgb::vsb`); `far` is column `i + m/2 - 1` for
/// an even `m`, `i + m/2 + 1` for an odd one (no clamps away from the edges).
#[inline(always)]
pub fn chroma16_x(cv: &[u8], rn: usize, rf: usize, i: usize) -> (r: __m128i)
    requires 1 <= i, rn + i + 9 <= cv@.len(), rf + i + 9 <= cv@.len(),
    ensures
        forall|m: int| 0 <= m < 16 ==> #[trigger] v8(r)[m] as int ==
            (3 * vsb(cv@, rn as int, rf as int, i + m / 2)
                + vsb(cv@, rn as int, rf as int, if m % 2 == 0 { i + m / 2 - 1 } else { i + m / 2 + 1 }) + 8) / 16,
{
    let _n = cv.len();
    let tl = tri8_x(cv, rn + i - 1, rf + i - 1);
    let tc = tri8_x(cv, rn + i, rf + i);
    let tr = tri8_x(cv, rn + i + 1, rf + i + 1);
    let e = mix8_x(tc, tl);
    let o = mix8_x(tc, tr);
    let pe = sx::packus_epi16(e, e);
    let po = sx::packus_epi16(o, o);
    let r = sx::unpacklo_epi8(pe, po);
    proof {
        let s = cv@;
        assert forall|m: int| 0 <= m < 16 implies #[trigger] v8(r)[m] as int ==
            (3 * vsb(s, rn as int, rf as int, i + m / 2)
                + vsb(s, rn as int, rf as int, if m % 2 == 0 { i + m / 2 - 1 } else { i + m / 2 + 1 }) + 8) / 16 by {
            let l = m / 2;
            assert(w16(v8(tc), l) == vsb(s, rn as int, rf as int, i + l));
            assert(w16(v8(tl), l) == vsb(s, rn as int, rf as int, i + l - 1));
            assert(w16(v8(tr), l) == vsb(s, rn as int, rf as int, i + l + 1));
            assert(sw16(v8(e), l) >= 0 && sw16(v8(o), l) >= 0);
            assert(v8(pe)[l] as int == clamp(sw16(v8(e), l), 0, 255));
            assert(v8(po)[l] as int == clamp(sw16(v8(o), l), 0, 255));
        }
    }
    r
}

/// Eight pixels of row `y` from `x` on, written at `o`: `partial` moves on
/// by eight.
pub fn pixels8_x(out: &mut [u8], o: usize, mode: u8, f: &FrameX, alpha: &Option<Vec<u8>>, ur: &Vec<u8>, vr: &Vec<u8>,
    yrow: usize, x: usize, y: usize, stride: usize,
    Ghost(old_out): Ghost<Seq<u8>>, Ghost(p): Ghost<Pic>)
    requires
        mode == 1 || mode == 3 || mode == 4,
        p matches Pic::Lossy { f: fs, alpha: al } && f.is(fs) && pic_wf(p) && match (alpha, al) {
            (None, None) => true,
            (Some(v), Some(s)) => v@ == s,
            _ => false,
        },
        1 <= f.w <= 16384, 1 <= f.h <= 16384, y < f.h, x + 8 <= f.w, yrow == y * f.w,
        ur@.len() >= f.w, vr@.len() >= f.w,
        forall|xx: int| 0 <= xx < f.w ==> #[trigger] ur@[xx] == fancy(p->f.u, ((f.w + 1) / 2) as int, ((f.h + 1) / 2) as int, xx, y as int),
        forall|xx: int| 0 <= xx < f.w ==> #[trigger] vr@[xx] == fancy(p->f.v, ((f.w + 1) / 2) as int, ((f.h + 1) / 2) as int, xx, y as int),
        stride >= 1, stride >= f.w * 4, o == y * stride + x * 4, y * stride + f.w * 4 <= old(out)@.len(),
        old(out)@ == partial(old_out, stride as nat, f.w as nat, mode, p, y as int, x as int),
    ensures
        final(out)@ == partial(old_out, stride as nat, f.w as nat, mode, p, y as int, x + 8),
{
    let ghost fs = p->f;
    let ghost s0 = out@;
    let _n = out.len();
    let w = f.w;
    proof {
        lemma_idx(w as nat, f.h as nat, (x + 7) as int, y as int);
        assert(f.h * w == w * f.h && f.h * w <= 16384 * 16384) by (nonlinear_arith) requires f.h <= 16384, w <= 16384;
        assert(o + 32 <= y * stride + w * 4) by (nonlinear_arith) requires o == y * stride + x * 4, x + 8 <= w;
    }
    let yb = sx::loadl(f.y.as_slice(), yrow + x);
    let ub = sx::loadl(ur.as_slice(), x);
    let vb = sx::loadl(vr.as_slice(), x);
    let ab = match alpha { None => sx::set1_epi8(255), Some(av) => sx::loadl(av.as_slice(), yrow + x) };
    let (o1, o2) = rgba8_x(yb, ub, vb, ab, mode);
    sx::storeu_s(out, o, o1);
    sx::storeu_s(out, o + 16, o2);
    proof {
        let i0 = y * stride + x * 4;
        assert forall|j: int| 0 <= j < out@.len() implies #[trigger] out@[j] == if i0 <= j < i0 + 32 {
            out32((o1, o2), j - i0) } else { s0[j] } by {}
        assert forall|m: int| 0 <= m < 8 implies #[trigger] tup(v8(yb), v8(ub), v8(vb), v8(ab), m) == pic_px(p, x + m, y as int) by {
            lemma_idx(w as nat, f.h as nat, x + m, y as int);
            assert(v8(yb)[m] == f.y@[yrow + x + m]);
            assert(v8(ub)[m] == ur@[x + m]);
            assert(v8(vb)[m] == vr@[x + m]);
        }
        lemma_run(old_out, stride as nat, w as nat, mode, p, y as int, x as int, 8, s0, out@, (o1, o2));
    }
}

/// Writing `n` pixels' bytes from (x, y) on moves `partial` on by `n`.
proof fn lemma_run(old: Seq<u8>, stride: nat, w: nat, mode: u8, p: Pic, y: int, x: int, n: int,
    s: Seq<u8>, t: Seq<u8>, r: (__m128i, __m128i))
    requires
        mode == 1 || mode == 3 || mode == 4, stride >= 1, stride >= w * 4, 0 <= x, x + n <= w, 0 <= y, n == 8,
        s == partial(old, stride, w, mode, p, y, x), t.len() == s.len(),
        forall|i: int| 0 <= i < 32 ==> #[trigger] out32(r, i) == px_byte(mode, pic_px(p, x + i / 4, y), i % 4),
        forall|j: int| 0 <= j < t.len() ==> #[trigger] t[j] == if y * stride + x * 4 <= j < y * stride + x * 4 + 32 {
            out32(r, j - (y * stride + x * 4)) } else { s[j] },
    ensures t == partial(old, stride, w, mode, p, y, x + n),
{
    let st = stride as int;
    let b = bpp(mode) as int;
    assert(b == 4);
    let i0 = y * st + x * 4;
    let u = partial(old, stride, w, mode, p, y, x + n);
    assert forall|j: int| 0 <= j < old.len() implies t[j] == u[j] by {
        let rr = j / st;
        let c = j % st;
        lemma_fundamental_div_mod(j, st);
        if i0 <= j < i0 + 32 {
            let i = j - i0;
            assert(0 <= x * 4 + i < w * 4);
            lemma_fundamental_div_mod_converse(j, st, y, x * 4 + i);
            lemma_fundamental_div_mod_converse(x * 4 + i, 4, x + i / 4, i % 4);
        } else {
            if c < w * b && rr == y && x <= c / b < x + n {
                lemma_fundamental_div_mod(c, b);
                assert(4 * x <= c < 4 * x + 32);
                assert(st * rr == y * st) by (nonlinear_arith) requires rr == y;
                assert(false);
            }
            assert(c / b >= 0) by (nonlinear_arith) requires c >= 0, b >= 1;
        }
    }
    assert(t =~= u);
}

} // verus!
