//! RGB(A) output, as libwebp 1.6.0 produces it, verified.
//!
//! This is **libwebp's output convention**, not part of RFC 6386 or RFC
//! 9649: the RFCs define the decoded Y'CbCr planes (lossy) and ARGB pixels
//! (lossless), and say nothing of how a decoder turns 4:2:0 planes into RGB.
//! What real programs see is what libwebp's `WebPDecode` hands them in its
//! RGB modes with default options, and that is what `render` states:
//!
//! * Chroma upsampling is libwebp's "fancy" upsampler (`dsp/upsampling.c`,
//!   `UPSAMPLE_FUNC`, driven row pair by row pair by `EmitFancyRGB` in
//!   `dec/io_dec.c`), which in closed form is `fancy` below: the output
//!   pixel (x, y) weighs its own chroma sample (x/2, y/2) by 9, the
//!   horizontally and vertically nearest other samples by 3, and the
//!   diagonal one by 1, the neighbours clamped at the plane's edges.
//! * Y'CbCr to RGB is `dsp/yuv.h`'s 14-bit BT.601 fixed point
//!   (`VP8YUVToR/G/B`, `MultHi`, `VP8Clip8`): `yuv_r`, `yuv_g`, `yuv_b`.
//! * Alpha is the ALPH chunk's plane, copied (255 without one); lossless
//!   pixels are only reordered.
//! * The premultiplied modes (`MODE_rgbA`, `MODE_bgrA`, `MODE_Argb`) scale
//!   each color by alpha as `WebPApplyAlphaMultiply` does: `(c * a *
//!   32897) >> 23`, which is floor(c * a / 255).
//! * Modes and their byte orders are `WEBP_CSP_MODE`'s: 0 RGB, 1 RGBA,
//!   2 BGR, 3 BGRA, 4 ARGB, 7 rgbA, 8 bgrA, 9 Argb (not the 16-bit ones).
//!
//! The pixels land in a caller's buffer of rows `stride` bytes apart, as
//! `WebPDecode` writes them; the bytes between rows are left alone
//! (`render`).
//!
//! The closed form of the upsampler was derived from the C by hand and is
//! checked against libwebp bit for bit by bench/webp/e2e (every Kodak and
//! photo image, and the lossy+alpha and lossless test files).
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
use crate::vp8::spec::{Frame, Plane};
use crate::vp8::dec::FrameX;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::vp8::plane::{holds, lemma_idx};
use crate::spec::Image;
use crate::dec::ImageX;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::dec::image_view;

verus! {

// ---------------------------------------------------------------------------
// The spec: libwebp's output convention.

/// `MultHi(v, coeff)` of `dsp/yuv.h`: `(v * coeff) >> 8`.
pub open spec fn mult_hi(v: int, k: int) -> int { (v * k) / 256 }

/// `VP8Clip8`: `((v & ~16383) == 0) ? (v >> 6) : (v < 0) ? 0 : 255`
/// (`lemma_clip8_c`).
pub open spec fn clip8(v: int) -> u8 {
    if v < 0 { 0 } else if v >= 16384 { 255 } else { (v / 64) as u8 }
}

/// `VP8YUVToR`.
pub open spec fn yuv_r(y: u8, v: u8) -> u8 {
    clip8(mult_hi(y as int, 19077) + mult_hi(v as int, 26149) - 14234)
}

/// `VP8YUVToG`.
pub open spec fn yuv_g(y: u8, u: u8, v: u8) -> u8 {
    clip8(mult_hi(y as int, 19077) - mult_hi(u as int, 6419) - mult_hi(v as int, 13320) + 8708)
}

/// `VP8YUVToB`.
pub open spec fn yuv_b(y: u8, u: u8) -> u8 {
    clip8(mult_hi(y as int, 19077) + mult_hi(u as int, 33050) - 17685)
}

/// The chroma sample farther from output coordinate `i` (of `n` samples):
/// the next one for an odd `i`, the previous one for an even `i`, clamped
/// to the plane.
pub open spec fn far(i: int, n: int) -> int {
    let f = if i % 2 == 1 { i / 2 + 1 } else { i / 2 - 1 };
    if f < 0 { 0 } else if f >= n { n - 1 } else { f }
}

/// libwebp's fancy upsampler, in closed form: chroma plane `c` (`cw` x
/// `ch`) at output pixel (x, y).
pub open spec fn fancy(c: Plane, cw: int, ch: int, x: int, y: int) -> u8 {
    let nx = x / 2;
    let ny = y / 2;
    let fx = far(x, cw);
    let fy = far(y, ch);
    ((9 * c[ny][nx] + 3 * c[ny][fx] + 3 * c[fy][nx] + c[fy][fx] + 8) / 16) as u8
}

/// A decoded image, before output.
pub enum Pic {
    /// A VP8 frame, and the ALPH chunk's plane if any.
    Lossy { f: Frame, alpha: Option<Seq<u8>> },
    /// A VP8L image (ARGB).
    Lossless { img: Image },
}

pub open spec fn pic_w(p: Pic) -> nat { match p { Pic::Lossy { f, .. } => f.w, Pic::Lossless { img } => img.w } }
pub open spec fn pic_h(p: Pic) -> nat { match p { Pic::Lossy { f, .. } => f.h, Pic::Lossless { img } => img.h } }

/// Pixel (x, y) of a lossy image: (R, G, B, A).
pub open spec fn lossy_px(f: Frame, alpha: Option<Seq<u8>>, x: int, y: int) -> (u8, u8, u8, u8) {
    let cw = ((f.w + 1) / 2) as int;
    let ch = ((f.h + 1) / 2) as int;
    let yy = f.y[y][x];
    let u = fancy(f.u, cw, ch, x, y);
    let v = fancy(f.v, cw, ch, x, y);
    let a = match alpha { None => 255u8, Some(s) => s[y * f.w + x] };
    (yuv_r(yy, v), yuv_g(yy, u, v), yuv_b(yy, u), a)
}

/// An ARGB pixel as (R, G, B, A).
pub open spec fn argb_px(c: u32) -> (u8, u8, u8, u8) {
    (((c >> 16u32) & 0xffu32) as u8, ((c >> 8u32) & 0xffu32) as u8, (c & 0xffu32) as u8, (c >> 24u32) as u8)
}

/// Pixel (x, y): (R, G, B, A), not premultiplied.
pub open spec fn pic_px(p: Pic, x: int, y: int) -> (u8, u8, u8, u8) {
    match p {
        Pic::Lossy { f, alpha } => lossy_px(f, alpha, x, y),
        Pic::Lossless { img } => argb_px(img.px[y * img.w + x]),
    }
}

/// The modes: `WEBP_CSP_MODE`'s RGB ones of 3 and 4 bytes a pixel.
pub open spec fn mode_ok(mode: u8) -> bool { mode <= 4 || (7 <= mode && mode <= 9) }

/// Bytes per pixel.
pub open spec fn bpp(mode: u8) -> nat { if mode == 0 || mode == 2 { 3 } else { 4 } }

/// `MODE_rgbA`, `MODE_bgrA`, `MODE_Argb`.
pub open spec fn premultiplied(mode: u8) -> bool { 7 <= mode && mode <= 9 }

/// `WebPApplyAlphaMultiply`'s `PREMULTIPLY(c, MULTIPLIER(a))`.
pub open spec fn premul(c: u8, a: u8) -> u8 { ((c as int * (a as int * 32897)) / 0x80_0000) as u8 }

/// Byte `k` of a pixel (R, G, B, A) in `mode`.
pub open spec fn px_byte(mode: u8, p: (u8, u8, u8, u8), k: int) -> u8 {
    let a = p.3;
    let r = if premultiplied(mode) { premul(p.0, a) } else { p.0 };
    let g = if premultiplied(mode) { premul(p.1, a) } else { p.1 };
    let b = if premultiplied(mode) { premul(p.2, a) } else { p.2 };
    if mode == 0 { if k == 0 { r } else if k == 1 { g } else { b } }
    else if mode == 1 || mode == 7 { if k == 0 { r } else if k == 1 { g } else if k == 2 { b } else { a } }
    else if mode == 2 { if k == 0 { b } else if k == 1 { g } else { r } }
    else if mode == 3 || mode == 8 { if k == 0 { b } else if k == 1 { g } else if k == 2 { r } else { a } }
    else { if k == 0 { a } else if k == 1 { r } else if k == 2 { g } else { b } }
}

/// The buffer `old` after the image is written into it in `mode`, rows
/// `stride` bytes apart: byte `k` of pixel (x, y) at `y * stride + x *
/// bpp + k`, every other byte as it was.
pub open spec fn render(old: Seq<u8>, stride: nat, mode: u8, p: Pic) -> Seq<u8> {
    Seq::new(old.len(), |j: int| {
        let r = j / stride as int;
        let c = j % stride as int;
        let b = bpp(mode) as int;
        if r < pic_h(p) && c < pic_w(p) * b { px_byte(mode, pic_px(p, c / b, r), c % b) } else { old[j] }
    })
}

/// A buffer of `len` bytes holds `h` rows of `w` pixels, `stride` apart
/// (libwebp's `CheckDecBuffer`: `stride >= w * bpp`, `size >= stride *
/// (h - 1) + w * bpp`).
pub open spec fn fits(len: nat, stride: nat, w: nat, h: nat, mode: u8) -> bool {
    &&& stride >= 1 && stride >= w * bpp(mode)
    &&& h == 0 || (h - 1) * stride + w * bpp(mode) <= len
}

/// `clip8` is `VP8Clip8`'s text.
pub proof fn lemma_clip8_c(v: i32)
    ensures clip8(v as int) == if (v & !16383i32) == 0 { (v >> 6u32) as u8 } else if v < 0 { 0u8 } else { 255u8 },
{
    assert((v & !16383i32) == 0 <==> (0 <= v && v < 16384)) by (bit_vector);
    if 0 <= v && v < 16384 {
        assert(v >> 6u32 == v / 64) by (bit_vector) requires 0 <= v && v < 16384;
    }
}

// ---------------------------------------------------------------------------
// Writing pixel by pixel.

/// `render` after the pixels before (x, y) in scan order.
pub open spec fn partial(old: Seq<u8>, stride: nat, w: nat, mode: u8, p: Pic, yy: int, xx: int) -> Seq<u8> {
    Seq::new(old.len(), |j: int| {
        let r = j / stride as int;
        let c = j % stride as int;
        let b = bpp(mode) as int;
        if c < w * b && (r < yy || (r == yy && c / b < xx)) { px_byte(mode, pic_px(p, c / b, r), c % b) } else { old[j] }
    })
}

/// `s` with pixel `p` written at `i`.
pub open spec fn put(s: Seq<u8>, i: int, mode: u8, p: (u8, u8, u8, u8)) -> Seq<u8> {
    Seq::new(s.len(), |j: int| if i <= j < i + bpp(mode) { px_byte(mode, p, j - i) } else { s[j] })
}

proof fn lemma_start(old: Seq<u8>, stride: nat, w: nat, mode: u8, p: Pic)
    requires stride >= 1,
    ensures partial(old, stride, w, mode, p, 0, 0) == old,
{
    let s = partial(old, stride, w, mode, p, 0, 0);
    assert forall|j: int| 0 <= j < old.len() implies s[j] == old[j] by {
        lemma_fundamental_div_mod(j, stride as int);
        let c = j % stride as int;
        let b = bpp(mode) as int;
        assert(j / stride as int >= 0) by (nonlinear_arith) requires j >= 0, stride >= 1;
        assert(c / b >= 0) by (nonlinear_arith) requires c >= 0, b >= 1;
    }
    assert(s =~= old);
}

proof fn lemma_row(old: Seq<u8>, stride: nat, w: nat, mode: u8, p: Pic, y: int)
    requires stride >= 1,
    ensures partial(old, stride, w, mode, p, y, w as int) == partial(old, stride, w, mode, p, y + 1, 0),
{
    let s = partial(old, stride, w, mode, p, y, w as int);
    let t = partial(old, stride, w, mode, p, y + 1, 0);
    assert forall|j: int| 0 <= j < old.len() implies s[j] == t[j] by {
        let c = j % stride as int;
        let b = bpp(mode) as int;
        lemma_fundamental_div_mod(j, stride as int);
        lemma_fundamental_div_mod(c, b);
        assert(c / b >= 0) by (nonlinear_arith) requires c >= 0, b >= 1;
        if c < w * b {
            assert(c / b < w) by (nonlinear_arith) requires c < w * b, c == b * (c / b) + c % b, c % b >= 0, b >= 1;
        }
    }
    assert(s =~= t);
}

proof fn lemma_end(old: Seq<u8>, stride: nat, mode: u8, p: Pic)
    requires stride >= 1,
    ensures partial(old, stride, pic_w(p), mode, p, pic_h(p) as int, 0) == render(old, stride, mode, p),
{
    let s = partial(old, stride, pic_w(p), mode, p, pic_h(p) as int, 0);
    let t = render(old, stride, mode, p);
    assert forall|j: int| 0 <= j < old.len() implies s[j] == t[j] by {
        let c = j % stride as int;
        let b = bpp(mode) as int;
        lemma_fundamental_div_mod(j, stride as int);
        assert(c / b >= 0) by (nonlinear_arith) requires c >= 0, b >= 1;
    }
    assert(s =~= t);
}

/// Writing pixel (x, y) moves `partial` on by one.
proof fn lemma_step(old: Seq<u8>, stride: nat, w: nat, mode: u8, p: Pic, y: int, x: int)
    requires stride >= 1, stride >= w * bpp(mode), 0 <= x < w, 0 <= y,
    ensures
        put(partial(old, stride, w, mode, p, y, x), y * stride + x * bpp(mode), mode, pic_px(p, x, y))
            == partial(old, stride, w, mode, p, y, x + 1),
{
    let b = bpp(mode) as int;
    let st = stride as int;
    let i0 = y * st + x * b;
    let s = partial(old, stride, w, mode, p, y, x);
    let lhs = put(s, i0, mode, pic_px(p, x, y));
    let rhs = partial(old, stride, w, mode, p, y, x + 1);
    assert forall|j: int| 0 <= j < old.len() implies lhs[j] == rhs[j] by {
        let r = j / st;
        let c = j % st;
        lemma_fundamental_div_mod(j, st);
        if i0 <= j < i0 + b {
            let k = j - i0;
            assert(0 <= x * b + k < w * b) by (nonlinear_arith) requires 0 <= x < w, 0 <= k < b;
            assert(j == y * st + (x * b + k));
            lemma_fundamental_div_mod_converse(j, st, y, x * b + k);
            lemma_fundamental_div_mod_converse(x * b + k, b, x, k);
        } else {
            if c < w * b && r == y && c / b == x {
                lemma_fundamental_div_mod(c, b);
                assert(j == y * st + x * b + c % b) by (nonlinear_arith)
                    requires j == st * r + c, r == y, c == b * (c / b) + c % b, c / b == x;
                assert(false);
            }
            assert(c / b >= 0) by (nonlinear_arith) requires c >= 0, b >= 1;
        }
    }
    assert(lhs =~= rhs);
}

// ---------------------------------------------------------------------------
// The implementation.

#[inline(always)]
fn clip8_x(v: i32) -> (r: u8)
    ensures r == clip8(v as int),
{
    if v < 0 { 0 } else if v >= 16384 { 255 } else {
        proof { assert((v as u32) >> 6u32 == (v as u32) / 64) by (bit_vector); }
        ((v as u32) >> 6u32) as u8
    }
}

/// `VP8YuvToRgb`.
#[inline(always)]
fn yuv_x(y: u8, u: u8, v: u8) -> (r: (u8, u8, u8))
    ensures r == (yuv_r(y, v), yuv_g(y, u, v), yuv_b(y, u)),
{
    let yy = ((y as u32 * 19077) / 256) as i32;
    let ur = ((u as u32 * 6419) / 256) as i32;
    let ub = ((u as u32 * 33050) / 256) as i32;
    let vr = ((v as u32 * 26149) / 256) as i32;
    let vg = ((v as u32 * 13320) / 256) as i32;
    (clip8_x(yy + vr - 14234), clip8_x(yy - ur - vg + 8708), clip8_x(yy + ub - 17685))
}

#[inline(always)]
fn argb_x(c: u32) -> (r: (u8, u8, u8, u8))
    ensures r == argb_px(c),
{
    proof {
        assert((c >> 16u32) & 0xffu32 <= 255 && (c >> 8u32) & 0xffu32 <= 255 && c & 0xffu32 <= 255 && c >> 24u32 <= 255) by (bit_vector);
    }
    (((c >> 16u32) & 0xffu32) as u8, ((c >> 8u32) & 0xffu32) as u8, (c & 0xffu32) as u8, (c >> 24u32) as u8)
}

#[inline(always)]
fn premul_x(c: u8, a: u8) -> (r: u8)
    ensures r == premul(c, a),
{
    proof {
        assert(c as int * (a as int * 32897) <= 255 * (255 * 32897)) by (nonlinear_arith) requires c <= 255, a <= 255;
    }
    ((c as u32 * (a as u32 * 32897)) / 0x80_0000) as u8
}

/// Write pixel (R, G, B, A) at `out[i..]` in `mode`.
#[inline(always)]
fn put_px(out: &mut [u8], i: usize, mode: u8, p: (u8, u8, u8, u8))
    requires mode_ok(mode), i + bpp(mode) <= old(out)@.len(),
    ensures final(out)@ == put(old(out)@, i as int, mode, p),
{
    let ghost o = out@;
    let _n = out.len();
    let (r0, g0, b0, a) = p;
    let pm = mode >= 7;
    let r = if pm { premul_x(r0, a) } else { r0 };
    let g = if pm { premul_x(g0, a) } else { g0 };
    let b = if pm { premul_x(b0, a) } else { b0 };
    if mode == 1 || mode == 7 {
        vsimd::mem::sset(out, i, r); vsimd::mem::sset(out, i + 1, g); vsimd::mem::sset(out, i + 2, b); vsimd::mem::sset(out, i + 3, a);
    } else if mode == 3 || mode == 8 {
        vsimd::mem::sset(out, i, b); vsimd::mem::sset(out, i + 1, g); vsimd::mem::sset(out, i + 2, r); vsimd::mem::sset(out, i + 3, a);
    } else if mode == 4 || mode == 9 {
        vsimd::mem::sset(out, i, a); vsimd::mem::sset(out, i + 1, r); vsimd::mem::sset(out, i + 2, g); vsimd::mem::sset(out, i + 3, b);
    } else if mode == 0 {
        vsimd::mem::sset(out, i, r); vsimd::mem::sset(out, i + 1, g); vsimd::mem::sset(out, i + 2, b);
    } else {
        vsimd::mem::sset(out, i, b); vsimd::mem::sset(out, i + 1, g); vsimd::mem::sset(out, i + 2, r);
    }
    proof { assert(out@ =~= put(o, i as int, mode, p)); }
}

/// The frame's planes are the sizes `vp8` gives them.
pub open spec fn frame_wf(f: Frame) -> bool {
    &&& f.y.len() == f.h && f.u.len() == (f.h + 1) / 2 && f.v.len() == (f.h + 1) / 2
}

/// `pic`'s sizes agree.
pub open spec fn pic_wf(p: Pic) -> bool {
    match p {
        Pic::Lossy { f, alpha } => frame_wf(f) && f.w <= 16384 && f.h <= 16384 && match alpha {
            None => true,
            Some(a) => a.len() == f.w * f.h,
        },
        Pic::Lossless { img } => img.px.len() == img.w * img.h && img.w <= 16384 && img.h <= 16384,
    }
}

/// `far`, for `i < 2n`.
#[inline(always)]
fn far_x(i: usize, n: usize) -> (r: usize)
    requires 1 <= n, i < 2 * n,
    ensures r == far(i as int, n as int), r < n,
{
    if i % 2 == 1 {
        if i / 2 + 1 >= n { n - 1 } else { i / 2 + 1 }
    } else {
        if i == 0 { 0 } else { i / 2 - 1 }
    }
}

/// `3 * near + far`: the vertical half of `fancy`, for column `k`.
pub open spec fn vsum(c: Plane, ch: int, y: int, k: int) -> int {
    3 * c[y / 2][k] + c[far(y, ch)][k]
}

/// `3 * near + far` at column `k`, from the plane's buffer: rows start at
/// `rn` (near) and `rf` (far).
pub open spec fn vsb(cv: Seq<u8>, rn: int, rf: int, k: int) -> int { 3 * cv[rn + k] + cv[rf + k] }

#[inline(always)]
fn vs_x(cv: &Vec<u8>, rn: usize, rf: usize, k: usize) -> (r: u16)
    requires rn + k < cv@.len(), rf + k < cv@.len(),
    ensures r == vsb(cv@, rn as int, rf as int, k as int), r <= 1020,
{
    let _n = cv.len();
    3 * vsimd::mem::get(cv.as_slice(), rn + k) as u16 + vsimd::mem::get(cv.as_slice(), rf + k) as u16
}

/// Row `y` of chroma plane `c` (`cw` x `ch`, in `cv`) upsampled:
/// `r[x] == fancy(c, cw, ch, x, y)`. The vertical pass (3 * near + far) and
/// the horizontal one together, sixteen outputs at a time in SSE2
/// (`rgbx::chroma16_x`) away from the plane's edges.
fn chroma_row_x(cv: &Vec<u8>, cw: usize, ch: usize, y: usize, r: &mut Vec<u8>, Ghost(c): Ghost<Plane>)
    requires
        holds(cv@, cw as nat, c), c.len() == ch, 1 <= cw <= 8192, 1 <= ch <= 8192, y < 2 * ch,
        old(r)@.len() == 2 * cw,
    ensures
        final(r)@.len() == 2 * cw,
        forall|x: int| 0 <= x < 2 * cw ==> #[trigger] final(r)@[x] == fancy(c, cw as int, ch as int, x, y as int),
{
    let ny = y / 2;
    let fy = far_x(y, ch);
    proof {
        assert(ch * cw <= 8192 * 8192) by (nonlinear_arith) requires ch <= 8192, cw <= 8192;
        lemma_idx(cw as nat, ch as nat, 0, ny as int);
        lemma_idx(cw as nat, ch as nat, 0, fy as int);
        assert(ch * cw == cw * ch) by (nonlinear_arith);
    }
    let rn = ny * cw;
    let rf = fy * cw;
    proof {
        lemma_idx(cw as nat, ch as nat, (cw - 1) as int, ny as int);
        lemma_idx(cw as nat, ch as nat, (cw - 1) as int, fy as int);
        // vsb over the buffer is vsum over the plane.
        assert forall|k: int| 0 <= k < cw implies #[trigger] vsb(cv@, rn as int, rf as int, k) == vsum(c, ch as int, y as int, k) by {
            lemma_idx(cw as nat, ch as nat, k, ny as int);
            lemma_idx(cw as nat, ch as nat, k, fy as int);
        }
    }
    #[cfg(target_arch = "x86_64")]
    let simd = true;
    #[cfg(not(target_arch = "x86_64"))]
    let simd = false;
    let mut i: usize = 0;
    while i < cw
        invariant
            1 <= cw <= 8192, 1 <= ch <= 8192, y < 2 * ch, r@.len() == 2 * cw, i <= cw, c.len() == ch,
            rn + cw <= cv@.len(), rf + cw <= cv@.len(),
            forall|k: int| 0 <= k < cw ==> #[trigger] vsb(cv@, rn as int, rf as int, k) == vsum(c, ch as int, y as int, k),
            forall|x: int| 0 <= x < 2 * i ==> #[trigger] r@[x] == fancy(c, cw as int, ch as int, x, y as int),
        decreases cw - i,
    {
        let ghost r0 = r@;
        let ghost (ii, yy, cwi, chi) = (i as int, y as int, cw as int, ch as int);
        if simd && i >= 1 && i + 9 <= cw {
            #[cfg(target_arch = "x86_64")]
            {
                let v = crate::rgbx::chroma16_x(cv.as_slice(), rn, rf, i);
                vsimd::x86::storeu(r, 2 * i, v);
                proof {
                    assert forall|x: int| 0 <= x < 2 * (i + 8) implies #[trigger] r@[x] == fancy(c, cwi, chi, x, yy) by {
                        if x < 2 * ii {
                            assert(r@[x] == r0[x]);
                        } else {
                            let m = x - 2 * ii;
                            let k = ii + m / 2;
                            assert(r@[x] == vsimd::x86::v8(v)[m]);
                            assert(x / 2 == k && (x % 2 == 0 <==> m % 2 == 0));
                            assert(far(x, cwi) == if m % 2 == 0 { k - 1 } else { k + 1 });
                            assert(vsb(cv@, rn as int, rf as int, k) == vsum(c, chi, yy, k));
                            assert(vsb(cv@, rn as int, rf as int, far(x, cwi)) == vsum(c, chi, yy, far(x, cwi)));
                        }
                    }
                }
            }
            i = i + 8;
        } else {
            let il = if i == 0 { 0 } else { i - 1 };
            let ir = if i + 1 >= cw { cw - 1 } else { i + 1 };
            let tc = vs_x(cv, rn, rf, i);
            let tl = vs_x(cv, rn, rf, il);
            let tr = vs_x(cv, rn, rf, ir);
            let c3 = 3 * tc;
            let e = ((c3 + tl + 8) / 16) as u8;
            let o = ((c3 + tr + 8) / 16) as u8;
            vsimd::mem::vset(r, 2 * i, e);
            vsimd::mem::vset(r, 2 * i + 1, o);
            proof {
                assert((2 * ii) / 2 == ii && (2 * ii) % 2 == 0 && (2 * ii + 1) / 2 == ii && (2 * ii + 1) % 2 == 1);
                assert(far(2 * ii, cwi) == il);
                assert(far(2 * ii + 1, cwi) == ir);
                assert(tc == vsum(c, chi, yy, ii));
                assert(tl == vsum(c, chi, yy, il as int));
                assert(tr == vsum(c, chi, yy, ir as int));
                assert(e == fancy(c, cwi, chi, 2 * ii, yy));
                assert(o == fancy(c, cwi, chi, 2 * ii + 1, yy));
                assert forall|x: int| 0 <= x < 2 * (i + 1) implies #[trigger] r@[x] == fancy(c, cwi, chi, x, yy) by {
                    if x < 2 * ii { assert(r@[x] == r0[x]); }
                }
            }
            i = i + 1;
        }
    }
}

/// Render a lossy frame.
fn render_lossy_x(out: &mut [u8], stride: usize, mode: u8, f: &FrameX, alpha: &Option<Vec<u8>>,
    Ghost(p): Ghost<Pic>)
    requires
        mode_ok(mode),
        p matches Pic::Lossy { f: fs, alpha: al } && f.is(fs) && pic_wf(p) && match (alpha, al) {
            (None, None) => true,
            (Some(v), Some(s)) => v@ == s,
            _ => false,
        },
        fits(old(out)@.len(), stride as nat, pic_w(p), pic_h(p), mode),
    ensures final(out)@ == render(old(out)@, stride as nat, mode, p),
{
    let ghost old_out = out@;
    let n_out = out.len();
    let ghost fs = p->f;
    let ghost al = p->alpha;
    let w = f.w;
    let h = f.h;
    let b: usize = if mode == 0 || mode == 2 { 3 } else { 4 };
    proof {
        lemma_start(old_out, stride as nat, w as nat, mode, p);
        assert(w * b <= 16384 * 4) by (nonlinear_arith) requires w <= 16384, b <= 4;
    }
    if w == 0 || h == 0 {
        proof {
            lemma_end(old_out, stride as nat, mode, p);
            let s = partial(old_out, stride as nat, w as nat, mode, p, h as int, 0);
            let s0 = partial(old_out, stride as nat, w as nat, mode, p, 0, 0);
            if h == 0 { assert(s == s0); } else {
                assert forall|j: int| 0 <= j < old_out.len() implies s[j] == old_out[j] by {
                    lemma_fundamental_div_mod(j, stride as int);
                }
                assert(s =~= old_out);
            }
        }
        return;
    }
    let cw = (w + 1) / 2;
    let ch = (h + 1) / 2;
    let mut ur: Vec<u8> = vec![0u8; 2 * cw];
    let mut vr: Vec<u8> = vec![0u8; 2 * cw];
    // Eight pixels at a time in SSE2 for RGBA, BGRA and ARGB (`rgbx`).
    #[cfg(target_arch = "x86_64")]
    let simd = mode == 1 || mode == 3 || mode == 4;
    #[cfg(not(target_arch = "x86_64"))]
    let simd = false;
    let mut y: usize = 0;
    while y < h
        invariant
            simd ==> (mode == 1 || mode == 3 || mode == 4), stride >= 1,
            mode_ok(mode), b == bpp(mode), 1 <= w <= 16384, 1 <= h <= 16384, cw == (w + 1) / 2, ch == (h + 1) / 2,
            p == (Pic::Lossy { f: fs, alpha: al }), f.is(fs), pic_wf(p), w == f.w, h == f.h, fs.w == w, fs.h == h,
            match (alpha, al) { (None, None) => true, (Some(v), Some(s)) => v@ == s, _ => false },
            fits(old_out.len(), stride as nat, w as nat, h as nat, mode), out@.len() == old_out.len(), n_out == old_out.len(),
            ur@.len() == 2 * cw, vr@.len() == 2 * cw,
            y <= h,
            out@ == partial(old_out, stride as nat, w as nat, mode, p, y as int, 0),
        decreases h - y,
    {
        chroma_row_x(&f.u, cw, ch, y, &mut ur, Ghost(fs.u));
        chroma_row_x(&f.v, cw, ch, y, &mut vr, Ghost(fs.v));
        proof {
            assert(y * stride + w * b <= old_out.len()) by (nonlinear_arith)
                requires y < h, (h - 1) * stride + w * b <= old_out.len(), y >= 0, stride >= 0;
            assert(y * w < 16384 * 16384) by (nonlinear_arith) requires y < h, h <= 16384, w <= 16384;
            assert(y * stride <= (h - 1) * stride) by (nonlinear_arith) requires y < h, stride >= 0;
            assert(h * w == w * h && h * w <= 16384 * 16384) by (nonlinear_arith) requires h <= 16384, w <= 16384;
        }
        let yrow = y * w;
        let orow = y * stride;
        let mut x: usize = 0;
        let mut o: usize = orow;
        while x < w
            invariant
                simd ==> (mode == 1 || mode == 3 || mode == 4), stride >= 1,
                mode_ok(mode), b == bpp(mode), 1 <= w <= 16384, 1 <= h <= 16384, cw == (w + 1) / 2, ch == (h + 1) / 2, y < h,
                p == (Pic::Lossy { f: fs, alpha: al }), f.is(fs), pic_wf(p), fs.w == w, fs.h == h,
                match (alpha, al) { (None, None) => true, (Some(v), Some(s)) => v@ == s, _ => false },
                fits(old_out.len(), stride as nat, w as nat, h as nat, mode), out@.len() == old_out.len(), n_out == old_out.len(),
                orow == y * stride, orow + w * b <= old_out.len(), yrow == y * w, h * w <= 16384 * 16384,
                ur@.len() == 2 * cw, vr@.len() == 2 * cw,
                forall|xx: int| 0 <= xx < 2 * cw ==> #[trigger] ur@[xx] == fancy(fs.u, cw as int, ch as int, xx, y as int),
                forall|xx: int| 0 <= xx < 2 * cw ==> #[trigger] vr@[xx] == fancy(fs.v, cw as int, ch as int, xx, y as int),
                x <= w, o == orow + x * b,
                out@ == partial(old_out, stride as nat, w as nat, mode, p, y as int, x as int),
            decreases w - x,
        {
          if simd && x + 8 <= w {
            proof {
                assert(o + 32 <= orow + w * b) by (nonlinear_arith) requires o == orow + x * b, x + 8 <= w, b == 4;
            }
            #[cfg(target_arch = "x86_64")]
            crate::rgbx::pixels8_x(out, o, mode, f, alpha, &ur, &vr, yrow, x, y, stride, Ghost(old_out), Ghost(p));
            x = x + 8;
            o = o + 32;
          } else {
            proof {
                lemma_idx(w as nat, h as nat, x as int, y as int);
                assert(h * w == w * h) by (nonlinear_arith);
            }
            let i = yrow + x;
            let yv = vsimd::mem::get(f.y.as_slice(), i);
            let u = vsimd::mem::get(ur.as_slice(), x);
            let v = vsimd::mem::get(vr.as_slice(), x);
            let a = match alpha { None => 255u8, Some(av) => vsimd::mem::get(av.as_slice(), i) };
            let (r, g, bl) = yuv_x(yv, u, v);
            proof {
                assert((r, g, bl, a) == pic_px(p, x as int, y as int));
                lemma_step(old_out, stride as nat, w as nat, mode, p, y as int, x as int);
                assert(o + b <= orow + w * b) by (nonlinear_arith) requires o == orow + x * b, x < w;
            }
            put_px(out, o, mode, (r, g, bl, a));
            x = x + 1;
            o = o + b;
          }
        }
        proof { lemma_row(old_out, stride as nat, w as nat, mode, p, y as int); }
        y = y + 1;
    }
    proof { lemma_end(old_out, stride as nat, mode, p); }
}

/// Render a lossless image.
fn render_lossless_x(out: &mut [u8], stride: usize, mode: u8, img: &ImageX, Ghost(p): Ghost<Pic>)
    requires
        mode_ok(mode),
        p == (Pic::Lossless { img: image_view(img) }), pic_wf(p),
        fits(old(out)@.len(), stride as nat, pic_w(p), pic_h(p), mode),
    ensures final(out)@ == render(old(out)@, stride as nat, mode, p),
{
    let ghost old_out = out@;
    let n_out = out.len();
    let w = img.w;
    let h = img.h;
    let b: usize = if mode == 0 || mode == 2 { 3 } else { 4 };
    proof {
        lemma_start(old_out, stride as nat, w as nat, mode, p);
        assert(w * b <= 16384 * 4) by (nonlinear_arith) requires w <= 16384, b <= 4;
    }
    let mut y: usize = 0;
    while y < h
        invariant
            mode_ok(mode), b == bpp(mode), w <= 16384, h <= 16384, w == img.w, h == img.h,
            p == (Pic::Lossless { img: image_view(img) }), pic_wf(p),
            fits(old_out.len(), stride as nat, w as nat, h as nat, mode), out@.len() == old_out.len(), n_out == old_out.len(),
            y <= h,
            out@ == partial(old_out, stride as nat, w as nat, mode, p, y as int, 0),
        decreases h - y,
    {
        proof {
            assert(y * stride + w * b <= old_out.len()) by (nonlinear_arith)
                requires y < h, (h - 1) * stride + w * b <= old_out.len(), y >= 0, stride >= 0;
        }
        proof {
            assert(y * w < 16384 * 16384) by (nonlinear_arith) requires y < h, h <= 16384, w <= 16384;
            assert(y * stride <= (h - 1) * stride) by (nonlinear_arith) requires y < h, stride >= 0;
        }
        let yrow = y * w;
        let orow = y * stride;
        let mut x: usize = 0;
        let mut o: usize = orow;
        while x < w
            invariant
                mode_ok(mode), b == bpp(mode), w <= 16384, h <= 16384, w == img.w, h == img.h, y < h,
                p == (Pic::Lossless { img: image_view(img) }), pic_wf(p),
                fits(old_out.len(), stride as nat, w as nat, h as nat, mode), out@.len() == old_out.len(), n_out == old_out.len(),
                orow == y * stride, orow + w * b <= old_out.len(), yrow == y * w,
                x <= w, o == orow + x * b,
                out@ == partial(old_out, stride as nat, w as nat, mode, p, y as int, x as int),
            decreases w - x,
        {
            proof {
                lemma_idx(w as nat, h as nat, x as int, y as int);
                assert(h * w == w * h && h * w <= 16384 * 16384) by (nonlinear_arith) requires h <= 16384, w <= 16384;
            }
            let c = vsimd::mem::get(img.px.as_slice(), yrow + x);
            let px = argb_x(c);
            proof {
                lemma_step(old_out, stride as nat, w as nat, mode, p, y as int, x as int);
                assert(o + b <= orow + w * b) by (nonlinear_arith) requires o == orow + x * b, x < w;
            }
            if mode == 1 {
                // RGBA: the ARGB word with its bytes 0 and 2 swapped, one store.
                let sw = (c & 0xff00ff00u32) | ((c >> 16u32) & 0xffu32) | ((c & 0xffu32) << 16u32);
                let ghost o0 = out@;
                vsimd::mem::sset_u32le(out, o, sw);
                proof {
                    let (p0, p1, p2, p3) = px;
                    assert(((sw >> 0u32) & 0xffu32) as u8 == p0 && ((sw >> 8u32) & 0xffu32) as u8 == p1
                        && ((sw >> 16u32) & 0xffu32) as u8 == p2 && ((sw >> 24u32) & 0xffu32) as u8 == p3) by (bit_vector)
                        requires sw == (c & 0xff00ff00u32) | ((c >> 16u32) & 0xffu32) | ((c & 0xffu32) << 16u32),
                            p0 == ((c >> 16u32) & 0xffu32) as u8, p1 == ((c >> 8u32) & 0xffu32) as u8,
                            p2 == (c & 0xffu32) as u8, p3 == (c >> 24u32) as u8;
                    assert forall|j: int| 0 <= j < o0.len() implies #[trigger] out@[j] == put(o0, o as int, mode, px)[j] by {
                        if o <= j < o + 4 {
                            let k = j - o;
                            if k == 0 { assert((8 * k) as u32 == 0u32); }
                            else if k == 1 { assert((8 * k) as u32 == 8u32); }
                            else if k == 2 { assert((8 * k) as u32 == 16u32); }
                            else { assert((8 * k) as u32 == 24u32); }
                        }
                    }
                    assert(out@ =~= put(o0, o as int, mode, px));
                }
            } else {
                put_px(out, o, mode, px);
            }
            x = x + 1;
            o = o + b;
        }
        proof { lemma_row(old_out, stride as nat, w as nat, mode, p, y as int); }
        y = y + 1;
    }
    proof {
        lemma_end(old_out, stride as nat, mode, p);
        if h == 0 {}
    }
}

// ---------------------------------------------------------------------------
// A decoded image, sealed: only the verified decoder makes one.

pub enum PicX {
    Lossy { f: FrameX, alpha: Option<Vec<u8>> },
    Lossless { img: ImageX },
}

/// The buffers hold `p`.
pub open spec fn pic_is(x: &PicX, p: Pic) -> bool {
    match (x, p) {
        (PicX::Lossy { f, alpha }, Pic::Lossy { f: fs, alpha: al }) => f.is(fs) && match (alpha, al) {
            (None, None) => true,
            (Some(v), Some(s)) => v@ == s,
            _ => false,
        },
        (PicX::Lossless { img }, Pic::Lossless { img: im }) => image_view(img) == im,
        _ => false,
    }
}

/// A decoded image, whose buffers hold `view()`, of the sizes `pic_wf`
/// says. Its fields are private, so code outside this module (the C API's
/// glue) can only get one from `Decoded::new`, and cannot break `inv`.
pub struct Decoded {
    x: PicX,
    p: Ghost<Pic>,
}

impl Decoded {
    #[verifier::type_invariant]
    spec fn inv(&self) -> bool { pic_is(&self.x, self.p@) && pic_wf(self.p@) }

    pub closed spec fn view(&self) -> Pic { self.p@ }

    pub fn new(x: PicX, Ghost(p): Ghost<Pic>) -> (r: Decoded)
        requires pic_is(&x, p), pic_wf(p),
        ensures r.view() == p,
    {
        Decoded { x, p: Ghost(p) }
    }

    pub fn width(&self) -> (r: usize)
        ensures r == pic_w(self.view()), r <= 16384,
    {
        proof { use_type_invariant(self); }
        match &self.x { PicX::Lossy { f, .. } => f.w, PicX::Lossless { img } => img.w }
    }

    pub fn height(&self) -> (r: usize)
        ensures r == pic_h(self.view()), r <= 16384,
    {
        proof { use_type_invariant(self); }
        match &self.x { PicX::Lossy { f, .. } => f.h, PicX::Lossless { img } => img.h }
    }

    pub fn is_lossless(&self) -> (r: bool)
        ensures r == (self.view() is Lossless),
    {
        proof { use_type_invariant(self); }
        match &self.x { PicX::Lossy { .. } => false, PicX::Lossless { .. } => true }
    }

    /// Write the image into `out` in `mode`, rows `stride` bytes apart, as
    /// libwebp's `WebPDecode` does (`render`); false, leaving `out` alone,
    /// if the mode is not one of `mode_ok`'s or the image does not fit.
    pub fn render_x(&self, out: &mut [u8], stride: usize, mode: u8) -> (ok: bool)
        ensures
            ok == (mode_ok(mode) && fits(old(out)@.len(), stride as nat, pic_w(self.view()), pic_h(self.view()), mode)),
            ok ==> final(out)@ == render(old(out)@, stride as nat, mode, self.view()),
            !ok ==> final(out)@ == old(out)@,
    {
        proof { use_type_invariant(self); }
        if !(mode <= 4 || (7 <= mode && mode <= 9)) {
            return false;
        }
        let w = self.width();
        let h = self.height();
        let b: usize = if mode == 0 || mode == 2 { 3 } else { 4 };
        proof { assert(w * b <= 16384 * 4) by (nonlinear_arith) requires w <= 16384, b <= 4; }
        if stride < 1 || stride < w * b {
            return false;
        }
        if h > 0 {
            // (h - 1) * stride + w * b <= len, without overflow.
            let n = out.len();
            if n < w * b {
                return false;
            }
            if h > 1 && stride > (n - w * b) / (h - 1) {
                proof {
                    assert((h - 1) * stride + w * b > n) by (nonlinear_arith)
                        requires h > 1, stride > (n - w * b) / (h - 1), n >= w * b;
                }
                return false;
            }
            proof {
                if h > 1 {
                    assert((h - 1) * stride <= n - w * b) by (nonlinear_arith)
                        requires h > 1, stride <= (n - w * b) / (h - 1), n >= w * b;
                }
            }
        }
        match &self.x {
            PicX::Lossy { f, alpha } => render_lossy_x(out, stride, mode, f, alpha, Ghost(self.p@)),
            PicX::Lossless { img } => render_lossless_x(out, stride, mode, img, Ghost(self.p@)),
        }
        true
    }
}

} // verus!
