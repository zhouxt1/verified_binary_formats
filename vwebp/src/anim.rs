//! Animated WebP, proved to compute `aspec::webp_anim`.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::lsb::lbits;
use crate::aspec::*;
use crate::cspec::*;
use crate::dec::*;
use crate::inv::*;
use crate::spec::*;

verus! {

fn le32_x(f: &[u8], i: usize) -> (r: u64)
    requires i + 4 <= f@.len(),
    ensures r as nat == le32(f@, i as int), r <= 0xffff_ffff,
{
    f[i] as u64 + 256 * f[i + 1] as u64 + 65536 * f[i + 2] as u64 + 16777216 * f[i + 3] as u64
}

fn le24_x(f: &[u8], i: usize) -> (r: u64)
    requires i + 3 <= f@.len(),
    ensures r as nat == le24(f@, i as int), r <= 0xff_ffff,
{
    f[i] as u64 + 256 * f[i + 1] as u64 + 65536 * f[i + 2] as u64
}

fn le16_x(f: &[u8], i: usize) -> (r: u64)
    requires i + 2 <= f@.len(),
    ensures r as nat == le16(f@, i as int), r <= 0xffff,
{
    f[i] as u64 + 256 * f[i + 1] as u64
}

fn padded_x(e: usize) -> (r: usize)
    requires e < usize::MAX,
    ensures r as int == padded(e as int), e <= r <= e + 1,
{
    if e % 2 == 1 { e + 1 } else { e }
}

/// `fits`.
fn fits_x(body: &[u8], i0: usize, end: usize) -> (r: bool)
    requires end <= body@.len(), body@.len() <= 0xffff_ffff,
    ensures r == fits(body@, i0 as int, end as int),
{
    let mut i = i0;
    loop
        invariant end <= body@.len(), body@.len() <= 0xffff_ffff,
            fits(body@, i as int, end as int) == fits(body@, i0 as int, end as int),
        decreases end - i,
    {
        if i >= end {
            return i == end;
        }
        if end - i < 8 {
            return false;
        }
        let size = le32_x(body, i + 4) as usize;
        let nxt = padded_x(i + 8 + size);
        if nxt > end {
            return false;
        }
        i = nxt;
    }
}

pub struct AFrameX {
    pub x: usize,
    pub y: usize,
    pub img: ImageX,
    pub dur: u64,
    pub dispose_bg: bool,
    pub no_blend: bool,
}

pub open spec fn aframe_view(f: &AFrameX) -> AFrame {
    AFrame { x: f.x as nat, y: f.y as nat, img: image_view(&f.img), dur: f.dur as nat,
             dispose_bg: f.dispose_bg, no_blend: f.no_blend }
}

/// A frame that fits its canvas: its pixels are its size, inside `cw` x `ch`.
pub open spec fn aframe_ok(f: &AFrameX, cw: nat, ch: nat) -> bool {
    &&& f.img.px@.len() == f.img.w * f.img.h
    &&& f.x + f.img.w <= cw && f.y + f.img.h <= ch
    &&& f.dur <= 0xff_ffff
}

pub enum FrameR {
    Frame(AFrameX),
    Lossy,
}

/// `frame_at`.
fn frame_at_x(body: &[u8], a: usize, e: usize, pe: usize, cw: u64, ch: u64, max_pixels: u64)
    -> (r: Result<FrameR, Error>)
    requires body@.len() <= 0xffff_ffff, a <= e <= pe <= body@.len(), cw <= 0x100_0000, ch <= 0x100_0000,
    ensures
        match r {
            Ok(FrameR::Frame(fr)) => frame_at(body@, a as int, e as int, pe as int, cw as nat, ch as nat)
                    == Some(Some(aframe_view(&fr))) && aframe_ok(&fr, cw as nat, ch as nat),
            Ok(FrameR::Lossy) => frame_at(body@, a as int, e as int, pe as int, cw as nat, ch as nat) == Some(None::<AFrame>),
            Err(Error::Bad) => frame_at(body@, a as int, e as int, pe as int, cw as nat, ch as nat) is None,
            Err(Error::TooBig) => true,
        },
{
    proof { crate::riff::lemma_fourccs(); }
    if e - a < 16 {
        return Err(Error::Bad);
    }
    let fx = 2 * le24_x(body, a);
    let fy = 2 * le24_x(body, a + 3);
    let fw = le24_x(body, a + 6) + 1;
    let fh = le24_x(body, a + 9) + 1;
    let dur = le24_x(body, a + 12);
    let bits = body[a + 15];
    proof { assert(fw * fh <= 0x100_0000 * 0x100_0000) by (nonlinear_arith) requires fw <= 0x100_0000, fh <= 0x100_0000; }
    if fw * fh > 0xffff_ffff || !fits_x(body, a + 16, pe) || a + 16 >= pe {
        return Err(Error::Bad);
    }
    frame_img_x(body, a + 16, pe, fx, fy, dur, bits, cw, ch, max_pixels)
}

/// `frame_img`.
fn frame_img_x(body: &[u8], s: usize, pe: usize, fx: u64, fy: u64, dur: u64, bits: u8, cw: u64, ch: u64, max_pixels: u64)
    -> (r: Result<FrameR, Error>)
    requires body@.len() <= 0xffff_ffff, s < pe <= body@.len(), fits(body@, s as int, pe as int),
        cw <= 0x100_0000, ch <= 0x100_0000, fx <= 0x200_0000, fy <= 0x200_0000, dur <= 0xff_ffff,
    ensures
        match r {
            Ok(FrameR::Frame(fr)) => frame_img(body@, s as int, pe as int, fx as nat, fy as nat, dur as nat, bits, cw as nat, ch as nat)
                    == Some(Some(aframe_view(&fr))) && aframe_ok(&fr, cw as nat, ch as nat),
            Ok(FrameR::Lossy) => frame_img(body@, s as int, pe as int, fx as nat, fy as nat, dur as nat, bits, cw as nat, ch as nat)
                    == Some(None::<AFrame>),
            Err(Error::Bad) => frame_img(body@, s as int, pe as int, fx as nat, fy as nat, dur as nat, bits, cw as nat, ch as nat) is None,
            Err(Error::TooBig) => true,
        },
{
    proof { crate::riff::lemma_fourccs(); assert(cc_alph() == 0x4850_4c41); lemma_fits_header(body@, s as int, pe as int, s as int); }
    let k = if le32_x(body, s) == 0x4850_4c41 {
        let size = le32_x(body, s + 4) as usize;
        padded_x(s + 8 + size)
    } else {
        s
    };
    if k >= pe {
        return Err(Error::Bad);
    }
    proof { lemma_fits_header(body@, s as int, pe as int, k as int); }
    let tag = le32_x(body, k);
    if k != s && tag == 0x4c38_5056 {
        return Err(Error::Bad);
    }
    if tag == 0x2038_5056 {
        return Ok(FrameR::Lossy);
    }
    if tag != 0x4c38_5056 {
        return Err(Error::Bad);
    }
    let size = le32_x(body, k + 4) as usize;
    let bs = vstd::slice::slice_subrange(body, k + 8, k + 8 + size);
    frame_of_x(bs, fx, fy, dur, bits, cw, ch, max_pixels)
}

/// `frame_of`.
fn frame_of_x(bs: &[u8], fx: u64, fy: u64, dur: u64, bits: u8, cw: u64, ch: u64, max_pixels: u64) -> (r: Result<FrameR, Error>)
    requires bs@.len() <= 0xffff_ffff, cw <= 0x100_0000, ch <= 0x100_0000, fx <= 0x200_0000, fy <= 0x200_0000, dur <= 0xff_ffff,
    ensures
        match r {
            Ok(FrameR::Frame(fr)) => frame_of(bs@, fx as nat, fy as nat, dur as nat, bits, cw as nat, ch as nat)
                    == Some(Some(aframe_view(&fr))) && aframe_ok(&fr, cw as nat, ch as nat),
            Ok(FrameR::Lossy) => false,
            Err(Error::Bad) => frame_of(bs@, fx as nat, fy as nat, dur as nat, bits, cw as nat, ch as nat) is None,
            Err(Error::TooBig) => true,
        },
{
    hide(vp8l);
    let (img, _bits, _st) = vp8l_x(bs, max_pixels)?;
    if fx + img.w as u64 > cw || fy + img.h as u64 > ch {
        return Err(Error::Bad);
    }
    Ok(FrameR::Frame(AFrameX { x: fx as usize, y: fy as usize, img, dur, dispose_bg: bits & 1 == 1, no_blend: bits & 2 == 2 }))
}

/// A chunk list that fits from `i` to `end` has a whole chunk at `i` and at
/// the chunk after it, when that is before `end`.
proof fn lemma_fits_header(body: Seq<u8>, i: int, end: int, k: int)
    requires fits(body, i, end), i < end, k == i || (k == next_chunk(body, i)), k < end,
    ensures k + 8 <= end, next_chunk(body, k) <= end, k + 8 + le32(body, k + 4) <= end,
{
    reveal_with_fuel(fits, 3);
    if k != i {
        assert(fits(body, next_chunk(body, i), end));
    }
}


// ------------------------------------------------------- the chunk walk

pub open spec fn frames_view(v: Seq<AFrameX>) -> Seq<AFrame> {
    Seq::new(v.len(), |k: int| aframe_view(&v[k]))
}

pub open spec fn anim_view(a: Option<(u64, u64)>) -> Option<(nat, nat)> {
    match a {
        None => None,
        Some((bg, l)) => Some((bg as nat, l as nat)),
    }
}

pub enum ParsedX {
    Frames(Option<(u64, u64)>, Vec<AFrameX>),
    Lossy,
}

/// `top_chunks` from none, over chunks that fit.
fn top_chunks_x(body: &[u8], i0: usize, end: usize, cw: u64, ch: u64, max_pixels: u64) -> (r: Result<ParsedX, Error>)
    requires body@.len() <= 0xffff_ffff, end <= body@.len(), fits(body@, i0 as int, end as int),
        cw <= 0x100_0000, ch <= 0x100_0000,
    ensures
        match r {
            Ok(ParsedX::Frames(a, v)) => top_chunks(body@, i0 as int, end as int, cw as nat, ch as nat,
                    PSt { anim: None, frames: Seq::empty() })
                    == Some(Parsed::Frames(PSt { anim: anim_view(a), frames: frames_view(v@) }))
                && forall|k: int| 0 <= k < v@.len() ==> #[trigger] aframe_ok(&v@[k], cw as nat, ch as nat),
            Ok(ParsedX::Lossy) => top_chunks(body@, i0 as int, end as int, cw as nat, ch as nat,
                    PSt { anim: None, frames: Seq::empty() }) == Some(Parsed::Lossy),
            Err(Error::Bad) => top_chunks(body@, i0 as int, end as int, cw as nat, ch as nat,
                    PSt { anim: None, frames: Seq::empty() }) is None,
            Err(Error::TooBig) => true,
        },
{
    let ghost target = top_chunks(body@, i0 as int, end as int, cw as nat, ch as nat, PSt { anim: None, frames: Seq::empty() });
    let mut i = i0;
    let mut anim: Option<(u64, u64)> = None;
    let mut v: Vec<AFrameX> = Vec::new();
    proof {
        crate::riff::lemma_fourccs();
        assert(cc_alph() == 0x4850_4c41 && cc_anim() == 0x4d49_4e41 && cc_anmf() == 0x464d_4e41);
        assert(frames_view(v@) =~= Seq::<AFrame>::empty());
    }
    loop
        invariant
            body@.len() <= 0xffff_ffff, end <= body@.len(), fits(body@, i as int, end as int),
            cw <= 0x100_0000, ch <= 0x100_0000,
            cc_alph() == 0x4850_4c41 && cc_anim() == 0x4d49_4e41 && cc_anmf() == 0x464d_4e41,
            cc_vp8x() == 0x5838_5056 && cc_vp8l() == 0x4c38_5056 && cc_vp8() == 0x2038_5056,
            top_chunks(body@, i as int, end as int, cw as nat, ch as nat, PSt { anim: anim_view(anim), frames: frames_view(v@) })
                == target,
            target == top_chunks(body@, i0 as int, end as int, cw as nat, ch as nat, PSt { anim: None, frames: Seq::empty() }),
            forall|k: int| 0 <= k < v@.len() ==> #[trigger] aframe_ok(&v@[k], cw as nat, ch as nat),
        decreases end - i,
    {
        if i >= end || end - i < 8 {
            return Ok(ParsedX::Frames(anim, v));
        }
        proof { lemma_fits_header(body@, i as int, end as int, i as int); }
        let tag = le32_x(body, i);
        let a = i + 8;
        let e = a + le32_x(body, i + 4) as usize;
        let nxt = padded_x(e);
        proof { reveal_with_fuel(fits, 2); assert(fits(body@, nxt as int, end as int)); }
        if tag == 0x5838_5056 || tag == 0x4850_4c41 || tag == 0x2038_5056 || tag == 0x4c38_5056 {
            return Err(Error::Bad);
        }
        if tag == 0x4d49_4e41 {
            if e - a < 6 {
                return Err(Error::Bad);
            }
            if anim.is_none() {
                anim = Some((le32_x(body, a), le16_x(body, a + 4)));
            }
        } else if tag == 0x464d_4e41 {
            if anim.is_none() {
                return Err(Error::Bad);
            }
            match frame_at_x(body, a, e, nxt, cw, ch, max_pixels)? {
                FrameR::Lossy => return Ok(ParsedX::Lossy),
                FrameR::Frame(fr) => {
                    let ghost v0 = v@;
                    v.push(fr);
                    proof { assert(frames_view(v@) =~= frames_view(v0).push(aframe_view(&fr))); }
                },
            }
        }
        i = nxt;
    }
}

// --------------------------------------------------- canvas assembly

/// `blend`: libwebp's formula, in 64 bits.
pub fn blend_x(src: u32, dst: u32) -> (r: u32)
    ensures r == blend(src, dst),
{
    let sa = alpha_x(src);
    if sa == 0 {
        return dst;
    }
    let da = alpha_x(dst);
    proof { assert(0 <= da * (256 - sa) <= 255 * 256) by (nonlinear_arith) requires 0 <= da < 256, 0 < sa < 256; }
    let dfa = (da * (256 - sa)) / 256;
    proof {
        assert(da * (256 - sa) < 256 * (256 - sa)) by (nonlinear_arith) requires 0 <= da < 256, 0 < sa < 256;
        assert(dfa < 256 - sa) by (nonlinear_arith) requires dfa == (da * (256 - sa)) / 256, da * (256 - sa) < 256 * (256 - sa), sa < 256;
        assert(0 <= dfa) by (nonlinear_arith) requires dfa == (da * (256 - sa)) / 256, 0 <= da, sa < 256;
    }
    let ba = sa + dfa;
    let scale = 0x100_0000i64 / ba;
    proof {
        assert(scale <= 0x100_0000) by (nonlinear_arith) requires scale == 0x100_0000i64 / ba, ba >= 1;
        assert(scale >= 0) by (nonlinear_arith) requires scale == 0x100_0000i64 / ba, ba >= 1;
    }
    let r = blend_ch_x(red_x(src), sa, red_x(dst), dfa, scale);
    let g = blend_ch_x(green_x(src), sa, green_x(dst), dfa, scale);
    let b = blend_ch_x(blue_x(src), sa, blue_x(dst), dfa, scale);
    argb_x(ba, r, g, b)
}

fn blend_ch_x(sc: i64, sa: i64, dc: i64, dfa: i64, scale: i64) -> (r: i64)
    requires 0 <= sc < 256, 0 < sa < 256, 0 <= dc < 256, 0 <= dfa < 256, 0 <= scale <= 0x100_0000,
    ensures r == blend_ch(sc as int, sa as int, dc as int, dfa as int, scale as int), 0 <= r < 256,
{
    proof {
        assert(0 <= sc * sa + dc * dfa <= 2 * 255 * 255) by (nonlinear_arith)
            requires 0 <= sc < 256, 0 < sa < 256, 0 <= dc < 256, 0 <= dfa < 256;
        assert(0 <= (sc * sa + dc * dfa) * scale <= 2 * 255 * 255 * 0x100_0000) by (nonlinear_arith)
            requires 0 <= sc * sa + dc * dfa <= 2 * 255 * 255, 0 <= scale <= 0x100_0000;
    }
    let x = (sc * sa + dc * dfa) * scale;
    let y = x % 0x1_0000_0000;
    proof {
        assert(0 <= y < 0x1_0000_0000);
        assert(y / 0x100_0000 < 256) by (nonlinear_arith) requires 0 <= y < 0x1_0000_0000;
    }
    y / 0x100_0000
}

/// `in_rect` for pixel (x, y) of the canvas.
pub open spec fn in_rect_xy(fr: AFrame, x: int, y: int) -> bool {
    fr.x <= x < fr.x + fr.img.w && fr.y <= y < fr.y + fr.img.h
}

fn in_rect_x(fr: &AFrameX, x: usize, y: usize) -> (r: bool)
    requires fr.x + fr.img.w <= 0x200_0000, fr.y + fr.img.h <= 0x200_0000,
    ensures r == in_rect_xy(aframe_view(fr), x as int, y as int),
{
    fr.x <= x && x < fr.x + fr.img.w && fr.y <= y && y < fr.y + fr.img.h
}

/// The canvas pixel `i`'s value after drawing: `draw(..)[i]`.
fn draw_px(fr: &AFrameX, k: usize, prev: &AFrameX, key: bool, cw: usize, ch: usize, disposed: &Vec<u32>, i: usize) -> (r: u32)
    requires
        aframe_ok(fr, cw as nat, ch as nat), aframe_ok(prev, cw as nat, ch as nat),
        1 <= cw <= 0x100_0000, 1 <= ch <= 0x100_0000, i < cw * ch, disposed@.len() == cw * ch,
    ensures
        r == ({
            let f = aframe_view(fr);
            let p = aframe_view(prev);
            if in_rect(f, cw as nat, i as int) {
                let s = frame_px(f, cw as nat, i as int);
                if k > 0 && !f.no_blend && !key && !(p.dispose_bg && in_rect(p, cw as nat, i as int)) && alpha(s) != 255 {
                    blend(s, disposed@[i as int])
                } else {
                    s
                }
            } else if key {
                0u32
            } else {
                disposed@[i as int]
            }
        }),
{
    let x = i % cw;
    let y = i / cw;
    proof {
        assert(y < ch) by (nonlinear_arith) requires y == i / cw, i < cw * ch, cw >= 1;
    }
    if in_rect_x(fr, x, y) {
        let (fw, fh) = (fr.img.w, fr.img.h);
        let np = fr.img.px.len();
        proof {
            assert(np == fw * fh);
            assert((y - fr.y) * fw + (x - fr.x) < fw * fh) by (nonlinear_arith)
                requires fr.y <= y < fr.y + fh, fr.x <= x < fr.x + fw;
            assert((y - fr.y) * fw <= (y - fr.y) * fw + (x - fr.x));
        }
        let s = fr.img.px[(y - fr.y) * fw + (x - fr.x)];
        if k > 0 && !fr.no_blend && !key && !(prev.dispose_bg && in_rect_x(prev, x, y)) && s >> 24u32 != 255 {
            blend_x(s, disposed[i])
        } else {
            s
        }
    } else if key {
        0
    } else {
        disposed[i]
    }
}

/// `draw`.
fn draw_x(fr: &AFrameX, k: usize, prev: &AFrameX, key: bool, cw: usize, ch: usize, disposed: &Vec<u32>) -> (r: Vec<u32>)
    requires
        aframe_ok(fr, cw as nat, ch as nat), aframe_ok(prev, cw as nat, ch as nat),
        1 <= cw <= 0x100_0000, 1 <= ch <= 0x100_0000, cw * ch <= 0x1_0000_0000, disposed@.len() == cw * ch,
    ensures
        r@ == draw(aframe_view(fr), k as int, aframe_view(prev), key, cw as nat, ch as nat, disposed@),
{
    let n = cw * ch;
    let mut out: Vec<u32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == cw * ch, aframe_ok(fr, cw as nat, ch as nat), aframe_ok(prev, cw as nat, ch as nat),
            1 <= cw <= 0x100_0000, 1 <= ch <= 0x100_0000, disposed@.len() == n, i <= n, out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] out@[j]
                == draw(aframe_view(fr), k as int, aframe_view(prev), key, cw as nat, ch as nat, disposed@)[j],
        decreases n - i,
    {
        out.push(draw_px(fr, k, prev, key, cw, ch, disposed, i));
        i = i + 1;
    }
    proof { assert(out@ =~= draw(aframe_view(fr), k as int, aframe_view(prev), key, cw as nat, ch as nat, disposed@)); }
    out
}

/// `dispose`.
fn dispose_x(fr: &AFrameX, cw: usize, ch: usize, canvas: &Vec<u32>) -> (r: Vec<u32>)
    requires aframe_ok(fr, cw as nat, ch as nat), 1 <= cw <= 0x100_0000, 1 <= ch <= 0x100_0000,
        canvas@.len() == cw * ch,
    ensures r@ == dispose(aframe_view(fr), cw as nat, canvas@),
{
    if !fr.dispose_bg {
        return canvas.clone();
    }
    let n = canvas.len();
    let mut out: Vec<u32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            n == canvas@.len(), n == cw * ch, aframe_ok(fr, cw as nat, ch as nat), fr.dispose_bg,
            1 <= cw <= 0x100_0000, 1 <= ch <= 0x100_0000, i <= n, out@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] out@[j] == dispose(aframe_view(fr), cw as nat, canvas@)[j],
        decreases n - i,
    {
        let x = i % cw;
        let y = i / cw;
        out.push(if in_rect_x(fr, x, y) { 0 } else { canvas[i] });
        i = i + 1;
    }
    proof { assert(out@ =~= dispose(aframe_view(fr), cw as nat, canvas@)); }
    out
}


fn is_key_x(fr: &AFrameX, k: usize, prev: &AFrameX, prev_key: bool, cw: usize, ch: usize) -> (r: bool)
    ensures r == is_key(aframe_view(fr), k as int, aframe_view(prev), prev_key, cw as nat, ch as nat),
{
    let full = fr.img.w == cw && fr.img.h == ch;
    let prev_full = prev.img.w == cw && prev.img.h == ch;
    k == 0 || ((!fr.img.alpha_hint || fr.no_blend) && full) || (prev.dispose_bg && (prev_full || prev_key))
}

pub open spec fn outs_view(v: Seq<(u64, Vec<u32>)>) -> Seq<(nat, Seq<u32>)> {
    Seq::new(v.len(), |j: int| (v[j].0 as nat, v[j].1@))
}

/// `compose` from the first frame on a transparent canvas.
fn compose_x(frames: &Vec<AFrameX>, cw: usize, ch: usize) -> (r: Vec<(u64, Vec<u32>)>)
    requires
        1 <= cw <= 0x100_0000, 1 <= ch <= 0x100_0000, cw * ch <= 0x1_0000_0000, frames@.len() <= 0x1_0000_0000,
        forall|k: int| 0 <= k < frames@.len() ==> #[trigger] aframe_ok(&frames@[k], cw as nat, ch as nat),
    ensures
        outs_view(r@) == compose(frames_view(frames@), 0, cw as nat, ch as nat, Seq::new((cw * ch) as nat, |_i: int| 0u32),
                                 false, 0, Seq::empty()),
{
    let ghost fv = frames_view(frames@);
    let ghost target = compose(fv, 0, cw as nat, ch as nat, Seq::new((cw * ch) as nat, |_i: int| 0u32), false, 0, Seq::empty());
    let n = frames.len();
    let mut disposed: Vec<u32> = vec![0u32; cw * ch];
    let mut prev_key = false;
    let mut ts: u64 = 0;
    let mut out: Vec<(u64, Vec<u32>)> = Vec::new();
    let mut k: usize = 0;
    proof {
        assert(disposed@ =~= Seq::new((cw * ch) as nat, |_i: int| 0u32));
        assert(outs_view(out@) =~= Seq::<(nat, Seq<u32>)>::empty());
    }
    while k < n
        invariant
            n == frames@.len(), n <= 0x1_0000_0000, fv == frames_view(frames@), k <= n,
            1 <= cw <= 0x100_0000, 1 <= ch <= 0x100_0000, cw * ch <= 0x1_0000_0000,
            forall|j: int| 0 <= j < frames@.len() ==> #[trigger] aframe_ok(&frames@[j], cw as nat, ch as nat),
            disposed@.len() == cw * ch, ts <= k * 0xff_ffff,
            compose(fv, k as int, cw as nat, ch as nat, disposed@, prev_key, ts as nat, outs_view(out@)) == target,
            target == compose(frames_view(frames@), 0, cw as nat, ch as nat, Seq::new((cw * ch) as nat, |_i: int| 0u32),
                              false, 0, Seq::empty()),
        decreases n - k,
    {
        let fr = &frames[k];
        let prev = if k > 0 { &frames[k - 1] } else { fr };
        proof {
            assert(aframe_ok(&frames@[k as int], cw as nat, ch as nat));
            if k > 0 { assert(aframe_ok(&frames@[k - 1], cw as nat, ch as nat)); }
            assert(fv[k as int] == aframe_view(fr));
            if k > 0 { assert(fv[k - 1] == aframe_view(prev)); }
        }
        let key = is_key_x(fr, k, prev, prev_key, cw, ch);
        let canvas = draw_x(fr, k, prev, key, cw, ch, &disposed);
        let next = dispose_x(fr, cw, ch, &canvas);
        proof { assert(ts + fr.dur <= (k + 1) * 0xff_ffff) by (nonlinear_arith) requires ts <= k * 0xff_ffff, fr.dur <= 0xff_ffff; }
        ts = ts + fr.dur;
        let ghost o0 = out@;
        let ghost cv = canvas@;
        out.push((ts, canvas));
        proof { assert(outs_view(out@) =~= outs_view(o0).push((ts as nat, cv))); }
        disposed = next;
        prev_key = key;
        k = k + 1;
    }
    out
}

pub enum AnimRX {
    Anim { cw: usize, ch: usize, bg: u64, loops: u64, frames: Vec<(u64, Vec<u32>)>, lib: bool },
    Lossy,
}

pub open spec fn animr_view(r: &AnimRX) -> AnimR {
    match r {
        AnimRX::Anim { cw, ch, bg, loops, frames, lib } =>
            AnimR::Anim { a: Anim { cw: *cw as nat, ch: *ch as nat, bg: *bg as nat, loops: *loops as nat, frames: outs_view(frames@) },
                          lib: *lib },
        AnimRX::Lossy => AnimR::Lossy,
    }
}

/// `animation`: the canvases, at most `max_pixels` pixels in all.
fn animation_x(body: &[u8], a: usize, e: usize, max_pixels: u64) -> (r: Result<AnimRX, Error>)
    requires body@.len() <= 0xffff_ffff, a + 10 <= e <= body@.len(),
    ensures
        match r {
            Ok(x) => animation(body@, a as int, e as int) == Some(animr_view(&x)),
            Err(Error::Bad) => animation(body@, a as int, e as int) is None,
            Err(Error::TooBig) => true,
        },
{
    hide(vp8l);
    hide(frame_of);
    let flags = body[a];
    let cw = le24_x(body, a + 4) + 1;
    let ch = le24_x(body, a + 7) + 1;
    let lib = e - a == 10 && flags & 0xc1 == 0;
    proof { assert(cw * ch <= 0x100_0000 * 0x100_0000) by (nonlinear_arith) requires cw <= 0x100_0000, ch <= 0x100_0000; }
    if cw * ch > 0xffff_ffff || flags & 2 != 2 {
        return Err(Error::Bad);
    }
    let pe = padded_x(e);
    if pe > body.len() || !fits_x(body, pe, body.len()) {
        proof { if pe > body@.len() { reveal_with_fuel(fits, 1); } }
        return Err(Error::Bad);
    }
    let (anim, frames) = match top_chunks_x(body, pe, body.len(), cw, ch, max_pixels)? {
        ParsedX::Lossy => return Ok(AnimRX::Lossy),
        ParsedX::Frames(anim, frames) => (anim, frames),
    };
    let (bg, loops) = match anim { None => return Err(Error::Bad), Some(x) => x };
    if frames.len() == 0 {
        return Err(Error::Bad);
    }
    if frames.len() > 0x1_0000_0000 || cw * ch > max_pixels / frames.len() as u64 {
        return Err(Error::TooBig);
    }
    let out = compose_x(&frames, cw as usize, ch as usize);
    Ok(AnimRX::Anim { cw: cw as usize, ch: ch as usize, bg, loops, frames: out, lib })
}

/// An animated WebP file: its canvases, at most `max_pixels` pixels in all,
/// or that it is lossy. `TooBig` says only that it was not decoded.
pub fn webp_anim_x(f: &[u8], max_pixels: u64) -> (r: Result<AnimRX, Error>)
    ensures
        match r {
            Ok(x) => webp_anim(f@) == Some(animr_view(&x)),
            Err(Error::Bad) => webp_anim(f@) is None,
            Err(Error::TooBig) => true,
        },
{
    proof { crate::riff::lemma_fourccs(); }
    if f.len() < 12 || le32_x(f, 0) != 0x4646_4952 || le32_x(f, 8) != 0x5042_4557 {
        return Err(Error::Bad);
    }
    let rs = le32_x(f, 4);
    if rs < 12 || rs > 0xffff_fff6 || rs as usize > f.len() - 8 {
        return Err(Error::Bad);
    }
    let body = vstd::slice::slice_subrange(f, 12, 8 + rs as usize);
    if body.len() < 8 {
        return Err(Error::Bad);
    }
    let size = le32_x(body, 4) as usize;
    if size > body.len() - 8 {
        return Err(Error::Bad);
    }
    if le32_x(body, 0) != 0x5838_5056 || size < 10 {
        return Err(Error::Bad);
    }
    animation_x(body, 8, 8 + size, max_pixels)
}

} // verus!
