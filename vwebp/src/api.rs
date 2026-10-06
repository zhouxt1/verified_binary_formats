//! The inputs libwebp's `WebPDecode` takes, verified: `payload_x` computes
//! `payload`, and hands back a `rgb::Decoded`, which `render_x` writes out
//! in libwebp's RGB(A) convention.
//!
//! `WebPDecode` (`ParseHeadersInternal` in `dec/webp_dec.c`) takes more than
//! WebP files. libwebpdemux (so every `WebPAnimDecoder` user, Pillow among
//! them) passes it a frame's chunks without the RIFF header: the `ALPH`
//! chunk, any chunks after it, and the `VP8 ` chunk; or a lone `VP8 ` or
//! `VP8L` chunk. It also takes a raw VP8 or VP8L bitstream. `payload`:
//!
//! * `RIFF`...: a WebP file, as `cspec::webp` (lossless, animated) and
//!   `vp8::fspec::webp_lossy` (lossy, with alpha) have it.
//! * A `VP8 ` chunk first: its payload is a frame, without alpha.
//! * A `VP8L` chunk first: its payload is a VP8L bitstream.
//! * An `ALPH` chunk first: the chunks up to the first `VP8 ` or `VP8L`
//!   (`cspec::find_image`); the last `ALPH` among them is the frame's alpha
//!   (`vp8::fspec::last_alph`), as libwebp's `ParseOptionalChunks`. A VP8L
//!   image after them ignores them, as libwebp does.
//! * Anything else is a raw bitstream: VP8L if it starts with its
//!   signature byte 0x2f, else VP8.
//!
//! Where libwebp's container parsing refuses what the RFC allows (`lib`
//! false; `cspec`, `fspec`), the C API refuses it too. The raw and chunk
//! forms are libwebp's, not the RFC's ("not a valid WebP format: only
//! allowed for internal purpose").
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::lsb::lbits;
use crate::cspec::*;
use crate::riff::*;
use crate::dec::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::spec::vp8l;
use crate::vp8::fspec::*;
use crate::vp8::file::*;
use crate::rgb::*;

verus! {

pub enum Payload {
    /// An image, and whether libwebp's container parsing takes it too.
    Image { p: Pic, lib: bool },
    /// An animated file: `WebPDecode` does not decode those.
    Animated,
}

pub open spec fn lossy_pic(l: Lossy) -> Option<Payload> {
    match l {
        Lossy::Image { frame, alpha, lib } => Some(Payload::Image { p: Pic::Lossy { f: frame, alpha }, lib }),
        Lossy::NotLossy => None,
    }
}

pub open spec fn lossy_opt(l: Option<Lossy>) -> Option<Payload> {
    match l { None => None, Some(l) => lossy_pic(l) }
}

/// A VP8L bitstream's image.
pub open spec fn lossless(bs: Seq<u8>, lib: bool) -> Option<Payload> {
    match vp8l(lbits(bs)) {
        None => None,
        Some((img, _bits, _st)) => Some(Payload::Image { p: Pic::Lossless { img }, lib }),
    }
}

/// A raw bitstream.
pub open spec fn raw(d: Seq<u8>) -> Option<Payload> {
    if d.len() >= 1 && d[0] == 0x2f { lossless(d, true) } else { lossy_opt(lossy_image(d, None, 0, 0, true)) }
}

/// Chunks without the RIFF header, or a raw bitstream.
pub open spec fn chunks(d: Seq<u8>) -> Option<Payload> {
    match chunk_at(d, 0) {
        None => raw(d),
        Some((cc, a, e)) =>
            if cc == cc_vp8() {
                lossy_opt(lossy_image(d.subrange(a, e), None, 0, 0, true))
            } else if cc == cc_vp8l() {
                lossless(d.subrange(a, e), true)
            } else if cc == cc_alph() {
                match find_image(d, 0) {
                    None => None,
                    Some((cc2, a2, e2)) =>
                        if cc2 == cc_vp8() {
                            lossy_opt(lossy_image(d.subrange(a2, e2), last_alph(d, 0, a2 - 8, None), 0, 0, true))
                        } else {
                            lossless(d.subrange(a2, e2), true)
                        },
                }
            } else {
                raw(d)
            },
    }
}

/// What `WebPDecode` decodes `d` to.
pub open spec fn payload(d: Seq<u8>) -> Option<Payload> {
    if d.len() >= 4 && le32(d, 0) == cc_riff() {
        match webp(d) {
            None => None,
            Some((Webp::Animated, _)) => Some(Payload::Animated),
            Some((Webp::Still { img, strict: _ }, lib)) => Some(Payload::Image { p: Pic::Lossless { img }, lib }),
            Some((Webp::Lossy, _)) => lossy_opt(webp_lossy(d)),
        }
    } else {
        chunks(d)
    }
}

pub enum DecodeX {
    Image { d: Decoded, lib: bool },
    Animated,
}

/// `r` is `payload`'s answer. `TooBig` says only that nothing was decoded:
/// an image of more than `max_pixels`, an input of 4 GiB or more, or
/// planes of other sizes than `rgb::pic_wf`'s, which the decoders do not
/// make (they are checked, not proved, here).
pub open spec fn decoded(r: Result<DecodeX, Error>, want: Option<Payload>) -> bool {
    match r {
        Ok(DecodeX::Image { d, lib }) => want == Some(Payload::Image { p: d.view(), lib }),
        Ok(DecodeX::Animated) => want == Some(Payload::Animated),
        Err(Error::Bad) => want is None,
        Err(Error::TooBig) => true,
    }
}

proof fn lemma_cancel(a: int, b: int, c: int)
    requires a * c == b * c, c >= 1, a >= 0, b >= 0,
    ensures a == b,
{
    if a < b { assert(a * c < b * c) by (nonlinear_arith) requires a < b, c >= 1; }
    if a > b { assert(a * c > b * c) by (nonlinear_arith) requires a > b, c >= 1; }
}

fn wrap_lossy(x: crate::vp8::file::LossyX, Ghost(l): Ghost<Lossy>) -> (r: Result<DecodeX, Error>)
    requires lossy_is(&x, l),
    ensures decoded(r, lossy_pic(l)),
{
    match x {
        LossyX::NotLossy => Err(Error::Bad),
        LossyX::Image { frame, alpha, lib } => {
            let ghost (fs, al) = match l { Lossy::Image { frame, alpha, .. } => (frame, alpha), _ => arbitrary() };
            let w = frame.w;
            let h = frame.h;
            if w > 16384 || h > 16384 {
                return Err(Error::TooBig);
            }
            let cw = (w + 1) / 2;
            let ch = (h + 1) / 2;
            proof {
                assert(w * h <= 16384 * 16384) by (nonlinear_arith) requires w <= 16384, h <= 16384;
                assert(cw * ch <= 8192 * 8192) by (nonlinear_arith) requires cw <= 8192, ch <= 8192;
            }
            if w == 0 || h == 0 || frame.y.len() != w * h || frame.u.len() != cw * ch || frame.v.len() != cw * ch {
                return Err(Error::TooBig);
            }
            match &alpha {
                None => {},
                Some(a) => if a.len() != w * h { return Err(Error::TooBig); },
            }
            proof {
                lemma_cancel(fs.y.len() as int, h as int, w as int);
                assert(h * w == w * h) by (nonlinear_arith);
                assert(ch * cw == cw * ch) by (nonlinear_arith);
                lemma_cancel(fs.u.len() as int, ch as int, cw as int);
                lemma_cancel(fs.v.len() as int, ch as int, cw as int);
            }
            let ghost p = Pic::Lossy { f: fs, alpha: al };
            Ok(DecodeX::Image { d: Decoded::new(PicX::Lossy { f: frame, alpha }, Ghost(p)), lib })
        },
    }
}

fn wrap_lossless(img: ImageX, lib: bool) -> (r: Result<DecodeX, Error>)
    ensures decoded(r, Some(Payload::Image { p: Pic::Lossless { img: image_view(&img) }, lib })),
{
    if img.w > 16384 || img.h > 16384 {
        return Err(Error::TooBig);
    }
    proof { assert(img.w * img.h <= 16384 * 16384) by (nonlinear_arith) requires img.w <= 16384, img.h <= 16384; }
    if img.px.len() != img.w * img.h {
        return Err(Error::TooBig);
    }
    let ghost p = Pic::Lossless { img: image_view(&img) };
    Ok(DecodeX::Image { d: Decoded::new(PicX::Lossless { img }, Ghost(p)), lib })
}

fn lossless_x(bs: &[u8], lib: bool, max_pixels: u64) -> (r: Result<DecodeX, Error>)
    requires bs@.len() <= 0xffff_ffff,
    ensures decoded(r, lossless(bs@, lib)),
{
    match vp8l_x(bs, max_pixels) {
        Err(e) => Err(e),
        Ok((img, _bits, _st)) => wrap_lossless(img, lib),
    }
}

fn lossy_x(frame: &[u8], ach: Option<&[u8]>, max_pixels: u64) -> (r: Result<DecodeX, Error>)
    requires match ach { None => true, Some(d) => d@.len() <= 0xffff_ffff },
    ensures decoded(r, lossy_opt(lossy_image(frame@, opt(ach), 0, 0, true))),
{
    match lossy_image_x(frame, ach, 0, 0, true, max_pixels) {
        Err(crate::vp8::dec::Error::Bad) => Err(Error::Bad),
        Err(crate::vp8::dec::Error::TooBig) => Err(Error::TooBig),
        Ok(x) => wrap_lossy(x, Ghost(lossy_image(frame@, opt(ach), 0, 0, true).unwrap())),
    }
}

fn raw_x(d: &[u8], max_pixels: u64) -> (r: Result<DecodeX, Error>)
    requires d@.len() <= 0xffff_ffff,
    ensures decoded(r, raw(d@)),
{
    if d.len() >= 1 && d[0] == 0x2f { lossless_x(d, true, max_pixels) } else { lossy_x(d, None, max_pixels) }
}

fn chunks_x(d: &[u8], max_pixels: u64) -> (r: Result<DecodeX, Error>)
    requires d@.len() <= 0xffff_ffff,
    ensures decoded(r, chunks(d@)),
{
    proof { lemma_fourccs(); }
    match chunk_at_x(d, 0) {
        None => raw_x(d, max_pixels),
        Some((cc, a, e)) => {
            if cc == 0x2038_5056 {
                lossy_x(vstd::slice::slice_subrange(d, a, e), None, max_pixels)
            } else if cc == 0x4c38_5056 {
                lossless_x(vstd::slice::slice_subrange(d, a, e), true, max_pixels)
            } else if cc == 0x4850_4c41 {
                match find_image_x(d, 0) {
                    None => Err(Error::Bad),
                    Some((cc2, a2, e2)) => {
                        let fr = vstd::slice::slice_subrange(d, a2, e2);
                        if cc2 == 0x2038_5056 {
                            proof { reveal_find_image_start(d@, 0); }
                            let al = last_alph_x(d, 0, a2 - 8);
                            let ach: Option<&[u8]> = match al { None => None, Some((x0, x1)) => Some(vstd::slice::slice_subrange(d, x0, x1)) };
                            lossy_x(fr, ach, max_pixels)
                        } else {
                            lossless_x(fr, true, max_pixels)
                        }
                    },
                }
            } else {
                raw_x(d, max_pixels)
            }
        },
    }
}

/// Decode what `WebPDecode` takes (`payload`), refusing an image of more
/// than `max_pixels`.
pub fn payload_x(d: &[u8], max_pixels: u64) -> (r: Result<DecodeX, Error>)
    ensures decoded(r, payload(d@)),
{
    proof { lemma_fourccs(); }
    if d.len() > 0xffff_ffff {
        return Err(Error::TooBig);
    }
    if d.len() >= 4 && le32_x(d, 0) == 0x4646_4952 {
        match webp_x(d, max_pixels) {
            Err(e) => Err(e),
            Ok((WebpX::Animated, _)) => Ok(DecodeX::Animated),
            Ok((WebpX::Still { img, strict: _ }, lib)) => wrap_lossless(img, lib),
            Ok((WebpX::Lossy, _)) => match webp_lossy_x(d, max_pixels) {
                Err(crate::vp8::dec::Error::Bad) => Err(Error::Bad),
                Err(crate::vp8::dec::Error::TooBig) => Err(Error::TooBig),
                Ok(x) => wrap_lossy(x, Ghost(webp_lossy(d@).unwrap())),
            },
        }
    } else {
        chunks_x(d, max_pixels)
    }
}

} // verus!
