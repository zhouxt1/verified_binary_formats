//! The whole VP8L decoder, proved to compute `spec::vp8l`.
use vstd::prelude::*;
use vbits::lsb::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::getbits;
use crate::code::*;
use crate::img::*;
use crate::tr::*;
use crate::spec::*;

verus! {

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Error {
    /// Not a VP8L bitstream the spec decodes.
    Bad,
    /// The header says more pixels than the caller allows.
    TooBig,
}

/// A decoded image: its size, the alpha hint, and ARGB pixels in scan-line
/// order (alpha in bits 31..24, red 23..16, green 15..8, blue 7..0).
pub struct ImageX {
    pub w: usize,
    pub h: usize,
    pub alpha_hint: bool,
    pub px: Vec<u32>,
}

pub open spec fn image_view(i: &ImageX) -> Image {
    Image { w: i.w as nat, h: i.h as nat, alpha_hint: i.alpha_hint, px: i.px@ }
}

/// The width and height the header of `b` says, if it has one.
pub open spec fn header_size(b: Seq<bool>) -> Option<(nat, nat)> {
    match (getbits(b, 8, 14), getbits(b, 22, 14)) {
        (Some(w1), Some(h1)) => Some((w1 + 1, h1 + 1)),
        _ => None,
    }
}

/// Decode a VP8L bitstream of at most `max_pixels` pixels: the image, the
/// bits the stream took, and `strict`.
pub fn vp8l_x(buf: &[u8], max_pixels: u64) -> (r: Result<(ImageX, usize, bool), Error>)
    requires buf_ok(buf@),
    ensures
        match r {
            Ok((img, bits, st)) => vp8l(lbits(buf@)) == Some((image_view(&img), bits as nat, st))
                && img.px@.len() == img.w * img.h && img.w * img.h <= max_pixels
                && 1 <= img.w <= 16384 && 1 <= img.h <= 16384,
            Err(Error::Bad) => vp8l(lbits(buf@)) is None,
            Err(Error::TooBig) => match header_size(lbits(buf@)) {
                Some((w, h)) => w * h > max_pixels,
                None => false,
            },
        },
{
    let ghost b = lbits(buf@);
    let sig = match getbits_x(buf, 0, 8) { None => return Err(Error::Bad), Some(x) => x };
    let w1 = match getbits_x(buf, 8, 14) { None => return Err(Error::Bad), Some(x) => x };
    let h1 = match getbits_x(buf, 22, 14) { None => return Err(Error::Bad), Some(x) => x };
    let a = match getbits_x(buf, 36, 1) { None => return Err(Error::Bad), Some(x) => x };
    let ver = match getbits_x(buf, 37, 3) { None => return Err(Error::Bad), Some(x) => x };
    if sig != 0x2f || ver != 0 {
        return Err(Error::Bad);
    }
    proof { assert(vbits::bitspec::p2(14) == 16384) by { reveal_with_fuel(vbits::bitspec::p2, 15); } }
    let w = (w1 + 1) as usize;
    let h = (h1 + 1) as usize;
    proof { assert(w * h <= 0x1000_0000) by (nonlinear_arith) requires w <= 16384, h <= 16384; }
    if (w * h) as u64 > max_pixels {
        return Err(Error::TooBig);
    }
    let (ts, dw, p, st) = match read_transforms_x(buf, 40, w, h) { None => return Err(Error::Bad), Some(x) => x };
    let (px, q, st2) = match spatially_coded_image_x(buf, p, dw, h) { None => return Err(Error::Bad), Some(x) => x };
    let out = inverses_x(&ts, w, h, px);
    Ok((ImageX { w, h, alpha_hint: a == 1, px: out }, q, st && st2))
}

} // verus!
