//! The WebP container, proved to compute `cspec::webp`.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::lsb::lbits;
use crate::cspec::*;
use crate::dec::*;
use crate::spec::*;

verus! {

pub enum WebpX {
    Still { img: ImageX, strict: bool },
    Lossy,
    Animated,
}

pub open spec fn webp_view(w: &WebpX) -> Webp {
    match w {
        WebpX::Still { img, strict } => Webp::Still { img: image_view(img), strict: *strict },
        WebpX::Lossy => Webp::Lossy,
        WebpX::Animated => Webp::Animated,
    }
}

pub fn le32_x(f: &[u8], i: usize) -> (r: u64)
    requires i + 4 <= f@.len(),
    ensures r as nat == le32(f@, i as int), r <= 0xffff_ffff,
{
    f[i] as u64 + 256 * f[i + 1] as u64 + 65536 * f[i + 2] as u64 + 16777216 * f[i + 3] as u64
}

pub fn le24_x(f: &[u8], i: usize) -> (r: u64)
    requires i + 3 <= f@.len(),
    ensures r as nat == le24(f@, i as int), r <= 0xff_ffff,
{
    f[i] as u64 + 256 * f[i + 1] as u64 + 65536 * f[i + 2] as u64
}

/// `chunk_at`.
pub fn chunk_at_x(body: &[u8], i: usize) -> (r: Option<(u64, usize, usize)>)
    requires body@.len() <= 0xffff_ffff,
    ensures
        match r {
            Some((cc, a, e)) => chunk_at(body@, i as int) == Some((cc as nat, a as int, e as int))
                && i + 8 == a <= e <= body@.len(),
            None => chunk_at(body@, i as int) is None,
        },
{
    if i > body.len() || body.len() - i < 8 {
        return None;
    }
    let size = le32_x(body, i + 4);
    if size as usize > body.len() - i - 8 {
        return None;
    }
    Some((le32_x(body, i), i + 8, i + 8 + size as usize))
}

/// `find_image`.
pub fn find_image_x(body: &[u8], i0: usize) -> (r: Option<(u64, usize, usize)>)
    requires body@.len() <= 0xffff_ffff,
    ensures
        match r {
            Some((cc, a, e)) => find_image(body@, i0 as int) == Some((cc as nat, a as int, e as int))
                && a <= e <= body@.len(),
            None => find_image(body@, i0 as int) is None,
        },
{
    let ghost target = find_image(body@, i0 as int);
    let mut i = i0;
    loop
        invariant body@.len() <= 0xffff_ffff, find_image(body@, i as int) == target,
            target == find_image(body@, i0 as int),
        decreases body@.len() - i,
    {
        let (cc, a, e) = match chunk_at_x(body, i) { None => return None, Some(x) => x };
        proof { lemma_fourccs(); }
        if cc == 0x4c38_5056 || cc == 0x2038_5056 {
            return Some((cc, a, e));
        }
        let pe = if e % 2 == 1 { e + 1 } else { e };
        if pe > body.len() || pe <= i {
            return None;
        }
        i = pe;
    }
}

pub proof fn lemma_fourccs()
    ensures cc_riff() == 0x4646_4952, cc_webp() == 0x5042_4557, cc_vp8l() == 0x4c38_5056,
        cc_vp8() == 0x2038_5056, cc_vp8x() == 0x5838_5056,
{
}

/// `still`: the image of a VP8L bitstream, of the canvas's size if `cw` is
/// not 0.
fn still_x(bs: &[u8], cw: u64, ch: u64, max_pixels: u64) -> (r: Result<WebpX, Error>)
    requires bs@.len() <= 0xffff_ffff,
    ensures
        match r {
            Ok(x) => still(bs@, cw as nat, ch as nat) == Some(webp_view(&x)),
            Err(Error::Bad) => still(bs@, cw as nat, ch as nat) is None,
            Err(Error::TooBig) => true,
        },
{
    match vp8l_x(bs, max_pixels) {
        Err(e) => Err(e),
        Ok((img, _bits, st)) => {
            if cw != 0 && (img.w as u64 != cw || img.h as u64 != ch) {
                Err(Error::Bad)
            } else {
                Ok(WebpX::Still { img, strict: st })
            }
        },
    }
}

/// `extended`.
fn extended_x(body: &[u8], a: usize, e: usize, max_pixels: u64) -> (r: Result<(WebpX, bool), Error>)
    requires body@.len() <= 0xffff_ffff, a + 10 <= e <= body@.len(),
    ensures
        match r {
            Ok((x, lib)) => extended(body@, a as int, e as int) == Some((webp_view(&x), lib)),
            Err(Error::Bad) => extended(body@, a as int, e as int) is None,
            Err(Error::TooBig) => true,
        },
{
    proof { lemma_fourccs(); }
    let flags = body[a];
    let cw = le24_x(body, a + 4) + 1;
    let ch = le24_x(body, a + 7) + 1;
    let lib_x = e - a == 10;
    proof { assert(cw * ch <= 0x100_0000 * 0x100_0000) by (nonlinear_arith) requires cw <= 0x100_0000, ch <= 0x100_0000; }
    if cw * ch > 0xffff_ffff {
        return Err(Error::Bad);
    }
    if flags & 2 == 2 {
        return Ok((WebpX::Animated, lib_x));
    }
    let pe = if e % 2 == 1 { e + 1 } else { e };
    let (cc2, a2, e2) = match find_image_x(body, pe) { None => return Err(Error::Bad), Some(x) => x };
    if cc2 == 0x2038_5056 {
        return Ok((WebpX::Lossy, lib_x));
    }
    let bs = vstd::slice::slice_subrange(body, a2, e2);
    let r = still_x(bs, cw, ch, max_pixels)?;
    let pe2 = if e2 % 2 == 1 { e2 + 1 } else { e2 };
    Ok((r, lib_x && pe2 <= body.len()))
}

/// `webp_body`.
fn webp_body_x(body: &[u8], max_pixels: u64) -> (r: Result<(WebpX, bool), Error>)
    requires body@.len() <= 0xffff_ffff,
    ensures
        match r {
            Ok((x, lib)) => webp_body(body@) == Some((webp_view(&x), lib)),
            Err(Error::Bad) => webp_body(body@) is None,
            Err(Error::TooBig) => true,
        },
{
    proof { lemma_fourccs(); }
    let (cc, a, e) = match chunk_at_x(body, 0) { None => return Err(Error::Bad), Some(x) => x };
    if cc == 0x4c38_5056 {
        let bs = vstd::slice::slice_subrange(body, a, e);
        let r = still_x(bs, 0, 0, max_pixels)?;
        return Ok((r, true));
    }
    if cc == 0x2038_5056 {
        return Ok((WebpX::Lossy, true));
    }
    if cc != 0x5838_5056 || e - a < 10 {
        return Err(Error::Bad);
    }
    extended_x(body, a, e, max_pixels)
}

/// A WebP file: its still lossless image (of at most `max_pixels` pixels),
/// or that it is lossy or animated, and whether libwebp's container
/// parsing takes it too. `TooBig` says only that the image was not decoded.
pub fn webp_x(f: &[u8], max_pixels: u64) -> (r: Result<(WebpX, bool), Error>)
    ensures
        match r {
            Ok((x, lib)) => webp(f@) == Some((webp_view(&x), lib)),
            Err(Error::Bad) => webp(f@) is None,
            Err(Error::TooBig) => true,
        },
{
    proof { lemma_fourccs(); }
    if f.len() < 12 || le32_x(f, 0) != 0x4646_4952 || le32_x(f, 8) != 0x5042_4557 {
        return Err(Error::Bad);
    }
    let rs = le32_x(f, 4);
    if rs < 12 || rs > 0xffff_fff6 || rs as usize > f.len() - 8 {
        return Err(Error::Bad);
    }
    let body = vstd::slice::slice_subrange(f, 12, 8 + rs as usize);
    webp_body_x(body, max_pixels)
}

} // verus!
