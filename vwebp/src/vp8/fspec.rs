//! Lossy WebP files (RFC 9649 section 2) as a spec: the container around a
//! VP8 key frame (`spec::vp8`) and the ALPH chunk's alpha.
//!
//! The container rules are `cspec`'s (the still lossless images'), carried
//! over to lossy images, as the executable `vwebp-tool/src/lossy.rs` has
//! them (tested against libwebp by difftest/webp/lfile.py):
//!
//! * Simple format (2.5): the first chunk is `VP8 `; its payload is the
//!   frame. No alpha.
//! * Extended format (2.7): the first chunk is `VP8X`, not animated; the
//!   chunks after it up to the first `VP8 ` or `VP8L` are skipped
//!   (`cspec::find_image`) except that the last `ALPH` among them is the
//!   image's alpha (as libwebp's ParseOptionalChunks). The frame must be
//!   the canvas's size. The Alpha flag of VP8X is not looked at.
//! * An ALPH chunk that does not decode makes the file invalid.
//!
//! `lib` is `cspec`'s container flag, and libwebp's ALPH checks: it also
//! refuses reserved bits set and preprocessing past 1 (the RFC: "MUST
//! ignore"), and the lossless alpha stream's `strict`. It does not include
//! the frame's own `lib` flag (vwebp-tool's `vp8spec::Notes`, not verified).
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::lsb::lbits;
use crate::cspec::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::spec::{read_transforms, spatially_coded_image, inverses, green};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use super::spec::vp8;
use super::spec::Frame;

verus! {

pub open spec fn cc_alph() -> nat { fourcc(0x41, 0x4c, 0x50, 0x48) }  // "ALPH"

/// The payload of the last ALPH chunk among those from `i` up to `stop`
/// (the image chunk's header), or `acc` if there is none.
pub open spec fn last_alph(body: Seq<u8>, i: int, stop: int, acc: Option<Seq<u8>>) -> Option<Seq<u8>>
    decreases stop - i,
{
    if i >= stop {
        acc
    } else {
        match chunk_at(body, i) {
            None => acc,
            Some((cc, a, e)) => {
                let acc2 = if cc == cc_alph() { Some(body.subrange(a, e)) } else { acc };
                if padded(e) <= i || padded(e) > stop { acc2 } else { last_alph(body, padded(e), stop, acc2) }
            },
        }
    }
}

pub open spec fn clamp8(v: int) -> int { if v < 0 { 0 } else if v > 255 { 255 } else { v } }

/// Undo an alpha filter (RFC 9649 2.7.1.2), value by value from
/// `out.len()`: each is its predictor plus the stored value, mod 256.
/// Predictors: 0 none; 1 horizontal (A, the left); 2 vertical (B, above); 3
/// gradient (clip(A + B - C)). The top left value's is 0; on the left edge
/// the horizontal and gradient filters use B, on the top edge the vertical
/// and gradient ones use A.
pub open spec fn unfilter(method: nat, x: Seq<u8>, w: nat, out: Seq<u8>) -> Seq<u8>
    decreases x.len() - out.len(),
{
    if out.len() >= x.len() || w == 0 {
        out
    } else {
        let i = out.len() as int;
        let c = i % (w as int);
        let r = i / (w as int);
        let pred: int = if method == 0 || i == 0 { 0 }
            else if c == 0 { out[i - w] as int }
            else if r == 0 { out[i - 1] as int }
            else if method == 1 { out[i - 1] as int }
            else if method == 2 { out[i - w] as int }
            else { clamp8(out[i - 1] as int + out[i - w] as int - out[i - w - 1] as int) };
        unfilter(method, x, w, out.push(((pred + x[i] as int) % 256) as u8))
    }
}

/// An ALPH chunk's payload for a `w` x `h` image: the alpha plane, and
/// libwebp's agreement. Raw: w x h bytes (any more are not looked at).
/// Lossless: an image-stream of the image's size, alpha in green.
pub open spec fn alph(d: Seq<u8>, w: nat, h: nat) -> Option<(Seq<u8>, bool)> {
    if d.len() < 1 {
        None
    } else {
        let hdr = d[0] as nat;
        let method = hdr % 4;
        let filter = (hdr / 4) % 4;
        let pre = (hdr / 16) % 4;
        let rsv = hdr / 64;
        let x: Option<(Seq<u8>, bool)> = if method == 0 {
            if d.len() - 1 < w * h { None } else { Some((d.subrange(1, (1 + w * h) as int), true)) }
        } else if method == 1 {
            let b = lbits(d.subrange(1, d.len() as int));
            match read_transforms(b, 0, w, h, Seq::empty(), true) {
                None => None,
                Some((ts, dw, p, st)) => match spatially_coded_image(b, p, dw, h) {
                    None => None,
                    Some((px, _q, st2)) => {
                        let full = inverses(ts, ts.len() as int, h, px);
                        Some((Seq::new(w * h, |k: int| green(full[k]) as u8), st && st2))
                    },
                },
            }
        } else {
            None
        };
        match x {
            None => None,
            Some((x, st)) => Some((unfilter(filter, x, w, Seq::empty()), rsv == 0 && pre <= 1 && st)),
        }
    }
}

pub enum Lossy {
    /// A still lossless or an animated image (`cspec::webp` has it).
    NotLossy,
    Image { frame: Frame, alpha: Option<Seq<u8>>, lib: bool },
}

/// The image of a frame, with its alpha chunk's payload if any; the frame
/// must be `cw` x `ch` unless `cw` is 0.
pub open spec fn lossy_image(frame: Seq<u8>, ach: Option<Seq<u8>>, cw: nat, ch: nat, lib: bool) -> Option<Lossy> {
    match vp8(frame) {
        None => None,
        Some(f) =>
            if cw != 0 && (f.w != cw || f.h != ch) {
                None
            } else {
                match ach {
                    None => Some(Lossy::Image { frame: f, alpha: None, lib }),
                    Some(d) => match alph(d, f.w, f.h) {
                        None => None,
                        Some((a, al)) => Some(Lossy::Image { frame: f, alpha: Some(a), lib: lib && al }),
                    },
                }
            },
    }
}

/// An extended file (`cspec::extended`), whose VP8X payload is `body[a..e]`.
pub open spec fn lossy_extended(body: Seq<u8>, a: int, e: int) -> Option<Lossy> {
    let flags = body[a];
    let cw = le24(body, a + 4) + 1;
    let ch = le24(body, a + 7) + 1;
    let lib_x = e - a == 10;
    if cw * ch > 0xffff_ffff {
        None
    } else if flags & 2 == 2 {
        Some(Lossy::NotLossy)
    } else {
        match find_image(body, padded(e)) {
            None => None,
            Some((cc2, a2, e2)) =>
                if cc2 == cc_vp8() {
                    lossy_image(body.subrange(a2, e2), last_alph(body, padded(e), a2 - 8, None), cw, ch,
                                lib_x && padded(e2) <= body.len())
                } else {
                    Some(Lossy::NotLossy)
                },
        }
    }
}

/// The RIFF data after `WEBP` (`cspec::webp_body`).
pub open spec fn lossy_body(body: Seq<u8>) -> Option<Lossy> {
    match chunk_at(body, 0) {
        None => None,
        Some((cc, a, e)) =>
            if cc == cc_vp8l() {
                Some(Lossy::NotLossy)
            } else if cc == cc_vp8() {
                lossy_image(body.subrange(a, e), None, 0, 0, true)
            } else if cc != cc_vp8x() || e - a < 10 {
                None
            } else {
                lossy_extended(body, a, e)
            },
    }
}

/// A WebP file, as a lossy image (`cspec::webp`'s checks).
pub open spec fn webp_lossy(f: Seq<u8>) -> Option<Lossy> {
    if f.len() < 12 || le32(f, 0) != cc_riff() || le32(f, 8) != cc_webp() {
        None
    } else {
        let rs = le32(f, 4);
        if rs < 12 || rs > 0xffff_fff6 || 8 + rs > f.len() {
            None
        } else {
            lossy_body(f.subrange(12, 8 + rs as int))
        }
    }
}

} // verus!
