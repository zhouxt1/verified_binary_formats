//! Animated WebP (RFC 9649 2.7.1.1, 2.7.2) for lossless frames, as a spec
//! over the file's bytes: the ANIM and ANMF chunks, and the canvases a
//! reader shows, one per frame, with their timestamps.
//!
//! The RFC's canvas assembly is not exact (the background color "MAY" be
//! used; blending "SHOULD be done in linear color space"), so the canvases
//! are those of libwebp 1.6.0's WebPAnimDecoder (`src/demux/anim_decode.c`),
//! and each such place says `LIBWEBP:`:
//!
//! * the canvas starts transparent (0), and disposal clears the frame's
//!   rectangle to transparent; the ANIM background color is reported, not
//!   used;
//! * a frame is a key frame (drawn on a transparent canvas, not blended) if
//!   it is the first; or it covers the canvas and has no alpha (its VP8L
//!   alpha hint is 0) or does not blend; or the previous frame was disposed
//!   and covered the canvas or was itself a key frame;
//! * other frames are drawn on the previous canvas as disposed, and those
//!   that blend blend each pixel whose alpha is not 255 over the pixel
//!   before, with libwebp's integer formula (`blend`), except inside the
//!   previous frame's rectangle when that frame was disposed;
//! * a frame's size is its bitstream's (the ANMF's width and height are
//!   only checked to have an area below 2^32).
//!
//! The file is the extended format with the Animation flag (`cspec`), and:
//! every chunk fits the RIFF data, padding included; ANIM, of at least 6
//! bytes, comes before the first ANMF (the first ANIM counts); no VP8X
//! again and no ALPH, VP8 or VP8L outside an ANMF; an ANMF of at least 16
//! bytes, whose payload is chunks: an optional ALPH, then VP8 or VP8L (not
//! VP8L after ALPH: "SHOULD NOT"; libwebp refuses), then any; the frame
//! inside the canvas; at least one frame. A VP8 frame makes the file lossy
//! (not decoded here). The flag `lib` is false where libwebp refuses a
//! file the RFC allows: a VP8X of other than 10 bytes, VP8X reserved bits
//! set ("Readers MUST ignore"; libwebp's demuxer refuses them).
//!
//! libwebp takes more than this (difftest/webp/README.md): an ANMF's size
//! is not used past its image chunks, a frame's VP8L chunk and a 5-byte
//! ANIM are read into their padding bytes, and an ANMF without a bitstream
//! chunk is dropped.
//!
//! `difftest/webp/animmodel.py` is this spec, executable, checked against
//! WebPAnimDecoder before this was written.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::lsb::lbits;
use crate::cspec::*;
use crate::spec::*;

verus! {

pub open spec fn cc_anim() -> nat { fourcc(0x41, 0x4e, 0x49, 0x4d) }  // "ANIM"
pub open spec fn cc_anmf() -> nat { fourcc(0x41, 0x4e, 0x4d, 0x46) }  // "ANMF"
pub open spec fn cc_alph() -> nat { fourcc(0x41, 0x4c, 0x50, 0x48) }  // "ALPH"

/// A little-endian uint16 at byte `i`.
pub open spec fn le16(f: Seq<u8>, i: int) -> nat { f[i] as nat + 256 * f[i + 1] as nat }

/// Every chunk from `i` to `end` fits, payload and padding.
pub open spec fn fits(body: Seq<u8>, i: int, end: int) -> bool
    decreases end - i,
{
    if i >= end {
        i == end
    } else if i + 8 > end {
        false
    } else {
        let nxt = padded(i + 8 + le32(body, i + 4));
        nxt <= end && fits(body, nxt, end)
    }
}

/// The chunk after the one at `i` (with its padding).
pub open spec fn next_chunk(body: Seq<u8>, i: int) -> int { padded(i + 8 + le32(body, i + 4)) }

/// A frame, decoded, where it goes and how.
pub struct AFrame {
    pub x: nat,
    pub y: nat,
    pub img: Image,
    pub dur: nat,
    pub dispose_bg: bool,
    pub no_blend: bool,
}

/// An ANMF's payload `body[a..e]` (e its padded end): the frame, `None`
/// if invalid, or `Some(None)` if its bitstream is lossy.
pub open spec fn frame_at(body: Seq<u8>, a: int, e: int, pe: int, cw: nat, ch: nat) -> Option<Option<AFrame>> {
    if e - a < 16 {
        None
    } else {
        let fx = 2 * le24(body, a);
        let fy = 2 * le24(body, a + 3);
        let fw = le24(body, a + 6) + 1;
        let fh = le24(body, a + 9) + 1;
        let dur = le24(body, a + 12);
        let bits = body[a + 15];
        if fw * fh > 0xffff_ffff || !fits(body, a + 16, pe) || a + 16 >= pe {
            None
        } else {
            frame_img(body, a + 16, pe, fx, fy, dur, bits, cw, ch)
        }
    }
}

/// The chunks of an ANMF's frame data, `body[s..pe]` (which fit): an
/// optional ALPH, then the bitstream chunk.
pub open spec fn frame_img(body: Seq<u8>, s: int, pe: int, fx: nat, fy: nat, dur: nat, bits: u8, cw: nat, ch: nat)
    -> Option<Option<AFrame>>
{
    let k = if le32(body, s) == cc_alph() { next_chunk(body, s) } else { s };
    if k >= pe {
        None
    } else if k != s && le32(body, k) == cc_vp8l() {
        None
    } else if le32(body, k) == cc_vp8() {
        Some(None)
    } else if le32(body, k) != cc_vp8l() {
        None  // no bitstream chunk
    } else {
        frame_of(body.subrange(k + 8, k + 8 + le32(body, k + 4)), fx, fy, dur, bits, cw, ch)
    }
}

/// The frame of a VP8L bitstream `bs`, placed at (fx, fy) on the canvas.
pub open spec fn frame_of(bs: Seq<u8>, fx: nat, fy: nat, dur: nat, bits: u8, cw: nat, ch: nat) -> Option<Option<AFrame>> {
    match vp8l(lbits(bs)) {
        None => None,
        Some((img, _bits, _st)) =>
            if fx + img.w > cw || fy + img.h > ch {
                None
            } else {
                Some(Some(AFrame { x: fx, y: fy, img, dur, dispose_bg: bits & 1 == 1, no_blend: bits & 2 == 2 }))
            },
    }
}

/// What the chunks so far give: the ANIM's background and loop count, if
/// one was seen, and the frames.
pub struct PSt {
    pub anim: Option<(nat, nat)>,
    pub frames: Seq<AFrame>,
}

pub enum Parsed {
    Frames(PSt),
    Lossy,
}

/// The chunks from `i` (all of which fit) to `end`, after the VP8X.
pub open spec fn top_chunks(body: Seq<u8>, i: int, end: int, cw: nat, ch: nat, st: PSt) -> Option<Parsed>
    decreases end - i,
{
    if i >= end || i + 8 > end {
        Some(Parsed::Frames(st))
    } else {
        let tag = le32(body, i);
        let a = i + 8;
        let e = a + le32(body, i + 4);
        let nxt = padded(e);
        if nxt <= i || nxt > end {
            None  // not reached: the chunks fit
        } else if tag == cc_vp8x() || tag == cc_alph() || tag == cc_vp8() || tag == cc_vp8l() {
            None
        } else if tag == cc_anim() {
            if e - a < 6 {
                None
            } else {
                let st2 = if st.anim is None { PSt { anim: Some((le32(body, a), le16(body, a + 4))), ..st } } else { st };
                top_chunks(body, nxt, end, cw, ch, st2)
            }
        } else if tag == cc_anmf() {
            if st.anim is None {
                None
            } else {
                match frame_at(body, a, e, nxt, cw, ch) {
                    None => None,
                    Some(None) => Some(Parsed::Lossy),
                    Some(Some(fr)) => top_chunks(body, nxt, end, cw, ch, PSt { frames: st.frames.push(fr), ..st }),
                }
            }
        } else {
            top_chunks(body, nxt, end, cw, ch, st)
        }
    }
}

// ------------------------------------------------------ canvas assembly

/// Pixel `i` of a canvas `cw` wide is inside the frame's rectangle.
pub open spec fn in_rect(fr: AFrame, cw: nat, i: int) -> bool {
    let x = i % (cw as int);
    let y = i / (cw as int);
    fr.x <= x < fr.x + fr.img.w && fr.y <= y < fr.y + fr.img.h
}

/// The frame's pixel at canvas pixel `i` (inside its rectangle).
pub open spec fn frame_px(fr: AFrame, cw: nat, i: int) -> u32 {
    let x = i % (cw as int);
    let y = i / (cw as int);
    fr.img.px[(y - fr.y) * fr.img.w + (x - fr.x)]
}

/// LIBWEBP: `BlendPixelNonPremult`, `src` over `dst`, not premultiplied.
pub open spec fn blend_ch(sc: int, sa: int, dc: int, dfa: int, scale: int) -> int {
    (((sc * sa + dc * dfa) * scale) % 0x1_0000_0000) / 0x100_0000
}

pub open spec fn blend(src: u32, dst: u32) -> u32 {
    let sa = alpha(src);
    if sa == 0 {
        dst
    } else {
        let dfa = (alpha(dst) * (256 - sa)) / 256;
        let ba = sa + dfa;
        let scale = 0x100_0000int / ba;
        argb(ba, blend_ch(red(src), sa, red(dst), dfa, scale), blend_ch(green(src), sa, green(dst), dfa, scale),
             blend_ch(blue(src), sa, blue(dst), dfa, scale))
    }
}

/// LIBWEBP: `IsKeyFrame`.
pub open spec fn is_key(fr: AFrame, k: int, prev: AFrame, prev_key: bool, cw: nat, ch: nat) -> bool {
    let full = fr.img.w == cw && fr.img.h == ch;
    let prev_full = prev.img.w == cw && prev.img.h == ch;
    k == 0 || ((!fr.img.alpha_hint || fr.no_blend) && full) || (prev.dispose_bg && (prev_full || prev_key))
}

/// The canvas after drawing frame `k`, from the previous one as disposed.
pub open spec fn draw(fr: AFrame, k: int, prev: AFrame, key: bool, cw: nat, ch: nat, disposed: Seq<u32>)
    -> Seq<u32>
{
    Seq::new(cw * ch, |i: int|
        if in_rect(fr, cw, i) {
            let s = frame_px(fr, cw, i);
            if k > 0 && !fr.no_blend && !key && !(prev.dispose_bg && in_rect(prev, cw, i)) && alpha(s) != 255 {
                blend(s, disposed[i])
            } else {
                s
            }
        } else if key {
            0u32
        } else {
            disposed[i]
        })
}

/// The canvas after `fr`'s disposal.
pub open spec fn dispose(fr: AFrame, cw: nat, canvas: Seq<u32>) -> Seq<u32> {
    if fr.dispose_bg { Seq::new(canvas.len(), |i: int| if in_rect(fr, cw, i) { 0u32 } else { canvas[i] }) } else { canvas }
}

/// The canvases from frame `k` on, with their timestamps (the sum of the
/// durations so far).
pub open spec fn compose(frames: Seq<AFrame>, k: int, cw: nat, ch: nat, disposed: Seq<u32>, prev_key: bool, ts: nat,
                         out: Seq<(nat, Seq<u32>)>) -> Seq<(nat, Seq<u32>)>
    decreases frames.len() - k,
{
    if k < 0 || k >= frames.len() {
        out
    } else {
        let fr = frames[k];
        let prev = if k > 0 { frames[k - 1] } else { fr };
        let key = is_key(fr, k, prev, prev_key, cw, ch);
        let canvas = draw(fr, k, prev, key, cw, ch, disposed);
        compose(frames, k + 1, cw, ch, dispose(fr, cw, canvas), key, ts + fr.dur, out.push((ts + fr.dur, canvas)))
    }
}

pub struct Anim {
    pub cw: nat,
    pub ch: nat,
    pub bg: nat,
    pub loops: nat,
    pub frames: Seq<(nat, Seq<u32>)>,
}

pub enum AnimR {
    Anim { a: Anim, lib: bool },
    Lossy,
}

/// An extended file's animation, the VP8X payload at `body[a..e]` (with the
/// Animation flag).
pub open spec fn animation(body: Seq<u8>, a: int, e: int) -> Option<AnimR> {
    let flags = body[a];
    let cw = le24(body, a + 4) + 1;
    let ch = le24(body, a + 7) + 1;
    let lib = e - a == 10 && flags & 0xc1 == 0;
    if cw * ch > 0xffff_ffff || flags & 2 != 2 || !fits(body, padded(e), body.len() as int) {
        None
    } else {
        match top_chunks(body, padded(e), body.len() as int, cw, ch, PSt { anim: None, frames: Seq::empty() }) {
            None => None,
            Some(Parsed::Lossy) => Some(AnimR::Lossy),
            Some(Parsed::Frames(st)) => match st.anim {
                None => None,
                Some((bg, loops)) =>
                    if st.frames.len() == 0 {
                        None
                    } else {
                        let zero = Seq::new(cw * ch, |_i: int| 0u32);
                        Some(AnimR::Anim {
                            a: Anim { cw, ch, bg, loops, frames: compose(st.frames, 0, cw, ch, zero, false, 0, Seq::empty()) },
                            lib,
                        })
                    },
            },
        }
    }
}

/// An animated WebP file.
pub open spec fn webp_anim(f: Seq<u8>) -> Option<AnimR> {
    if f.len() < 12 || le32(f, 0) != cc_riff() || le32(f, 8) != cc_webp() {
        None
    } else {
        let rs = le32(f, 4);
        if rs < 12 || rs > 0xffff_fff6 || 8 + rs > f.len() {
            None
        } else {
            let body = f.subrange(12, 8 + rs as int);
            match chunk_at(body, 0) {
                None => None,
                Some((cc, a, e)) => if cc != cc_vp8x() || e - a < 10 { None } else { animation(body, a, e) },
            }
        }
    }
}

} // verus!
