//! The WebP container (RFC 9649 section 2) for still lossless images, as a
//! spec over the file's bytes.
//!
//! `webp(f)` is what the file holds: a still lossless image (the VP8L
//! bitstream of its image chunk, decoded by `spec::vp8l`), or a lossy or an
//! animated image (outside this decoder), or nothing (invalid); with a flag
//! `lib`, false where libwebp 1.6.0's container parsing (`WebPDecode`,
//! `src/dec/webp_dec.c`) refuses a file the spec takes.
//!
//! * The file begins with `RIFF`, File Size, `WEBP` ("MUST"); File Size is
//!   at least 12 (a chunk header after `WEBP`) and at most 2^32 - 10, and the
//!   file holds all of it. Data after it is ignored ("Readers MAY parse such
//!   files, ignoring the trailing data").
//! * Every chunk's payload is its Chunk Size bytes, inside the RIFF data; an
//!   odd-sized chunk is followed by a padding byte, which the next chunk
//!   comes after. The image chunk's bitstream is its payload and no more:
//!   libwebp's VP8L decoder reads on past it (into the padding byte, later
//!   chunks and bytes after the RIFF), which the spec does not
//!   (difftest/webp/README.md).
//! * Simple format (2.6): the first chunk is `VP8L`. Nothing after the image
//!   chunk is looked at, here or in the extended format (as libwebp).
//! * Extended format (2.7): the first chunk is `VP8X`, of at least 10 bytes
//!   ("Future specifications may add more fields. Unknown fields MUST be
//!   ignored"; libwebp refuses any size but 10: `lib` is false). Its
//!   reserved bits are ignored ("Readers MUST ignore"). The canvas is at most
//!   2^32 - 1 pixels ("MUST"). With the Animation flag, the file is an
//!   animation. Otherwise the chunks after it up to the first `VP8 ` or
//!   `VP8L` are skipped, whatever they are (ICCP, ALPH, metadata, unknown):
//!   the RFC says readers "SHOULD fail" on reconstruction chunks out of
//!   order, and libwebp does not. The VP8L image must be the canvas's size
//!   (LIBWEBP: "Validates image size coherency"; the RFC assumes it). An
//!   ALPH chunk before a VP8L one is ignored ("SHOULD NOT contain"; the
//!   VP8L bitstream has its own alpha). libwebp also requires an odd-sized
//!   image chunk's padding byte inside the RIFF here: `lib` is false when
//!   it is not.
//! * A first chunk of any other type is invalid (libwebp reads the bytes
//!   from that chunk header on as a raw bitstream).
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::lsb::lbits;
use crate::spec::*;

verus! {

/// A little-endian uint32 at byte `i`.
pub open spec fn le32(f: Seq<u8>, i: int) -> nat {
    f[i] as nat + 256 * f[i + 1] as nat + 65536 * f[i + 2] as nat + 16777216 * f[i + 3] as nat
}

/// A little-endian uint24 at byte `i`.
pub open spec fn le24(f: Seq<u8>, i: int) -> nat {
    f[i] as nat + 256 * f[i + 1] as nat + 65536 * f[i + 2] as nat
}

/// FourCCs as little-endian uint32s.
pub open spec fn fourcc(a: u8, b: u8, c: u8, d: u8) -> nat {
    a as nat + 256 * b as nat + 65536 * c as nat + 16777216 * d as nat
}
pub open spec fn cc_riff() -> nat { fourcc(0x52, 0x49, 0x46, 0x46) }  // "RIFF"
pub open spec fn cc_webp() -> nat { fourcc(0x57, 0x45, 0x42, 0x50) }  // "WEBP"
pub open spec fn cc_vp8l() -> nat { fourcc(0x56, 0x50, 0x38, 0x4c) }  // "VP8L"
pub open spec fn cc_vp8() -> nat { fourcc(0x56, 0x50, 0x38, 0x20) }   // "VP8 "
pub open spec fn cc_vp8x() -> nat { fourcc(0x56, 0x50, 0x38, 0x58) }  // "VP8X"

pub enum Webp {
    Still { img: Image, strict: bool },
    Lossy,
    Animated,
}

/// The payload of the chunk whose header is at `i` of `body`, if the header
/// and payload are inside `body`: its FourCC, and where the payload starts
/// and ends.
pub open spec fn chunk_at(body: Seq<u8>, i: int) -> Option<(nat, int, int)> {
    if i < 0 || i + 8 > body.len() {
        None
    } else {
        let size = le32(body, i + 4);
        if i + 8 + size > body.len() { None } else { Some((le32(body, i), i + 8, i + 8 + size)) }
    }
}

/// The payload's end, and the padding byte of an odd-sized one.
pub open spec fn padded(end: int) -> int { if end % 2 == 1 { end + 1 } else { end } }

/// The image chunk of an extended file, from the chunk at `i` on: the first
/// `VP8 ` or `VP8L`, skipping every other chunk with its padding.
pub open spec fn find_image(body: Seq<u8>, i: int) -> Option<(nat, int, int)>
    decreases body.len() - i,
{
    match chunk_at(body, i) {
        None => None,
        Some((cc, a, e)) =>
            if cc == cc_vp8l() || cc == cc_vp8() {
                Some((cc, a, e))
            } else if padded(e) > body.len() || padded(e) <= i {
                None
            } else {
                find_image(body, padded(e))
            },
    }
}

/// The still image of a VP8L bitstream, if it is `cw` x `ch` (or any size
/// when `cw` is 0).
pub open spec fn still(bs: Seq<u8>, cw: nat, ch: nat) -> Option<Webp> {
    match vp8l(lbits(bs)) {
        None => None,
        Some((img, _bits, st)) =>
            if cw != 0 && (img.w != cw || img.h != ch) { None } else { Some(Webp::Still { img, strict: st }) },
    }
}

/// An extended file (2.7), whose VP8X payload is `body[a..e]`.
pub open spec fn extended(body: Seq<u8>, a: int, e: int) -> Option<(Webp, bool)> {
    let flags = body[a];
    let cw = le24(body, a + 4) + 1;
    let ch = le24(body, a + 7) + 1;
    let lib_x = e - a == 10;
    if cw * ch > 0xffff_ffff {
        None
    } else if flags & 2 == 2 {
        Some((Webp::Animated, lib_x))
    } else {
        match find_image(body, padded(e)) {
            None => None,
            Some((cc2, a2, e2)) =>
                if cc2 == cc_vp8() {
                    Some((Webp::Lossy, lib_x))
                } else {
                    match still(body.subrange(a2, e2), cw, ch) {
                        None => None,
                        Some(r) => Some((r, lib_x && padded(e2) <= body.len())),
                    }
                },
        }
    }
}

/// The RIFF data after `WEBP`: its chunks.
pub open spec fn webp_body(body: Seq<u8>) -> Option<(Webp, bool)> {
    match chunk_at(body, 0) {
        None => None,
        Some((cc, a, e)) =>
            if cc == cc_vp8l() {
                match still(body.subrange(a, e), 0, 0) {
                    None => None,
                    Some(r) => Some((r, true)),
                }
            } else if cc == cc_vp8() {
                Some((Webp::Lossy, true))
            } else if cc != cc_vp8x() || e - a < 10 {
                None
            } else {
                extended(body, a, e)
            },
    }
}

/// A WebP file: what it holds, and whether libwebp's container parsing
/// also takes it.
pub open spec fn webp(f: Seq<u8>) -> Option<(Webp, bool)> {
    if f.len() < 12 || le32(f, 0) != cc_riff() || le32(f, 8) != cc_webp() {
        None
    } else {
        let rs = le32(f, 4);
        if rs < 12 || rs > 0xffff_fff6 || 8 + rs > f.len() {
            None
        } else {
            webp_body(f.subrange(12, 8 + rs as int))
        }
    }
}

} // verus!
