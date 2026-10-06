//! The executable spec for lossy WebP files (RFC 9649 section 2): the
//! container around a VP8 key frame (`vp8spec`), and the ALPH chunk's alpha.
//!
//! The container rules are cspec.rs's (the verified container spec for
//! still lossless images), carried over to lossy images:
//!
//! * Simple format (2.5): the first chunk is `VP8 `; its payload is the
//!   frame. No alpha.
//! * Extended format (2.7): the first chunk is `VP8X` (at least 10 bytes;
//!   libwebp takes only 10: `lib` false otherwise), not animated. The chunks
//!   after it up to the first `VP8 ` or `VP8L` are skipped whatever they
//!   are, except that the last `ALPH` among them is the image's alpha (as
//!   libwebp: ParseOptionalChunks keeps the last one; the RFC allows one).
//!   The frame must be the canvas's size. The Alpha flag of VP8X is not
//!   looked at: an ALPH chunk gives alpha either way (as libwebp).
//! * An ALPH chunk that does not decode makes the file invalid (libwebp:
//!   "Could not decode alpha data").
//!
//! The frame is the image chunk's payload and no more. libwebp's VP8
//! decoder reads on past it, into the padding byte, later chunks and bytes
//! after the RIFF (difftest/webp/README.md): where the frame's `lib` flag is
//! set that changes nothing, since libwebp then stops inside the frame.
use crate::specdec::{self, Bits};
use crate::vp8spec::{self, Frame};

pub struct Lossy {
    pub frame: Frame,
    /// The alpha plane (`frame.w` x `frame.h`), if the file has an ALPH chunk.
    pub alpha: Option<Vec<u8>>,
    /// libwebp decodes the file to the same planes.
    pub lib: bool,
}

pub enum File {
    Lossy(Lossy),
    /// A still lossless or an animated image (not this decoder's).
    Other,
}

fn le32(f: &[u8], i: usize) -> u64 {
    u32::from_le_bytes([f[i], f[i + 1], f[i + 2], f[i + 3]]) as u64
}

fn le24(f: &[u8], i: usize) -> u64 {
    f[i] as u64 | (f[i + 1] as u64) << 8 | (f[i + 2] as u64) << 16
}

/// cspec::chunk_at: the chunk at `i` of `body`, if its header and payload
/// are inside: its FourCC, and where its payload starts and ends.
fn chunk_at(body: &[u8], i: usize) -> Option<(&[u8], usize, usize)> {
    if i + 8 > body.len() {
        return None;
    }
    let size = le32(body, i + 4) as usize;
    if i + 8 + size > body.len() {
        return None;
    }
    Some((&body[i..i + 4], i + 8, i + 8 + size))
}

fn padded(end: usize) -> usize {
    end + (end & 1)
}

/// The frame of an image chunk, with the alpha chunk's payload if any,
/// decoded; the frame must be `cw` x `ch` unless `cw` is 0.
fn image(frame: &[u8], alph: Option<&[u8]>, cw: u64, ch: u64, lib: bool) -> Option<File> {
    let (f, flib, _) = vp8spec::vp8_lib(frame)?;
    if cw != 0 && (f.w as u64 != cw || f.h as u64 != ch) {
        return None;
    }
    let (alpha, alib) = match alph {
        None => (None, true),
        Some(d) => {
            let (a, l) = alpha(d, f.w, f.h)?;
            (Some(a), l)
        }
    };
    Some(File::Lossy(Lossy { frame: f, alpha, lib: lib && flib && alib }))
}

/// cspec::extended, for a VP8X payload at `body[a..e]`.
fn extended(body: &[u8], a: usize, e: usize) -> Option<File> {
    let flags = body[a];
    let cw = le24(body, a + 4) + 1;
    let ch = le24(body, a + 7) + 1;
    let lib_x = e - a == 10;
    if cw * ch > 0xffff_ffff {
        return None;
    }
    if flags & 2 == 2 {
        return Some(File::Other);
    }
    let mut i = padded(e);
    let mut alph = None;
    loop {
        let (cc, a2, e2) = chunk_at(body, i)?;
        match cc {
            b"VP8L" => return Some(File::Other),
            b"VP8 " => return image(&body[a2..e2], alph, cw, ch, lib_x && padded(e2) <= body.len()),
            _ => {
                if cc == b"ALPH" {
                    alph = Some(&body[a2..e2]);
                }
                if padded(e2) > body.len() || padded(e2) <= i {
                    return None;
                }
                i = padded(e2);
            }
        }
    }
}

/// A WebP file (cspec::webp): a lossy image, another kind, or nothing.
pub fn webp(f: &[u8]) -> Option<File> {
    if f.len() < 12 || &f[0..4] != b"RIFF" || &f[8..12] != b"WEBP" {
        return None;
    }
    let rs = le32(f, 4);
    if rs < 12 || rs > 0xffff_fff6 || 8 + rs > f.len() as u64 {
        return None;
    }
    let body = &f[12..8 + rs as usize];
    let (cc, a, e) = chunk_at(body, 0)?;
    match cc {
        b"VP8L" => Some(File::Other),
        b"VP8 " => image(&body[a..e], None, 0, 0, true),
        b"VP8X" if e - a >= 10 => extended(body, a, e),
        _ => None,
    }
}

/// An ALPH chunk's payload (RFC 9649 2.7.1.2) for a `w` x `h` image: the
/// alpha plane, and whether libwebp decodes it the same (ALPHInit also
/// refuses reserved bits set and preprocessing values past 1, which the RFC
/// says to ignore; and the lossless stream's own strict flag).
pub fn alpha(d: &[u8], w: usize, h: usize) -> Option<(Vec<u8>, bool)> {
    let hdr = *d.first()?;
    let method = hdr & 3;
    let filter = (hdr >> 2) & 3;
    let pre = (hdr >> 4) & 3;
    let rsv = hdr >> 6;
    let mut lib = rsv == 0 && pre <= 1;
    let x: Vec<u8> = match method {
        // Raw: width x height bytes; any more are not looked at.
        0 => d.get(1..1 + w * h)?.to_vec(),
        // Lossless: an image-stream of the image's size; alpha is green.
        1 => {
            let (px, _, strict) = specdec::image_stream(&Bits { buf: &d[1..] }, 0, w as u64, h as u64)?;
            lib &= strict;
            px.iter().map(|&c| (c >> 8) as u8).collect()
        }
        _ => return None,
    };
    Some((unfilter(filter, &x, w, h), lib))
}

/// Undo an alpha filter: each value is its predictor plus the stored value,
/// modulo 256. Predictors: 0 none; 1 horizontal (A, the left); 2 vertical
/// (B, above); 3 gradient (clip(A + B - C)). The top left value's is 0; on
/// the left edge the horizontal and gradient filters use B, on the top edge
/// the vertical and gradient ones use A.
fn unfilter(method: u8, x: &[u8], w: usize, h: usize) -> Vec<u8> {
    let mut out = vec![0u8; w * h];
    for y in 0..h {
        for i in 0..w {
            let a = |o: &Vec<u8>| o[y * w + i - 1] as i32;
            let b = |o: &Vec<u8>| o[(y - 1) * w + i] as i32;
            let pred = if method == 0 || (i == 0 && y == 0) {
                0
            } else if i == 0 {
                b(&out) // left edge: above (methods 1, 2, 3)
            } else if y == 0 {
                a(&out) // top edge: left (methods 1, 2, 3)
            } else {
                match method {
                    1 => a(&out),
                    2 => b(&out),
                    _ => (a(&out) + b(&out) - out[(y - 1) * w + i - 1] as i32).clamp(0, 255),
                }
            };
            out[y * w + i] = (pred + x[y * w + i] as i32) as u8;
        }
    }
    out
}
