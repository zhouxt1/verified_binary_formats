//! vwebp-tool: drives the WebP lossless decoders for the differential tests.
//!
//! * `vwebp-tool spec FILE [OUT.pam]`: decode FILE (a WebP file with a VP8L
//!   image, or a bare VP8L bitstream) with the executable spec (`specdec`);
//!   report the size, the bits taken and the strict flag on stderr; write
//!   the image as PAM (RGB_ALPHA) if asked. Exit 1 if the spec has no result.
//! * `vwebp-tool batch-spec`: records on stdin, each a little-endian u32
//!   length and that many bytes (as for `spec`); for each, a record on
//!   stdout: a status byte (0: no result, 1: a result, 2: not a VP8L image),
//!   then for a result the width and height (u32 each), the strict flag
//!   byte, the bits taken (u64) and the pixels as little-endian ARGB u32s.
//!
//! * `vwebp-tool batch`: the same with the verified decoder
//!   (`vwebp::dec::vp8l_x`).
//! * `vwebp-tool batch-file`: whole WebP files through the verified container
//!   decoder (`vwebp::riff::webp_x`); see `batch_file`.
//! * `vwebp-tool batch-anim`: animated WebP files through the verified
//!   animation decoder (`vwebp::anim::webp_anim_x`); see `batch_anim`.
//!
//! * `vwebp-tool batch-vp8-spec`: records as for `batch-spec`, each a bare
//!   VP8 key frame (the payload of a "VP8 " chunk), decoded by the lossy
//!   executable spec (`vp8spec`). For each, on stdout: a status byte (0: no
//!   result, 1: a frame), then for a frame its width and height (u32 each),
//!   the `lib` flag byte, and the Y, U and V planes (Y is width x height, U
//!   and V ((width+1)/2) x ((height+1)/2)), row by row.
//!
//! * `vwebp-tool batch-lossy-file`: records as for `batch-file`, each a
//!   whole WebP file, decoded by the lossy executable spec (`lossy`, with
//!   `vp8spec`). For each, on stdout: a status byte (0: invalid, 1: a lossy
//!   image, 2: lossless or animated, not this decoder's), then for an image
//!   its width and height (u32 each), the `lib` flag byte, an alpha byte (1
//!   if the file has an ALPH chunk), and the Y, U and V planes, then the
//!   alpha plane (width x height) if it has one.
//! * `vwebp-tool batch-vp8`: as `batch-vp8-spec`, with the verified
//!   decoder (`vwebp::vp8::dec::vp8_x`); the `lib` flag is the spec's.
//! * `vwebp-tool vp8-notes`: records as for `batch-vp8-spec`; for each, a
//!   line with the verdict and the spec's notes on libwebp (`vp8spec::Notes`).
//!
//! With VW_LIMIT=N, an image of more than N pixels is no result, checked
//! from the header (as `wdec -n N`). With VW_COVER set, `batch-spec` prints on exit how often each part of
//! the spec ran.
use std::io::{Read, Write};
use std::sync::atomic::Ordering::Relaxed;

mod lossy;
mod specdec;
mod vp8spec;
mod vp8tab;

/// The VP8L bitstream in a file: the file itself unless it starts with
/// "RIFF", else the payload of a simple lossless RIFF file's VP8L chunk,
/// or of the VP8L chunk of an extended file without ALPH, ANIM or VP8.
/// (Not the container spec: just enough to run the bitstream spec on files.)
fn vp8l_payload(f: &[u8]) -> Option<&[u8]> {
    if !f.starts_with(b"RIFF") {
        return Some(f);
    }
    if f.len() < 12 || &f[8..12] != b"WEBP" {
        return None;
    }
    let mut i = 12;
    while i + 8 <= f.len() {
        let tag = &f[i..i + 4];
        let n = u32::from_le_bytes(f[i + 4..i + 8].try_into().unwrap()) as usize;
        let body = &f[i + 8..(i + 8 + n).min(f.len())];
        match tag {
            b"VP8L" => return Some(body),
            b"VP8 " | b"ALPH" | b"ANIM" | b"ANMF" => return None,
            _ => {}
        }
        i += 8 + n + (n & 1);
    }
    None
}

fn write_pam(path: &str, img: &specdec::Image) {
    let mut out = format!(
        "P7\nWIDTH {}\nHEIGHT {}\nDEPTH 4\nMAXVAL 255\nTUPLTYPE RGB_ALPHA\nENDHDR\n",
        img.w, img.h
    )
    .into_bytes();
    for &c in &img.px {
        out.extend_from_slice(&[(c >> 16) as u8, (c >> 8) as u8, c as u8, (c >> 24) as u8]);
    }
    std::fs::write(path, out).expect("write");
}

/// The header says more than `limit` pixels (as `wdec -n`, checked before decoding).
fn too_big(bs: &[u8], limit: u64) -> bool {
    let b = specdec::Bits { buf: bs };
    match (b.getbits(8, 14), b.getbits(22, 14)) {
        (Some(w), Some(h)) => (w + 1) * (h + 1) > limit,
        _ => false,
    }
}

fn batch(mut dec: impl FnMut(&[u8]) -> Option<(specdec::Image, u64, bool)>) {
    let limit: u64 = std::env::var("VW_LIMIT").ok().and_then(|v| v.parse().ok()).unwrap_or(1 << 28);
    let mut inp = std::io::stdin().lock();
    let mut out = std::io::BufWriter::new(std::io::stdout().lock());
    loop {
        let mut len = [0u8; 4];
        if inp.read_exact(&mut len).is_err() {
            break;
        }
        let mut buf = vec![0u8; u32::from_le_bytes(len) as usize];
        inp.read_exact(&mut buf).unwrap();
        match vp8l_payload(&buf) {
            None => out.write_all(&[2]).unwrap(),
            Some(bs) if too_big(bs, limit) => out.write_all(&[0]).unwrap(),
            Some(bs) => match dec(bs) {
                None => out.write_all(&[0]).unwrap(),
                Some((img, bits, strict)) => {
                    out.write_all(&[1]).unwrap();
                    out.write_all(&(img.w as u32).to_le_bytes()).unwrap();
                    out.write_all(&(img.h as u32).to_le_bytes()).unwrap();
                    out.write_all(&[strict as u8]).unwrap();
                    out.write_all(&bits.to_le_bytes()).unwrap();
                    for &c in &img.px {
                        out.write_all(&c.to_le_bytes()).unwrap();
                    }
                }
            },
        }
        out.flush().unwrap();
    }
}

/// `batch-file`: records as for `batch`, each a whole WebP file, decoded by
/// the verified container decoder (`vwebp::riff::webp_x`). For each, on
/// stdout: a status byte (0: invalid, 1: a still lossless image, 3: lossy,
/// 4: animated, 5: too big), the `lib` flag byte, and for an image its
/// width and height (u32 each), the strict flag byte and the pixels.
fn batch_file() {
    use vwebp::riff::WebpX;
    let limit: u64 = std::env::var("VW_LIMIT").ok().and_then(|v| v.parse().ok()).unwrap_or(1 << 28);
    let mut inp = std::io::stdin().lock();
    let mut out = std::io::BufWriter::new(std::io::stdout().lock());
    loop {
        let mut len = [0u8; 4];
        if inp.read_exact(&mut len).is_err() {
            break;
        }
        let mut buf = vec![0u8; u32::from_le_bytes(len) as usize];
        inp.read_exact(&mut buf).unwrap();
        match vwebp::riff::webp_x(&buf, limit) {
            Err(vwebp::dec::Error::Bad) => out.write_all(&[0, 0]).unwrap(),
            Err(vwebp::dec::Error::TooBig) => out.write_all(&[5, 0]).unwrap(),
            Ok((WebpX::Lossy, lib)) => out.write_all(&[3, lib as u8]).unwrap(),
            Ok((WebpX::Animated, lib)) => out.write_all(&[4, lib as u8]).unwrap(),
            Ok((WebpX::Still { img, strict }, lib)) => {
                out.write_all(&[1, lib as u8]).unwrap();
                out.write_all(&(img.w as u32).to_le_bytes()).unwrap();
                out.write_all(&(img.h as u32).to_le_bytes()).unwrap();
                out.write_all(&[strict as u8]).unwrap();
                for &c in &img.px {
                    out.write_all(&c.to_le_bytes()).unwrap();
                }
            }
        }
        out.flush().unwrap();
    }
}

/// `batch-anim`: records as for `batch`, each a whole WebP file, decoded by
/// the verified animation decoder (`vwebp::anim::webp_anim_x`). For each, on
/// stdout: a status byte (0: invalid, 1: an animation, 3: lossy, 5: too
/// big), the `lib` flag byte, and for an animation the canvas width and
/// height, loop count, background color and number of frames (u32 each),
/// then per frame its timestamp (u64) and canvas (little-endian ARGB u32s).
fn batch_anim() {
    use vwebp::anim::AnimRX;
    let limit: u64 = std::env::var("VW_LIMIT").ok().and_then(|v| v.parse().ok()).unwrap_or(1 << 26);
    let mut inp = std::io::stdin().lock();
    let mut out = std::io::BufWriter::new(std::io::stdout().lock());
    loop {
        let mut len = [0u8; 4];
        if inp.read_exact(&mut len).is_err() {
            break;
        }
        let mut buf = vec![0u8; u32::from_le_bytes(len) as usize];
        inp.read_exact(&mut buf).unwrap();
        match vwebp::anim::webp_anim_x(&buf, limit) {
            Err(vwebp::dec::Error::Bad) => out.write_all(&[0, 0]).unwrap(),
            Err(vwebp::dec::Error::TooBig) => out.write_all(&[5, 0]).unwrap(),
            Ok(AnimRX::Lossy) => out.write_all(&[3, 0]).unwrap(),
            Ok(AnimRX::Anim { cw, ch, bg, loops, frames, lib }) => {
                out.write_all(&[1, lib as u8]).unwrap();
                for v in [cw as u32, ch as u32, loops as u32, bg as u32, frames.len() as u32] {
                    out.write_all(&v.to_le_bytes()).unwrap();
                }
                for (ts, canvas) in &frames {
                    out.write_all(&ts.to_le_bytes()).unwrap();
                    for &c in canvas {
                        out.write_all(&c.to_le_bytes()).unwrap();
                    }
                }
            }
        }
        out.flush().unwrap();
    }
}

/// `batch-vp8-*`: see the module comment.
fn batch_vp8(mut dec: impl FnMut(&[u8]) -> Option<(vp8spec::Frame, bool)>) {
    let limit: u64 = std::env::var("VW_LIMIT").ok().and_then(|v| v.parse().ok()).unwrap_or(1 << 28);
    let mut inp = std::io::stdin().lock();
    let mut out = std::io::BufWriter::new(std::io::stdout().lock());
    loop {
        let mut len = [0u8; 4];
        if inp.read_exact(&mut len).is_err() {
            break;
        }
        let mut buf = vec![0u8; u32::from_le_bytes(len) as usize];
        inp.read_exact(&mut buf).unwrap();
        let big = buf.len() >= 10 && {
            let raw = u32::from_le_bytes([buf[6], buf[7], buf[8], buf[9]]) as u64;
            (raw & 0x3fff) * ((raw >> 16) & 0x3fff) > limit
        };
        match if big { None } else { dec(&buf) } {
            None => out.write_all(&[0]).unwrap(),
            Some((f, lib)) => {
                out.write_all(&[1]).unwrap();
                out.write_all(&(f.w as u32).to_le_bytes()).unwrap();
                out.write_all(&(f.h as u32).to_le_bytes()).unwrap();
                out.write_all(&[lib as u8]).unwrap();
                out.write_all(&f.y).unwrap();
                out.write_all(&f.u).unwrap();
                out.write_all(&f.v).unwrap();
            }
        }
        out.flush().unwrap();
    }
}

/// `batch-lossy-file`: see the module comment.
fn batch_lossy_file() {
    let limit: u64 = std::env::var("VW_LIMIT").ok().and_then(|v| v.parse().ok()).unwrap_or(1 << 28);
    let mut inp = std::io::stdin().lock();
    let mut out = std::io::BufWriter::new(std::io::stdout().lock());
    loop {
        let mut len = [0u8; 4];
        if inp.read_exact(&mut len).is_err() {
            break;
        }
        let mut buf = vec![0u8; u32::from_le_bytes(len) as usize];
        inp.read_exact(&mut buf).unwrap();
        match lossy::webp(&buf) {
            None => out.write_all(&[0]).unwrap(),
            Some(lossy::File::Other) => out.write_all(&[2]).unwrap(),
            Some(lossy::File::Lossy(l)) if (l.frame.w * l.frame.h) as u64 > limit => out.write_all(&[0]).unwrap(),
            Some(lossy::File::Lossy(l)) => {
                out.write_all(&[1]).unwrap();
                out.write_all(&(l.frame.w as u32).to_le_bytes()).unwrap();
                out.write_all(&(l.frame.h as u32).to_le_bytes()).unwrap();
                out.write_all(&[l.lib as u8, l.alpha.is_some() as u8]).unwrap();
                out.write_all(&l.frame.y).unwrap();
                out.write_all(&l.frame.u).unwrap();
                out.write_all(&l.frame.v).unwrap();
                if let Some(a) = &l.alpha {
                    out.write_all(a).unwrap();
                }
            }
        }
        out.flush().unwrap();
    }
}

/// `batch-lossy-file-v`: as `batch-lossy-file`, through the verified
/// decoder (`vwebp::vp8::file::webp_lossy_x`).
fn batch_lossy_file_v() {
    use vwebp::vp8::file::LossyX;
    let limit: u64 = std::env::var("VW_LIMIT").ok().and_then(|v| v.parse().ok()).unwrap_or(1 << 28);
    let mut inp = std::io::stdin().lock();
    let mut out = std::io::BufWriter::new(std::io::stdout().lock());
    loop {
        let mut len = [0u8; 4];
        if inp.read_exact(&mut len).is_err() {
            break;
        }
        let mut buf = vec![0u8; u32::from_le_bytes(len) as usize];
        inp.read_exact(&mut buf).unwrap();
        match vwebp::vp8::file::webp_lossy_x(&buf, limit) {
            Err(_) => out.write_all(&[0]).unwrap(),
            Ok(LossyX::NotLossy) => out.write_all(&[2]).unwrap(),
            Ok(LossyX::Image { frame, alpha, lib }) => {
                // The frame's own flag is the executable spec's (not verified).
                let flib = match lossy::webp(&buf) { Some(lossy::File::Lossy(l)) => l.lib, _ => false };
                out.write_all(&[1]).unwrap();
                out.write_all(&(frame.w as u32).to_le_bytes()).unwrap();
                out.write_all(&(frame.h as u32).to_le_bytes()).unwrap();
                out.write_all(&[(lib && flib) as u8, alpha.is_some() as u8]).unwrap();
                out.write_all(&frame.y).unwrap();
                out.write_all(&frame.u).unwrap();
                out.write_all(&frame.v).unwrap();
                if let Some(a) = &alpha {
                    out.write_all(a).unwrap();
                }
            }
        }
        out.flush().unwrap();
    }
}

fn cover() {
    if std::env::var_os("VW_COVER").is_some() {
        for (i, name) in specdec::COVER.iter().enumerate() {
            eprintln!("{:>10}  {}", specdec::HITS[i].load(Relaxed), name);
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("spec") => {
            let f = std::fs::read(&args[2]).expect("read");
            let Some(bs) = vp8l_payload(&f) else {
                eprintln!("spec: not a VP8L image");
                std::process::exit(2);
            };
            match specdec::vp8l(bs) {
                None => {
                    eprintln!("spec: no result");
                    std::process::exit(1);
                }
                Some((img, bits, strict)) => {
                    eprintln!(
                        "{}x{} alpha_hint {} bits {} ({} of {} bytes) strict {}",
                        img.w, img.h, img.alpha_hint, bits, bits.div_ceil(8), bs.len(), strict
                    );
                    if let Some(p) = args.get(3) {
                        write_pam(p, &img);
                    }
                }
            }
            cover();
        }
        Some("batch-spec") => {
            batch(specdec::vp8l);
            cover();
        }
        Some("batch-vp8-spec") => batch_vp8(|b| vp8spec::vp8_lib(b).map(|(f, lib, _)| (f, lib))),
        // The verified decoder; its `lib` flag is the executable spec's.
        Some("batch-vp8") => batch_vp8(|b| match vwebp::vp8::dec::vp8_x(b, 1 << 28) {
            Ok(f) => {
                let lib = vp8spec::vp8_lib(b).map(|(_, lib, _)| lib).unwrap_or(false);
                Some((vp8spec::Frame { w: f.w, h: f.h, y: f.y, u: f.u, v: f.v }, lib))
            }
            Err(_) => None,
        }),
        Some("vp8-notes") => {
            // Records as batch-vp8-spec; for each, one line: the verdict and the notes.
            let mut inp = std::io::stdin().lock();
            loop {
                let mut len = [0u8; 4];
                if inp.read_exact(&mut len).is_err() {
                    break;
                }
                let mut buf = vec![0u8; u32::from_le_bytes(len) as usize];
                inp.read_exact(&mut buf).unwrap();
                match vp8spec::vp8_lib(&buf) {
                    None => println!("none"),
                    Some((f, lib, n)) => {
                        println!("{}x{} lib={} {:?}", f.w, f.h, lib, n);
                        // VW_HEADER: the parsed header on stderr (VW_PROBS: and the
                        // coefficient probabilities on stdout, one per line).
                        if std::env::var_os("VW_HEADER").is_some() {
                            if let Some((mut h, _, parts)) = vp8spec::header(&buf) {
                                if std::env::var_os("VW_PROBS").is_some() {
                                    for p in &h.coeff_probs {
                                        println!("{}", p);
                                    }
                                }
                                h.coeff_probs.clear();
                                eprintln!("{:?}\npartitions {:?}", h, parts.iter().map(|p| p.len()).collect::<Vec<_>>());
                            }
                        }
                    }
                }
            }
        }
        Some("batch-lossy-file") => batch_lossy_file(),
        Some("batch-lossy-file-v") => batch_lossy_file_v(),
        Some("batch-file") => batch_file(),
        Some("batch-anim") => batch_anim(),
        Some("batch") => batch(|b| match vwebp::dec::vp8l_x(b, 1 << 28) {
            Ok((img, bits, strict)) => Some((
                specdec::Image { w: img.w as u64, h: img.h as u64, alpha_hint: img.alpha_hint, px: img.px },
                bits as u64,
                strict,
            )),
            Err(_) => None,
        }),
        _ => {
            eprintln!("usage: vwebp-tool spec FILE [OUT.pam] | batch-spec | batch | batch-file | batch-anim | batch-vp8-spec | vp8-notes");
            std::process::exit(2);
        }
    }
}
