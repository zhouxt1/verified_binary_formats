//! Tests that run on a fresh clone with `cargo test -p vwebp`: no libwebp or
//! RFC 6386 decoder to build. `data/vectors.txt` is a differential test
//! frozen by `difftest/webp/mkvec.py`, which kept only the inputs where the
//! verified decoders agree with libwebp (lossless) or RFC 6386's reference
//! decoder (lossy frames), or differ in a way the suites recognise. Each is
//! decoded here through the same verified entry point.
use vwebp::dec::vp8l_x;
use vwebp::riff::{webp_x, WebpX};
use vwebp::vp8::dec::vp8_x;
use vwebp::vp8::file::{webp_lossy_x, LossyX};

const LIMIT: u64 = 1 << 22;
const LOSSY_FILE_LIMIT: u64 = 1 << 25;

fn fnv(b: impl IntoIterator<Item = u8>) -> String {
    let h = b.into_iter().fold(0xcbf29ce484222325u64, |h, x| (h ^ x as u64).wrapping_mul(0x100000001b3));
    format!("{h:016x}")
}

fn px_bytes(px: &[u32]) -> impl Iterator<Item = u8> + '_ {
    px.iter().flat_map(|c| c.to_le_bytes())
}

fn unhex(s: &str) -> Vec<u8> {
    if s == "-" {
        return Vec::new();
    }
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

/// What the verified decoder gives for one vector, written as mkvec.py
/// writes the expected result.
fn result(kind: &str, s: &[u8]) -> String {
    match kind {
        "vp8l" => match vp8l_x(s, LIMIT) {
            Ok((img, bits, strict)) => format!("{} {} {} {} {}", img.w, img.h, strict as u8, bits, fnv(px_bytes(&img.px))),
            Err(_) => "bad".into(),
        },
        "vp8" => match vp8_x(s, LIMIT) {
            Ok(f) => format!("{} {} {}", f.w, f.h, fnv(f.y.iter().chain(&f.u).chain(&f.v).cloned())),
            Err(_) => "bad".into(),
        },
        "file" => match webp_x(s, LIMIT) {
            Ok((WebpX::Still { img, strict }, lib)) => {
                format!("{} {} {} {} {}", img.w, img.h, strict as u8, lib as u8, fnv(px_bytes(&img.px)))
            }
            Ok((WebpX::Lossy, lib)) => format!("lossy {}", lib as u8),
            Ok((WebpX::Animated, lib)) => format!("animated {}", lib as u8),
            Err(vwebp::dec::Error::TooBig) => "toobig".into(),
            Err(vwebp::dec::Error::Bad) => "bad".into(),
        },
        "lossy" => match webp_lossy_x(s, LOSSY_FILE_LIMIT) {
            Ok(LossyX::Image { frame: f, alpha, .. }) => format!(
                "{} {} {} {}",
                f.w,
                f.h,
                fnv(f.y.iter().chain(&f.u).chain(&f.v).cloned()),
                alpha.map(|a| fnv(a)).unwrap_or("-".into())
            ),
            Ok(LossyX::NotLossy) => "other".into(),
            Err(_) => "bad".into(),
        },
        _ => panic!("kind {kind}"),
    }
}

#[test]
fn vectors() {
    let mut n = std::collections::BTreeMap::new();
    for (i, line) in include_str!("data/vectors.txt").lines().enumerate() {
        if line.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = line.splitn(4, ' ').collect();
        let (kind, name, s, want) = (f[0], f[1], unhex(f[2]), f[3]);
        assert_eq!(result(kind, &s), want, "line {}: {kind} {name}", i + 1);
        *n.entry(kind).or_insert(0) += 1;
    }
    for kind in ["vp8l", "vp8", "file", "lossy"] {
        assert!(n.get(kind).copied().unwrap_or(0) >= 50, "{kind}: {n:?}");
    }
}

/// The pixel limit: a frame or stream over it is refused, at it decoded.
#[test]
fn limits() {
    for line in include_str!("data/vectors.txt").lines().filter(|l| !l.starts_with('#')) {
        let f: Vec<&str> = line.split(' ').collect();
        if f.len() < 6 || (f[0] != "vp8l" && f[0] != "vp8") {
            continue;
        }
        let s = unhex(f[2]);
        let px: u64 = f[3].parse::<u64>().unwrap() * f[4].parse::<u64>().unwrap();
        if f[0] == "vp8l" {
            assert!(matches!(vp8l_x(&s, px - 1), Err(vwebp::dec::Error::TooBig)), "{line}");
            assert!(vp8l_x(&s, px).is_ok());
        } else {
            assert!(matches!(vp8_x(&s, px - 1), Err(vwebp::vp8::dec::Error::TooBig)), "{line}");
            assert!(vp8_x(&s, px).is_ok());
        }
    }
}
