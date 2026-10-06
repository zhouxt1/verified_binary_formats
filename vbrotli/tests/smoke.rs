//! Tests that run on a fresh clone with `cargo test -p vbrotli`: no Google
//! decoder to build. `data/vectors.txt` is a differential test frozen by
//! `difftest/brotli/mkvec.py`: Google's verdict, data and end for each
//! stream (its small test vectors, edge.py's hand-built streams, its
//! encoder's output and mutants), or, where Google refuses and the RFC does
//! not, the spec's decode with the Google flag off.
use vbrotli::dec::{brotli_x, Error};
use vbrotli::{decompress, decompress_into, Decompressor, Status, DICTIONARY};

const LIMIT: usize = 1 << 30;

fn fnv(b: &[u8]) -> u64 {
    b.iter().fold(0xcbf29ce484222325u64, |h, &x| (h ^ x as u64).wrapping_mul(0x100000001b3))
}

fn unhex(s: &str) -> Vec<u8> {
    if s == "-" {
        return Vec::new();
    }
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

#[derive(Debug, PartialEq)]
struct Want {
    len: usize,
    hash: u64,
    end: usize,
    google: bool,
}

fn vectors() -> Vec<(String, Vec<u8>, Option<Want>)> {
    include_str!("data/vectors.txt")
        .lines()
        .filter(|l| !l.starts_with('#'))
        .map(|l| {
            let f: Vec<&str> = l.split_whitespace().collect();
            let want = (f[2] == "ok").then(|| Want {
                len: f[3].parse().unwrap(),
                hash: u64::from_str_radix(f[4], 16).unwrap(),
                end: f[5].parse().unwrap(),
                google: f[6] == "1",
            });
            (f[0].to_string(), unhex(f[1]), want)
        })
        .collect()
}

fn got(d: &[u8], end: usize, google: bool) -> Want {
    Want { len: d.len(), hash: fnv(d), end, google }
}

#[test]
fn vectors_whole() {
    let vs = vectors();
    assert!(vs.len() > 250);
    let mut buf = Vec::new();
    for (name, s, want) in &vs {
        match (brotli_x(&DICTIONARY[..], s, LIMIT), want) {
            (Ok((d, bits, g)), Some(w)) => {
                assert_eq!(bits % 8, 0, "{name}");
                assert_eq!(&got(&d, bits / 8, g), w, "{name}");
            }
            (Err(Error::Bad), None) => {}
            (r, w) => panic!("{name}: got {:?}, want {w:?}", r.map(|(d, b, g)| (d.len(), b, g))),
        }
        // the public API: the same data and end
        let r = decompress(s, LIMIT).ok().map(|(d, end)| (fnv(&d), d.len(), end));
        assert_eq!(r, want.as_ref().map(|w| (w.hash, w.len, w.end)), "{name}");
        let r = decompress_into(s, LIMIT, &mut buf).ok().map(|(n, end)| (fnv(&buf[..n]), n, end));
        assert_eq!(r, want.as_ref().map(|w| (w.hash, w.len, w.end)), "{name}");
    }
}

/// Each vector streamed in pieces: the same data, end and flag, or never
/// `Done` where the whole-buffer decoder refuses.
#[test]
fn vectors_streamed() {
    let mut seed = 0x2545F4914F6CDD1Du64;
    for (name, s, want) in vectors() {
        for max in [1usize, 7, 300, 70000] {
            let mut d = Decompressor::new(LIMIT);
            let mut sink = Vec::new();
            let mut done = None;
            let mut pos = 0;
            while pos < s.len() && done.is_none() {
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                let k = 1 + (seed % max.min(s.len() - pos) as u64) as usize;
                match d.feed(&s[pos..pos + k], &mut sink) {
                    Ok(Status::Done { bits }) => done = Some(got(&sink, bits / 8, d.google())),
                    Ok(Status::NeedMore) => {}
                    Err(_) => break,
                }
                pos += k;
            }
            match (&done, &want) {
                (Some(g), Some(w)) => assert_eq!(g, w, "{name}, pieces up to {max}"),
                (None, None) => {}
                _ => panic!("{name}, pieces up to {max}: {done:?}, want {want:?}"),
            }
        }
    }
}

#[test]
fn output_limit() {
    for (name, s, want) in vectors() {
        if let Some(w) = want {
            if w.len > 0 {
                assert!(matches!(brotli_x(&DICTIONARY[..], &s, w.len - 1), Err(Error::TooBig)), "{name}");
                assert!(brotli_x(&DICTIONARY[..], &s, w.len).is_ok(), "{name}");
            }
        }
    }
}

/// The static dictionary is RFC 7932 Appendix A's (its CRC-32 there).
#[test]
fn dictionary() {
    let t = vdeflate::wrap::crc_table();
    assert_eq!(vdeflate::wrap::crc32_x(&t, &DICTIONARY[..]), 0x5136_CB04);
}
