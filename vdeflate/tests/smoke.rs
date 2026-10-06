//! Tests that run on a fresh clone with `cargo test -p vdeflate`: no zlib to
//! build. `data/vectors.txt` is a differential test frozen by
//! `difftest/deflate/mkvec.py`: zlib's verdict, data and end for each stream
//! (or, where zlib refuses and the RFC does not, the spec's decode with the
//! zlib flag off). The rest are round trips and checksums against plain
//! reference implementations written here.
use vdeflate::deflater::ZDeflater;
use vdeflate::enc2::{deflate_level, level};
use vdeflate::inflate::{inflate_raw, inflate_raw_into, Error};
use vdeflate::stream::{Inflater, Status};
use vdeflate::wrap::{adler32_x, crc32_x, crc_table, deflate_gzip, deflate_zlib, inflate_gzip, inflate_gzip_file, inflate_zlib};
use vdeflate::zstream::{ZInflater, ZStatus};

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

/// A small deterministic generator (xorshift), for data and piece sizes.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Inputs of several kinds: text, runs, a small alphabet, random bytes, empty.
fn samples() -> Vec<Vec<u8>> {
    let mut r = Rng(0x9e3779b97f4a7c15);
    let text: Vec<u8> = include_str!("../src/spec.rs").bytes().collect();
    let mut v = vec![
        Vec::new(),
        b"a".to_vec(),
        text.clone(),
        text.iter().cycle().take(300_000).cloned().collect(),
        vec![7u8; 100_000],
        (0..50_000).map(|_| b"ab"[r.below(2)]).collect(),
        (0..70_000).map(|_| r.next() as u8).collect(),
    ];
    // the 258-byte matches and 32K distances at their limits
    let block: Vec<u8> = (0..32768).map(|_| r.next() as u8).collect();
    v.push([block.clone(), block.clone(), block].concat());
    v
}

#[derive(Debug)]
struct Want {
    len: usize,
    hash: u64,
    end: usize,
    zlib: bool,
}

fn vectors() -> Vec<(String, Vec<u8>, Option<Want>)> {
    include_str!("data/vectors.txt")
        .lines()
        .filter(|l| !l.starts_with('#'))
        .map(|l| {
            let f: Vec<&str> = l.split_whitespace().collect();
            let want = if f[2] == "ok" {
                Some(Want {
                    len: f[3].parse().unwrap(),
                    hash: u64::from_str_radix(f[4], 16).unwrap(),
                    end: f[5].parse().unwrap(),
                    zlib: f[6] == "1",
                })
            } else {
                None
            };
            (f[0].to_string(), unhex(f[1]), want)
        })
        .collect()
}

fn check(i: usize, got: Result<(Vec<u8>, usize, bool), Error>, want: &Option<Want>) {
    match (got, want) {
        (Ok((d, end, z)), Some(w)) => {
            assert_eq!((d.len(), fnv(&d), end, z), (w.len, w.hash, w.end, w.zlib), "vector {i}")
        }
        (Err(Error::Bad), None) => {}
        (got, want) => panic!("vector {i}: got {:?}, want {want:?}", got.map(|(d, e, z)| (d.len(), e, z))),
    }
}

#[test]
fn vectors_whole() {
    let vs = vectors();
    assert!(vs.len() > 300);
    let mut buf = Vec::new();
    for (i, (fmt, s, want)) in vs.iter().enumerate() {
        match fmt.as_str() {
            "raw" => {
                check(i, inflate_raw(s, LIMIT).map(|(d, bits, z)| (d, (bits + 7) / 8, z)), want);
                let r = inflate_raw_into(s, &mut buf, LIMIT);
                check(i, r.map(|(n, bits, z)| (buf[..n].to_vec(), (bits + 7) / 8, z)), want);
            }
            "zlib" => check(i, inflate_zlib(s, LIMIT), want),
            "gzip" => check(i, inflate_gzip(s, LIMIT), want),
            _ => panic!("format {fmt}"),
        }
    }
}

/// Each vector streamed in pieces: the same data and end, or never `Done`
/// where the whole-buffer decoder refuses.
#[test]
fn vectors_streamed() {
    let mut r = Rng(12345);
    for (i, (fmt, s, want)) in vectors().iter().enumerate() {
        for max in [1usize, 7, 300, 70000] {
            let mut sink = Vec::new();
            let mut done = None;
            let mut pos = 0;
            if fmt == "raw" {
                let mut d = Inflater::new(LIMIT);
                while pos < s.len() && done.is_none() {
                    let k = 1 + r.below(max.min(s.len() - pos));
                    let (d2, st) = d.feed(&s[pos..pos + k], &mut sink);
                    d = d2;
                    pos += k;
                    match st {
                        Ok(Status::Done { bits, zlib }) => done = Some(((bits + 7) / 8, zlib)),
                        Ok(Status::NeedMore) => {}
                        Err(_) => break,
                    }
                }
            } else {
                let mut d = ZInflater::new(fmt == "gzip", LIMIT);
                while pos < s.len() && done.is_none() {
                    let k = 1 + r.below(max.min(s.len() - pos));
                    let (d2, st) = d.feed(&s[pos..pos + k], &mut sink);
                    d = d2;
                    pos += k;
                    match st {
                        Ok(ZStatus::Done { n, zlib }) => done = Some((n, zlib)),
                        Ok(ZStatus::NeedMore) => {}
                        Err(_) => break,
                    }
                }
            }
            match (done, want) {
                (Some((end, z)), Some(w)) => {
                    assert_eq!((sink.len(), fnv(&sink), end, z), (w.len, w.hash, w.end, w.zlib), "vector {i}, pieces up to {max}")
                }
                (None, None) => {}
                (None, Some(w)) if w.len == 0 && s.is_empty() => {}
                (done, want) => panic!("vector {i}, pieces up to {max}: {done:?}, want {want:?}"),
            }
        }
    }
}

#[test]
fn round_trips() {
    for data in samples() {
        for n in 1..=9 {
            let raw = deflate_level(&data, level(n)).unwrap();
            let (back, bits, z) = inflate_raw(&raw, LIMIT).unwrap();
            assert!(back == data && (bits + 7) / 8 == raw.len() && z, "level {n}, {} bytes", data.len());
        }
        let zl = deflate_zlib(&data, level(6)).unwrap();
        assert_eq!(inflate_zlib(&zl, LIMIT).unwrap(), (data.clone(), zl.len(), true));
        let gz = deflate_gzip(&data, level(1)).unwrap();
        assert_eq!(inflate_gzip(&gz, LIMIT).unwrap(), (data.clone(), gz.len(), true));
    }
}

#[test]
fn streamed_round_trips() {
    let mut r = Rng(777);
    for data in samples() {
        for (gz, max) in [(true, 1usize), (false, 7), (true, 300), (false, 70000)] {
            if max == 1 && data.len() > 20_000 {
                continue;
            }
            let (mut z, mut out) = ZDeflater::new(level(if gz { 6 } else { 1 }), gz).unwrap();
            let mut pos = 0;
            while pos < data.len() {
                let k = 1 + r.below(max.min(data.len() - pos));
                out.extend(z.feed(&data[pos..pos + k]));
                pos += k;
            }
            out.extend(z.finish());
            let mut d = ZInflater::new(gz, LIMIT);
            let mut back = Vec::new();
            let mut pos = 0;
            let mut end = None;
            while pos < out.len() && end.is_none() {
                let k = 1 + r.below(max.max(13).min(out.len() - pos));
                let (d2, st) = d.feed(&out[pos..pos + k], &mut back);
                d = d2;
                pos += k;
                if let ZStatus::Done { n, .. } = st.unwrap() {
                    end = Some(n);
                }
            }
            assert!(back == data && end == Some(out.len()), "gzip {gz}, pieces up to {max}, {} bytes", data.len());
        }
    }
}

#[test]
fn gzip_members_and_limits() {
    let a = b"first member ".repeat(1000);
    let mut gz = deflate_gzip(&a, level(9)).unwrap();
    gz.extend(deflate_gzip(b"", level(6)).unwrap());
    gz.extend(deflate_gzip(b"and a third", level(1)).unwrap());
    let back = inflate_gzip_file(&gz, LIMIT).unwrap();
    assert_eq!(back, [a.clone(), b"and a third".to_vec()].concat());
    let raw = deflate_level(&a, level(6)).unwrap();
    assert!(matches!(inflate_raw(&raw, a.len() - 1), Err(Error::TooBig)));
    assert_eq!(inflate_raw(&raw, a.len()).unwrap().0, a);
}

fn crc32_ref(s: &[u8]) -> u32 {
    let mut c = !0u32;
    for &b in s {
        c ^= b as u32;
        for _ in 0..8 {
            c = if c & 1 != 0 { (c >> 1) ^ 0xEDB8_8320 } else { c >> 1 };
        }
    }
    !c
}

fn adler32_ref(s: &[u8]) -> u32 {
    let (mut a, mut b) = (1u32, 0u32);
    for &x in s {
        a = (a + x as u32) % 65521;
        b = (b + a) % 65521;
    }
    (b << 16) | a
}

/// The checksums' fast paths (eight bytes a step, sixteen in SSE2) at every
/// length and alignment near their edges, and across Adler-32's 64 KB runs.
#[test]
fn checksums() {
    let t = crc_table();
    assert_eq!(crc32_x(&t, b"123456789"), 0xCBF4_3926);
    assert_eq!(adler32_x(b"Wikipedia"), 0x11E6_0398);
    let mut r = Rng(42);
    let big: Vec<u8> = (0..300_000).map(|_| r.next() as u8).collect();
    let ones = vec![0xffu8; 200_000];
    for s in [&big[..], &ones[..]] {
        for off in 0..17 {
            for len in (0..80).chain([4095, 4096, 5552, 5553, 65535, 65536, 65537, 131_073, 199_983]) {
                let p = &s[off..off + len];
                assert_eq!(crc32_x(&t, p), crc32_ref(p), "crc, offset {off}, length {len}");
                assert_eq!(adler32_x(p), adler32_ref(p), "adler, offset {off}, length {len}");
            }
        }
    }
}
