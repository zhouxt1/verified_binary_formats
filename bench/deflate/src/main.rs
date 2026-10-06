//! Decoding speed of vdeflate against zlib, miniz_oxide and libdeflate, on
//! raw DEFLATE streams. Each round times every decoder once, in turn, so
//! that all see the same machine; the table gives each one's fastest round.
//!
//!   deflate-bench [-r ROUNDS] FILE.deflate...
use std::time::Instant;

fn zlib_inflate(src: &[u8], out: &mut Vec<u8>) -> usize {
    let mut d = flate2::Decompress::new(false);
    let st = d.decompress(src, out, flate2::FlushDecompress::Finish).unwrap();
    assert!(st == flate2::Status::StreamEnd);
    d.total_out() as usize
}

/// For each input path on stdin: every decoder's verdict and output hash.
fn verdicts() {
    use std::io::BufRead;
    fn fnv(s: &[u8]) -> u64 {
        let mut h: u64 = 0xcbf29ce484222325;
        for &b in s { h ^= b as u64; h = h.wrapping_mul(0x100000001b3); }
        h
    }
    let mut dec = libdeflater::Decompressor::new();
    for line in std::io::stdin().lock().lines() {
        let path = line.unwrap();
        let src = std::fs::read(&path).unwrap();
        let v = match vdeflate::inflate::inflate_raw(&src, 1 << 26) {
            Ok((o, _, st)) => format!("ok:{:x}:{}", fnv(&o), if st { "z" } else { "r" }),
            Err(_) => "bad".to_string(),
        };
        let mut z = flate2::Decompress::new(false);
        let mut buf = vec![0u8; 1 << 26];
        let zl = match z.decompress(&src, &mut buf, flate2::FlushDecompress::Finish) {
            Ok(flate2::Status::StreamEnd) => format!("ok:{:x}", fnv(&buf[..z.total_out() as usize])),
            _ => "bad".to_string(),
        };
        let mz = match miniz_oxide::inflate::decompress_to_vec_with_limit(&src, 1 << 26) {
            Ok(o) => format!("ok:{:x}", fnv(&o)),
            Err(_) => "bad".to_string(),
        };
        let ld = match dec.deflate_decompress(&src, &mut buf) {
            Ok(n) => format!("ok:{:x}", fnv(&buf[..n])),
            Err(libdeflater::DecompressionError::InsufficientSpace) => "big".to_string(),
            Err(_) => "bad".to_string(),
        };
        println!("{} {} {} {} {}", path, v, zl, mz, ld);
    }
}

fn main() {
    if std::env::args().nth(1).as_deref() == Some("--libdeflate") {
        let src = std::fs::read(std::env::args().nth(2).unwrap()).unwrap();
        let mut buf = vec![0u8; 1 << 20];
        match libdeflater::Decompressor::new().deflate_decompress(&src, &mut buf) {
            Ok(n) => println!("libdeflate: {} bytes {:?}", n, String::from_utf8_lossy(&buf[..n])),
            Err(e) => println!("libdeflate: {:?}", e),
        }
        return;
    }
    if std::env::args().nth(1).as_deref() == Some("--verdicts") {
        verdicts();
        return;
    }
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut rounds = 10;
    if args.len() > 1 && args[0] == "-r" {
        rounds = args[1].parse().unwrap();
        args.drain(0..2);
    }
    println!("{:<16} {:>9} {:>9} {:>9} {:>9} {:>9} {:>9}   {:>6} {:>6} {:>6} {:>6}", "file", "bytes",
             "vdeflate", "vd_into", "zlib", "miniz_ox", "libdefl", "vd/mz", "into/zl", "into/mz", "into/ld");
    for f in &args {
        let src = std::fs::read(f).unwrap();
        let (want, _, _) = vdeflate::inflate::inflate_raw(&src, 1 << 32).unwrap();
        let n = want.len();
        let mut best = [f64::MAX; 5];
        let mut vbuf: Vec<u8> = Vec::new();
        let mut buf = vec![0u8; n + 64];
        let mut dec = libdeflater::Decompressor::new();
        for _ in 0..rounds {
            let t = Instant::now();
            let (o, _, _) = vdeflate::inflate::inflate_raw(&src, 1 << 32).unwrap();
            best[0] = best[0].min(t.elapsed().as_secs_f64());
            assert!(o == want);
            let t = Instant::now();
            let (m, _, _) = vdeflate::inflate::inflate_raw_into(&src, &mut vbuf, 1 << 32).unwrap();
            best[4] = best[4].min(t.elapsed().as_secs_f64());
            assert!(m == n && vbuf[..n] == want[..]);
            let t = Instant::now();
            let m = zlib_inflate(&src, &mut buf);
            best[1] = best[1].min(t.elapsed().as_secs_f64());
            assert!(m == n && buf[..n] == want[..]);
            let t = Instant::now();
            let o = miniz_oxide::inflate::decompress_to_vec(&src).unwrap();
            best[2] = best[2].min(t.elapsed().as_secs_f64());
            assert!(o == want);
            let t = Instant::now();
            let m = dec.deflate_decompress(&src, &mut buf).unwrap();
            best[3] = best[3].min(t.elapsed().as_secs_f64());
            assert!(m == n && buf[..n] == want[..]);
        }
        let mbs: Vec<f64> = best.iter().map(|t| n as f64 / t / 1e6).collect();
        let name = std::path::Path::new(f).file_name().unwrap().to_string_lossy().to_string();
        println!("{:<16} {:>9} {:>9.1} {:>9.1} {:>9.1} {:>9.1} {:>9.1}   {:>6.2} {:>6.2} {:>6.2} {:>6.2}", name, n,
                 mbs[0], mbs[4], mbs[1], mbs[2], mbs[3], mbs[0] / mbs[2], mbs[4] / mbs[1], mbs[4] / mbs[2], mbs[4] / mbs[3]);
    }
}
