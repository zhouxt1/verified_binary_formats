//! Decoding speed of vbrotli (into a buffer reused from round to round, as
//! the others are given; into a new `Vec` each time; and streaming in 64 KB
//! pieces) against Google's C decoder (1.2.0) and the Rust
//! brotli-decompressor crate. Each round times every decoder once, in turn,
//! so that all see the same machine; the table gives each one's fastest
//! round, in MB/s of output.
//!
//!   brotli-bench [-r ROUNDS] FILE.br...
use std::time::Instant;

extern "C" {
    fn BrotliDecoderDecompress(encoded_size: usize, encoded: *const u8, decoded_size: *mut usize,
                               decoded: *mut u8) -> i32;
}

fn google(src: &[u8], out: &mut [u8]) -> usize {
    let mut n = out.len();
    let r = unsafe { BrotliDecoderDecompress(src.len(), src.as_ptr(), &mut n, out.as_mut_ptr()) };
    assert_eq!(r, 1, "google: result {}", r);
    n
}

/// vbrotli's streaming decoder, fed 64 KB at a time.
fn stream(src: &[u8]) -> Vec<u8> {
    let mut d = vbrotli::Decompressor::new(1 << 32);
    let mut out = Vec::new();
    for piece in src.chunks(1 << 16) {
        match d.feed(piece, &mut out) {
            Ok(vbrotli::Status::Done { .. }) => break,
            Ok(vbrotli::Status::NeedMore) => {}
            Err(e) => panic!("stream: {:?}", e),
        }
    }
    out
}

fn rust(src: &[u8], out: &mut [u8]) -> usize {
    let info = brotli_decompressor::brotli_decode(src, out);
    assert!(matches!(info.result, brotli_decompressor::BrotliResult::ResultSuccess));
    info.decoded_size
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut rounds = 10;
    if args.len() > 1 && args[0] == "-r" {
        rounds = args[1].parse().unwrap();
        args.drain(0..2);
    }
    println!("{:<20} {:>9} {:>8} {:>8} {:>8} {:>8} {:>8}  {:>5} {:>5} {:>5} {:>5}", "file", "bytes", "into", "vec",
             "stream", "google", "rust", "in/g", "vec/g", "st/g", "in/rs");
    for f in &args {
        let src = std::fs::read(f).unwrap();
        let (want, _) = vbrotli::decompress(&src, 1 << 32).unwrap();
        let n = want.len();
        let mut buf = vec![0u8; n + 64];
        let mut best = [f64::MAX; 5];
        let mut mine: Vec<u8> = Vec::new();
        for _ in 0..rounds {
            let t = Instant::now();
            let (o, _) = vbrotli::decompress(&src, 1 << 32).unwrap();
            best[0] = best[0].min(t.elapsed().as_secs_f64());
            assert!(o == want);
            let t = Instant::now();
            let k = google(&src, &mut buf);
            best[1] = best[1].min(t.elapsed().as_secs_f64());
            assert!(k == n && buf[..n] == want[..]);
            let t = Instant::now();
            let k = rust(&src, &mut buf);
            best[2] = best[2].min(t.elapsed().as_secs_f64());
            assert!(k == n && buf[..n] == want[..]);
            let t = Instant::now();
            let o = stream(&src);
            best[3] = best[3].min(t.elapsed().as_secs_f64());
            assert!(o == want);
            let t = Instant::now();
            let (k, _) = vbrotli::decompress_into(&src, 1 << 32, &mut mine).unwrap();
            best[4] = best[4].min(t.elapsed().as_secs_f64());
            assert!(k == n && mine[..n] == want[..]);
        }
        let mb = |t: f64| n as f64 / t / 1e6;
        let name = std::path::Path::new(f).file_name().unwrap().to_string_lossy().to_string();
        let name: String = name.chars().take(20).collect();
        println!("{:<20} {:>9} {:>8.0} {:>8.0} {:>8.0} {:>8.0} {:>8.0}  {:>5.2} {:>5.2} {:>5.2} {:>5.2}", name, n,
                 mb(best[4]), mb(best[0]), mb(best[3]), mb(best[1]), mb(best[2]), best[1] / best[4], best[1] / best[0],
                 best[1] / best[3], best[2] / best[4]);
    }
}
