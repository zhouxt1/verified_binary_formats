//! vbrotli-tool: drives vbrotli for the differential tests and benchmarks.
//!
//! * `vbrotli-tool spec FILE`: decode FILE with the executable spec
//!   (`specdec`), write the data to stdout; report the bits taken and the
//!   Google flag on stderr; exit 1 if the spec has no result.
//! * `vbrotli-tool dec FILE`: the same with the verified decoder.
//! * `vbrotli-tool batch` / `batch-spec`: records on stdin, each a little-endian u32
//!   length and that many bytes; for each, a record on stdout: a status byte
//!   (0: no result, 1: a result), then for a result the flag byte, the bits
//!   taken (u64) and the data (u32 length and bytes).
use std::io::{Read, Write};

mod specdec;

fn batch(mut dec: impl FnMut(&[u8]) -> Option<(Vec<u8>, u64, bool)>) {
    let mut inp = std::io::stdin().lock();
    let mut out = std::io::BufWriter::new(std::io::stdout().lock());
    loop {
        let mut len = [0u8; 4];
        if inp.read_exact(&mut len).is_err() {
            break;
        }
        let mut buf = vec![0u8; u32::from_le_bytes(len) as usize];
        inp.read_exact(&mut buf).unwrap();
        match dec(&buf) {
            None => out.write_all(&[0]).unwrap(),
            Some((data, bits, google)) => {
                out.write_all(&[1, google as u8]).unwrap();
                out.write_all(&bits.to_le_bytes()).unwrap();
                out.write_all(&(data.len() as u32).to_le_bytes()).unwrap();
                out.write_all(&data).unwrap();
            }
        }
        out.flush().unwrap();
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dict: &[u8] = &vbrotli::DICTIONARY[..];
    match args.get(1).map(|s| s.as_str()) {
        Some("spec") => {
            let buf = std::fs::read(&args[2]).expect("read");
            match specdec::brotli(dict, &buf) {
                None => {
                    eprintln!("spec: no result");
                    std::process::exit(1);
                }
                Some((data, bits, google)) => {
                    std::io::stdout().write_all(&data).unwrap();
                    eprintln!("bits {} ({} of {} bytes) google {}", bits, bits / 8, buf.len(), google);
                }
            }
        }
        Some("dec") => {
            let buf = std::fs::read(&args[2]).expect("read");
            match vbrotli::decompress(&buf, 1 << 32) {
                Err(e) => {
                    eprintln!("vbrotli: {:?}", e);
                    std::process::exit(1);
                }
                Ok((data, used)) => {
                    std::io::stdout().write_all(&data).unwrap();
                    eprintln!("{} bytes of {} taken", used, buf.len());
                }
            }
        }
        Some("batch") => batch(|b| {
            vbrotli::dec::brotli_x(dict, b, 1 << 30).ok().map(|(o, bits, g)| (o, bits as u64, g))
        }),
        Some("batch-stream") => {
            // pieces of 1..=VB_STREAM bytes, from a fixed pseudo-random sequence
            let maxp: usize = std::env::var("VB_STREAM").ok().and_then(|v| v.parse().ok()).unwrap_or(7);
            let mut seed: u64 = 0x9e3779b97f4a7c15;
            let mut held = (0usize, 0usize);
            batch(|b| {
                let mut d = vbrotli::Decompressor::new(1 << 30);
                let mut out = Vec::new();
                let mut i = 0;
                loop {
                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    let k = 1 + (seed >> 33) as usize % maxp;
                    let j = (i + k).min(b.len());
                    match d.feed(&b[i..j], &mut out) {
                        Ok(vbrotli::Status::Done { bits }) => return Some((out, bits as u64, d.google())),
                        Ok(vbrotli::Status::NeedMore) => {}
                        Err(_) => return None,
                    }
                    let h = d.held();
                    held = (held.0.max(h.0), held.1.max(h.1));
                    if j == b.len() {
                        return None;
                    }
                    i = j;
                }
            });
            if std::env::var_os("VB_MEM").is_some() {
                eprintln!("most held between pieces: input {} bytes, output buffer {} bytes", held.0, held.1);
            }
        }
        Some("batch-spec") => {
            batch(|b| specdec::brotli(dict, b));
            if std::env::var_os("VB_COVER").is_some() {
                for (name, h) in specdec::COVER.iter().zip(specdec::HITS.iter()) {
                    eprintln!("{:>12} {}", h.load(std::sync::atomic::Ordering::Relaxed), name);
                }
            }
        }
        _ => {
            eprintln!("usage: vbrotli-tool spec|dec FILE | batch | batch-spec");
            std::process::exit(2);
        }
    }
}
