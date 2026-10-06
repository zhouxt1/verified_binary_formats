//! vh26x-gen [--h265] [--any] SEED OUT [SLICES]: a random well-formed Annex B
//! stream; conforming, or with --any also breaking the constraints a decoder
//! must ignore.
use vh26x_tool::{annexb, sgen};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let h265 = args.iter().any(|a| a == "--h265");
    sgen::set_conforming(!args.iter().any(|a| a == "--any"));
    let rest: Vec<&String> = args.iter().filter(|a| !a.starts_with("--")).collect();
    let seed: u64 = rest[0].parse().unwrap();
    let out = rest[1];
    let slices: usize = rest.get(2).map(|s| s.parse().unwrap()).unwrap_or(3);
    for k in 0..1000u64 {
        let s = seed.wrapping_add(k << 32);
        let nals = if h265 { sgen::h265(s, slices) } else { sgen::h264(s, slices) };
        if let Some(n) = nals {
            if !sgen::decodes(&n, h265) {
                eprintln!("seed {s}: the stream does not decode back");
                std::process::exit(2);
            }
            std::fs::write(out, annexb::join(&n)).unwrap();
            return;
        }
    }
    eprintln!("no stream for seed {seed}");
    std::process::exit(1);
}
