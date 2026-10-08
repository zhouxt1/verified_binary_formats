//! vdeflate-tool: decode raw DEFLATE (or zlib-wrapped, with --zlib) with the
//! verified decoder.
//!
//!   vdeflate-tool [--zlib] IN [OUT]     decode; print verdict, sizes, zlib flag
//!   vdeflate-tool --time N [--zlib] IN  decode N times, print MB/s of output
use std::time::Instant;
use vdeflate::inflate::{inflate_raw, Error};

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut zlib = false;
    let mut time: Option<usize> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--zlib" => { zlib = true; args.remove(i); }
            "--time" => { time = Some(args[i + 1].parse().unwrap()); args.drain(i..i + 2); }
            _ => i += 1,
        }
    }
    if args.first().map(|a| a == "--batch-stream").unwrap_or(false) {
        // for each input: decode whole, then streamed in random pieces; they must agree
        use std::io::BufRead;
        let mut seed: u64 = 0x9E3779B97F4A7C15;
        let mut bad = 0usize;
        let mut count = 0usize;
        let mut peak = (0usize, 0usize);
        for line in std::io::stdin().lock().lines() {
            let path = line.unwrap();
            let data = std::fs::read(&path).expect("read input");
            let whole = inflate_raw(&data, 1 << 28);
            for round in 0..4 {
                let mut d = vdeflate::stream::Inflater::new(1 << 28);
                let mut sink: Vec<u8> = Vec::new();
                let mut pos = 0;
                let mut last = Ok(vdeflate::stream::Status::NeedMore);
                let mut peak_in = 0usize;
                let mut peak_out = 0usize;
                loop {
                    seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
                    let k = match round { 0 => 1, 1 => 1 + (seed % 7) as usize, 2 => 1 + (seed % 300) as usize, _ => 1 + (seed % 70000) as usize };
                    let end = (pos + k).min(data.len());
                    let (d2, r) = d.feed(&data[pos..end], &mut sink);
                    d = d2;
                    peak_in = peak_in.max(d.inp.len());
                    peak_out = peak_out.max(d.out.len());
                    pos = end;
                    let stop = !matches!(r, Ok(vdeflate::stream::Status::NeedMore));
                    last = r;
                    if stop || pos >= data.len() { break; }
                }
                if round == 0 { peak.0 = peak.0.max(peak_in); peak.1 = peak.1.max(peak_out); }
                let ok = match (&whole, &last) {
                    (Ok((o, q, st)), Ok(vdeflate::stream::Status::Done { bits, zlib })) =>
                        sink.len() == o.len() && sink[..] == o[..] && bits == q && zlib == st,
                    (Err(Error::Bad), Ok(vdeflate::stream::Status::NeedMore)) => true,
                    (Err(Error::Bad), Err(Error::Bad)) => true,
                    (Err(Error::TooBig), Err(Error::TooBig)) => true,
                    _ => false,
                };
                count += 1;
                if !ok {
                    bad += 1;
                    println!("MISMATCH {} round {}: whole {:?} stream {:?}", path, round,
                             whole.as_ref().map(|(o, q, s)| (o.len(), *q, *s)),
                             last.as_ref().map(|s| match s { vdeflate::stream::Status::NeedMore => (0, false),
                                 vdeflate::stream::Status::Done { bits, zlib } => (*bits, *zlib) }));
                }
            }
        }
        println!("stream checks {} mismatches {} (1-byte pieces: most input kept {} bytes, output buffer {} bytes)", count, bad, peak.0, peak.1);
        return;
    }
    if args.first().map(|a| a == "--compress").unwrap_or(false) {
        // compress each input path on stdin to PATH.vz; print sizes and time
        // (VD_LEVEL 1 to 9, VD_WRAP zlib or gzip, VD_FIXED, VD_STREAM=N: the
        // streaming compressor fed pieces of 1 to N bytes)
        use std::io::BufRead;
        for line in std::io::stdin().lock().lines() {
            let path = line.unwrap();
            let data = std::fs::read(&path).expect("read input");
            let t = Instant::now();
            let wrap = std::env::var("VD_WRAP").unwrap_or_default();
            let lv = vdeflate::enc2::level(std::env::var("VD_LEVEL").ok().and_then(|v| v.parse().ok()).unwrap_or(6));
            if let Some(maxp) = std::env::var("VD_STREAM").ok().and_then(|v| v.parse::<usize>().ok()) {
                // feed pieces of 1 to maxp bytes (a fixed pseudo-random sequence)
                enum D { Raw(vdeflate::deflater::Deflater), Z(vdeflate::deflater::ZDeflater) }
                let mut c: Vec<u8> = Vec::new();
                let mut d = if wrap == "zlib" || wrap == "gzip" {
                    let (z, h) = vdeflate::deflater::ZDeflater::new(lv, wrap == "gzip").expect("fixed codes");
                    c.extend_from_slice(&h);
                    D::Z(z)
                } else {
                    D::Raw(vdeflate::deflater::Deflater::new(lv).expect("fixed codes"))
                };
                let mut k = 0usize;
                let mut seed = data.len() as u64 ^ 0x9e3779b97f4a7c15;
                let mut peak = 0usize;
                while k < data.len() {
                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    let n = 1 + ((seed >> 33) as usize) % maxp;
                    let e = (k + n).min(data.len());
                    match &mut d {
                        D::Raw(d) => { c.extend_from_slice(&d.feed(&data[k..e])); peak = peak.max(d.kept_bytes()); }
                        D::Z(z) => c.extend_from_slice(&z.feed(&data[k..e])),
                    }
                    k = e;
                }
                match d { D::Raw(d) => c.extend_from_slice(&d.finish()), D::Z(z) => c.extend_from_slice(&z.finish()) }
                let dt = t.elapsed().as_secs_f64();
                std::fs::write(format!("{}.vz", path), &c).unwrap();
                println!("{} {} {} {:.1} kept {}", path, data.len(), c.len(), data.len() as f64 / dt / 1e6, peak);
                continue;
            }
            let c = if wrap == "zlib" { vdeflate::wrap::deflate_zlib(&data, lv) }
                else if wrap == "gzip" { vdeflate::wrap::deflate_gzip(&data, lv) }
                else if std::env::var("VD_FIXED").is_ok() { vdeflate::enc::deflate_fixed(&data) }
                else if std::env::var("VD_OPT").is_ok() {
                    // near-optimal parsing; VD_CHAIN, VD_NICE, VD_PASSES, VD_WIN
                    let ev = |k: &str, d: usize| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
                    let m = vdeflate::opt::opt_max();
                    let o = vdeflate::opt::Opt { chain: ev("VD_CHAIN", m.chain), nice: ev("VD_NICE", m.nice),
                                                 passes: ev("VD_PASSES", m.passes), win: ev("VD_WIN", m.win),
                                                 seg: ev("VD_SEG", m.seg), hbits: ev("VD_HBITS", m.hbits),
                                                 reopt: ev("VD_REOPT", m.reopt), steps3: ev("VD_STEPS3", m.steps3),
                                                 tries: ev("VD_TRIES", m.tries), bt: ev("VD_BT", m.bt as usize) != 0,
                                                 refine: ev("VD_REFINE", m.refine), rand: ev("VD_RAND", m.rand),
                                                 amp: ev("VD_AMP", m.amp as usize) as u32,
                                                 frac: ev("VD_FRAC", m.frac as usize) != 0 };
                    vdeflate::opt::deflate_opt(&data, o)
                }
                else { vdeflate::enc2::deflate_level(&data, lv) }.expect("input fits");
            let dt = t.elapsed().as_secs_f64();
            std::fs::write(format!("{}.vz", path), &c).unwrap();
            println!("{} {} {} {:.1}", path, data.len(), c.len(), data.len() as f64 / dt / 1e6);
        }
        return;
    }
    if args.first().map(|a| a == "--batch-wrap").unwrap_or(false) {
        // lines "zlib PATH" or "gzip PATH": verdict, zlib flag, length, bytes taken, FNV-1a;
        // "gzipfile PATH" (all members), "zlibdict PATH DICTPATH" (a preset dictionary)
        use std::io::BufRead;
        for line in std::io::stdin().lock().lines() {
            let line = line.unwrap();
            let (fmt, path) = line.split_once(' ').unwrap();
            if fmt == "zlibdict" {
                // "zlibdict PATH DICTPATH": a zlib stream that may use a preset dictionary
                let (p2, dpath) = path.split_once(' ').unwrap();
                let data = std::fs::read(p2).expect("read input");
                let dict = std::fs::read(dpath).expect("read dictionary");
                match vdeflate::wrap::inflate_zlib_dict(&data, &dict, 1 << 28) {
                    Ok((o, q, st)) => println!("{} ok {} {} {} {:016x}", p2, st as u8, o.len(), q, fnv(&o)),
                    Err(Error::Bad) => println!("{} bad", p2),
                    Err(Error::TooBig) => println!("{} toobig", p2),
                }
                continue;
            }
            let data = std::fs::read(path).expect("read input");
            if fmt == "gzipfile" {
                // a gzip file of one or more members
                match vdeflate::wrap::inflate_gzip_file(&data, 1 << 28) {
                    Ok(o) => println!("{} ok {} {:016x}", path, o.len(), fnv(&o)),
                    Err(Error::Bad) => println!("{} bad", path),
                    Err(Error::TooBig) => println!("{} toobig", path),
                }
                continue;
            }
            let r = if let Some(maxp) = std::env::var("VD_STREAM").ok().and_then(|v| v.parse::<usize>().ok()) {
                // the streaming decoder, in pieces of 1 to maxp bytes; NeedMore
                // at the end of the input is an incomplete stream: bad
                use vdeflate::zstream::{ZInflater, ZStatus};
                let mut z = ZInflater::new(fmt == "gzip", 1 << 28);
                let mut out: Vec<u8> = Vec::new();
                let mut k = 0usize;
                let mut seed = data.len() as u64 ^ 0x2545f4914f6cdd1d;
                let mut res = Err(Error::Bad);
                loop {
                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    let n = 1 + ((seed >> 33) as usize) % maxp;
                    let e = (k + n).min(data.len());
                    let (z2, r) = z.feed(&data[k..e], &mut out);
                    z = z2;
                    k = e;
                    match r {
                        Ok(ZStatus::Done { n, zlib }) => { res = Ok((std::mem::take(&mut out), n, zlib)); break; }
                        Ok(ZStatus::NeedMore) => { if k == data.len() { break; } }
                        Err(e) => { res = Err(e); break; }
                    }
                }
                res
            } else if fmt == "zlib" { vdeflate::wrap::inflate_zlib(&data, 1 << 28) } else { vdeflate::wrap::inflate_gzip(&data, 1 << 28) };
            match r {
                Ok((o, q, st)) => println!("{} ok {} {} {} {:016x}", path, st as u8, o.len(), q, fnv(&o)),
                Err(Error::Bad) => println!("{} bad", path),
                Err(Error::TooBig) => println!("{} toobig", path),
            }
        }
        return;
    }
    if args.first().map(|a| a == "--batch").unwrap_or(false) {
        // one input path per stdin line; print verdict, zlib flag, length, FNV-1a of the output
        use std::io::BufRead;
        for line in std::io::stdin().lock().lines() {
            let path = line.unwrap();
            let data = std::fs::read(&path).expect("read input");
            match inflate_raw(&data, 1 << 28) {
                Ok((o, q, st)) => println!("{} ok {} {} {} {:016x}", path, st as u8, o.len(), q, fnv(&o)),
                Err(Error::Bad) => println!("{} bad", path),
                Err(Error::TooBig) => println!("{} toobig", path),
            }
        }
        return;
    }
    let data = std::fs::read(&args[0]).expect("read input");
    let body: &[u8] = if zlib { &data[2..] } else { &data };
    let max_out = 1usize << 32;
    if let Some(n) = time {
        let mut best = f64::MAX;
        let mut outlen = 0;
        for _ in 0..n {
            let t = Instant::now();
            let r = inflate_raw(body, max_out);
            let dt = t.elapsed().as_secs_f64();
            if let Ok((o, _, _)) = &r { outlen = o.len(); }
            best = best.min(dt);
        }
        println!("{} bytes out, best {:.3} ms, {:.1} MB/s", outlen, best * 1e3, outlen as f64 / best / 1e6);
        return;
    }
    match inflate_raw(body, max_out) {
        Ok((o, q, st)) => {
            println!("ok {} bytes in {} bits, zlib {}", o.len(), q, if st { "accepts" } else { "rejects" });
            if args.len() > 1 { std::fs::write(&args[1], &o).expect("write output"); }
        }
        Err(Error::Bad) => { println!("bad"); std::process::exit(2); }
        Err(Error::TooBig) => { println!("toobig"); std::process::exit(3); }
    }
}

fn fnv(s: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in s { h ^= b as u64; h = h.wrapping_mul(0x100000001b3); }
    h
}
