//! vh26x-tool: decode an H.264 Annex B stream with vh26x's verified header
//! codecs, print what it holds, and re-encode it.
//!
//!   vh26x-tool [--h265] [--trace] [--check] [--vec] FILE...
//!
//! One line per NAL unit: its index, type, verdict (`ok`, `raw`, `reject:
//! why`), and `nonconf` when a "decoders shall ignore" constraint failed.
//! `--trace` adds the syntax elements, `--check` re-encodes each decoded NAL
//! unit and compares it with the original bytes; `--vec` prints each
//! stream's units on one line, as `stream::summary`.
use vh26x_tool::{annexb, names, stream::*, why};

fn main() {
    let mut trace = false;
    let mut check = false;
    let mut h265 = false;
    let mut dump = false;
    let mut vec = false;
    let mut files = Vec::new();
    for a in std::env::args().skip(1) {
        match a.as_str() {
            "--trace" => trace = true,
            "--check" => check = true,
            "--h265" => h265 = true,
            "--dump" => dump = true,
            "--vec" => vec = true,
            _ => files.push(a),
        }
    }
    let mut bad = 0;
    for f in files {
        let data = match std::fs::read(&f) { Ok(d) => d, Err(e) => { eprintln!("{f}: {e}"); bad += 1; continue; } };
        let nals = match annexb::split(&data) { Some(n) => n, None => { println!("{f}: not an Annex B byte stream"); bad += 1; continue; } };
        let is265 = h265 || f.ends_with(".bit") || f.ends_with(".bin") || f.ends_with(".265") || f.ends_with(".hevc");
        if vec {
            println!("{}", summary(is265, &nals).join(" "));
            continue;
        }
        let mut h = Codec::new(is265);
        for (i, n) in nals.iter().enumerate() {
            let u = h.parse(n);
            let verdict = match u.kind {
                Kind::Parsed => "ok".to_string(),
                Kind::Raw => "raw".to_string(),
                Kind::Deferred => format!("deferred: {}", u.why),
                Kind::Rejected => format!("reject: {}", u.why),
            };
            let conf = if u.conf() { "" } else { " nonconf" };
            let prog = u.prog.map(|p| p.name).unwrap_or("-");
            let layer = if n.len() >= 2 && matches!(h, Codec::H265(_)) { format!(" layer={}", ((n[0] & 1) << 5) | (n[1] >> 3)) } else { String::new() };
            println!("{f} #{i} type={}{layer} {} {}{}", u.nal_type, prog, verdict, conf);
            if u.kind == Kind::Rejected {
                bad += 1;
                if let (Some(raw), true) = (u.prog, u.why == "syntax") {
                    let p = h.prog(raw);
                    let end = if matches!(raw.name, "slice" | "slice_a" | "slice_bc") { Some(u.rbsp.len() * 8) } else { why::sodb_end(&u.rbsp) };
                    match end {
                        Some(e) => println!("    why: {}", why::why(raw, &p.x, &u.ctx, &u.rbsp, e)),
                        None => println!("    why: the RBSP does not end in rbsp_trailing_bits( )"),
                    }
                }
            }
            if let (Some(raw), false, Kind::Parsed) = (u.prog, u.conf(), u.kind) {
                let p = h.prog(raw);
                let end = if matches!(raw.name, "slice" | "slice_a" | "slice_bc") { Some(u.rbsp.len() * 8) } else { why::sodb_end(&u.rbsp) };
                if let Some(e) = end {
                    for c in why::nonconf(raw, &p.x, &u.ctx, &u.rbsp, e) { println!("    conf: {c}"); }
                }
            }
            if let (Some(raw), Some(px)) = (u.prog, &u.px) {
                if trace || dump {
                    let p = h.prog(raw);
                    let hb = 8 * u.hdr.len();
                    for nm in names::annotate(raw, &p.x, &u.ctx, &px.trace) {
                        if dump { println!("E {} {} {} {}", hb + nm.pos, nm.len, nm.name, nm.value); }
                        else { println!("    {} = {}", nm.name, nm.value); }
                    }
                    if dump {
                        let end = match u.hdr_bits { Some(k) => k, None => why::sodb_end(&u.rbsp).unwrap_or(0) };
                        println!("END {}", hb + end);
                    }
                }
                if check {
                    let p = h.prog(raw);
                    if let Err(e) = reencode(&u, p, n) {
                        println!("{f} #{i} RE-ENCODE MISMATCH: {e}");
                        bad += 1;
                    }
                }
            }
        }
    }
    std::process::exit(if bad > 0 { 1 } else { 0 });
}
