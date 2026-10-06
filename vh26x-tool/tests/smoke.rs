//! Tests that run on a fresh clone with `cargo test -p vh26x-tool`: no
//! references or conformance streams. `data/vectors.txt` is frozen by the
//! differential tests (difftest/h26x/mkvec.py, published with them): streams from vh26x-gen on which FFmpeg reads
//! every syntax element alike and FFmpeg, GStreamer and libde265 accept
//! every unit, and mutants of them on which every reference's verdicts are
//! vh26x's. Each stream must decode, unit by unit, to the same verdicts and
//! values, and every decoded unit must re-encode to its bytes.
use vh26x_tool::{annexb, stream::summary};

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

#[test]
fn vectors() {
    let mut n = std::collections::BTreeMap::new();
    for (i, line) in include_str!("data/vectors.txt").lines().enumerate() {
        if line.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = line.splitn(4, ' ').collect();
        let (codec, kind, b, want) = (f[0], f[1], unhex(f[2]), f[3]);
        let nals = annexb::split(&b).expect("an Annex B stream");
        let got = summary(codec == "h265", &nals).join(" ");
        assert_eq!(got, want, "line {}: {codec} {kind}", i + 1);
        assert!(!got.contains("REENC"), "line {}: a unit does not re-encode", i + 1);
        if kind == "gen" {
            assert!(!got.contains(",reject,"), "line {}: a generated stream is refused", i + 1);
        }
        *n.entry((codec, kind)).or_insert(0) += 1;
    }
    for k in [("h264", "gen"), ("h264", "mut"), ("h265", "gen"), ("h265", "mut")] {
        assert!(n.get(&k).copied().unwrap_or(0) >= 20, "{k:?}: {n:?}");
    }
}
