// Google's brotli decoder, C, at the release the tests use (v1.2.0),
// from difftest/brotli/build/brotli (difftest/brotli/build.sh fetches it).
fn main() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../difftest/brotli/build/brotli/c");
    let mut b = cc::Build::new();
    b.include(root.join("include")).opt_level(2).warnings(false);
    for dir in ["common", "dec"] {
        for e in std::fs::read_dir(root.join(dir)).expect("run difftest/brotli/build.sh first") {
            let p = e.unwrap().path();
            if p.extension().map_or(false, |x| x == "c") {
                b.file(&p);
            }
        }
    }
    b.compile("brotlidec");
    println!("cargo:rerun-if-changed=build.rs");
}
