# verified_binary_formats

Decoders (and some encoders) for binary formats, written in Rust and proved
in [Verus](https://github.com/verus-lang/verus) to compute what the format's
standard says. The proofs are about the Rust that runs: for every input,
the decoder returns exactly the spec's result, or an error exactly when the
spec has none, and it never panics, reads out of bounds or overflows. The
spec of each format is a Verus function written from the standard, clause
by clause, and tested against the reference implementations.

| crate | format | proved | obligations |
|---|---|---|---|
| [vdeflate](vdeflate/README.md) | DEFLATE, zlib, gzip (RFC 1951, 1950, 1952): decoding and compressing, whole or streamed in bounded memory | the decoder computes the RFCs' output; what the compressor writes decodes to its input | 665 |
| [vbrotli](vbrotli/README.md) | Brotli (RFC 7932), whole or streamed | the decoder computes the RFC's output | 395 |
| [vwebp](vwebp/README.md) | WebP: lossless (VP8L, RFC 9649), lossy (VP8 key frames, RFC 6386) with alpha, the container, animation | the decoders compute RFC 9649's image and RFC 6386's reference decoder's | 1016 |
| [vh26x](vh26x/README.md) | H.264 and H.265 headers: NAL units, parameter sets, slice headers | decoder and encoder inverse to each other and to the standards' syntax tables | 76 |
| [vsyn](vsyn/README.md) | syntax tables as data, the interpreter vh26x runs | decoding and encoding inverse, for every table | 225 |
| [vsimd](vsimd/README.md) | SSE2 intrinsics for Verus, lane by lane | idioms (masks, saturating arithmetic, transposes) proved over the intrinsics, which are trusted and validated against the CPU | 182 |
| [vbits](vbits/README.md) | bit fields over byte buffers, the layer they all share | reads and writes against a bit view | 145 |

## Why

The code that reads untrusted bytes is where memory-safety bugs live.
libwebp's heap overflow (CVE-2023-4863) was exploited in the wild; in July
2026 researchers turned a heap overflow in libheif, reached through an image
upload to a forum, into a takeover of OpenAI employee accounts. Header parsers in FFmpeg,
GStreamer and libde265 are a steady source of CVEs. A decoder proved to
compute its spec has none of these bugs on any input, and parses exactly
what the standard allows, so it cannot disagree with another correct
decoder about what a file means.

The proofs do not make the decoders slow:

* vdeflate decodes at 0.75 to 0.83 of libdeflate's speed and 1.3 to 2.4
  times zlib's, and compresses to within 0.25% of zlib's sizes at every level;
* vbrotli decodes at 0.84 to 1.07 of Google's C decoder at quality 11;
* vwebp's lossy decoder, built with LTO, is at parity with libwebp (SSE2).

Each crate's README has the numbers, the machine and the method.

## What is trusted

The Verus verifier and the Rust compiler; the spec of each format, which
is tested, not proved, against the standard (below); and in `vsimd`, the
lane-by-lane specs of the SSE2 intrinsics, each checked against the CPU
through a proved model (`vsimd/tests/validate.rs`). Each crate's README
lists what else it trusts, if anything. There is no `assume` anywhere.

## Testing the specs

The proofs tie the code to the spec; whether the spec says what the
standard says is tested, against the reference implementations:

* `cargo test` needs nothing but Rust. Each format crate checks a few
  hundred inputs frozen from its differential tests, with the reference's
  verdict and output for each.
* `difftest/` holds the differential tests themselves, against zlib,
  miniz_oxide and libdeflate, Google's Brotli decoder, libwebp and RFC
  6386's reference decoder, with generators and mutation. Each suite's
  README lists what it ran and where the references depart from the
  standards. H.264/H.265 conformance streams (all 845 decode; FFmpeg reads
  every syntax element of 149,924 units alike) and the fuzzing harness
  against FFmpeg, GStreamer and libde265 are summarized in
  [vh26x/README.md](vh26x/README.md); the harness will be published after
  the issues it found are reported upstream.

## Build, test, verify

Stable Rust (1.94 or later) builds and tests everything:

```bash
cargo build --release
cargo test --release
```

Checking the proofs needs Verus. `tools/get-verus.sh` fetches the pinned
release (about 1.6 GB unpacked), which includes `cargo verus`:

```bash
tools/get-verus.sh
export PATH=$PWD/tools/verus-x86-linux:$PATH
cargo verus verify --release     # 2,704 obligations, 0 errors, about a minute
```

The crates depend on Verus's `vstd` at the version that release pins
(`Cargo.toml`); plain `cargo build` compiles the same code with the proofs
erased. The SIMD paths are for x86-64; elsewhere portable code, proved the
same way but not yet tested on other CPUs, runs instead. 64-bit targets
only.

`docs/spec/get.sh` fetches the standards the specs are written from.

## Related

[vasn](https://github.com/zhouxt1/vasn) is verified ASN.1 PER (5G, LTE and
ETSI ITS) on the same bit layer.

## License

MIT; see [LICENSE](LICENSE). `vbrotli/data/dictionary.bin` and the Brotli
test vectors in `vbrotli/tests/data` are Google's, under the MIT license
(see the READMEs next to them).
