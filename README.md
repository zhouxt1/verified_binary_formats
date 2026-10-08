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
| [vdeflate](vdeflate/README.md) | DEFLATE, zlib, gzip (RFC 1951, 1950, 1952): decoding and compressing, whole or streamed in bounded memory | the decoder computes the RFCs' output; what the compressor writes decodes to its input | 812 |
| [vbrotli](vbrotli/README.md) | Brotli (RFC 7932), whole or streamed | the decoder computes the RFC's output | 395 |
| [vwebp](vwebp/README.md) | WebP: lossless (VP8L, RFC 9649), lossy (VP8 key frames, RFC 6386) with alpha, the container, animation | the decoders compute RFC 9649's image and RFC 6386's reference decoder's | 1016 |
| [vh26x](vh26x/README.md) | H.264 and H.265 headers: NAL units, parameter sets, slice headers | decoder and encoder inverse to each other and to the standards' syntax tables | 76 |
| [vsyn](vsyn/README.md) | syntax tables as data, the interpreter vh26x runs | decoding and encoding inverse, for every table | 225 |
| [vsimd](vsimd/README.md) | SSE2 intrinsics for Verus, lane by lane | idioms (masks, saturating arithmetic, transposes) proved over the intrinsics, which are trusted and validated against the CPU | 182 |
| [vbits](vbits/README.md) | bit fields over byte buffers, the layer they all share | reads and writes against a bit view | 145 |

## One DEFLATE spec, three verifiers

A Verus spec is read through Verus and its SMT encoding. For DEFLATE, zlib
and gzip there is now also a spec in Lean ([lspec](lspec/README.md)),
written from RFCs 1951, 1950 and 1952 clause by clause, with the places
where the text is silent or ambiguous listed as open points. It is small,
executable and first-order, so that any verifier can state it. Theorems
about the format are proved in Lean. Three implementations, in three
verifiers, are proved against it:

| implementation | verifier | how it reaches the Lean spec |
|---|---|---|
| vdeflate (Rust) | Verus | Lean reads the VIR that Verus elaborates from `vdeflate/src/spec.rs` and `wrap.rs`, gives it a semantics, and proves that the decoders' contracts (DEFLATE, zlib, zlib with a dictionary, gzip, whole gzip files) and the compressors' contract (`deflate_ok`) mean the Lean spec's definitions (`lspec/Lspec/Bridge`) |
| [vpuff](vpuff/README.md): zlib's `puff.c` (C) | Rocq + VST | the Lean definitions come into Rocq through Lean's kernel export and rocq-lean-import; `puff()` is proved against them (`vpuff/rocq/Puff.v`) |
| [lean-zip](https://github.com/kim-em/lean-zip) (Lean) | Lean | its spec decoder is proved equal to this one, except that it refuses HDIST 30 and 31, as zlib does; its compressor's output decodes by this spec to its input (`lspec/leanzip`). This is lean-zip with our fix for [kim-em/lean-zip#2586](https://github.com/kim-em/lean-zip/issues/2586) (dynamic headers with more than 286 literal/length or 30 distance codes accepted), from [our fork](https://github.com/zhouxt1/lean-zip/tree/feat/2586-symbol-counts) |

The Lean side uses no `sorry` and only Lean's three standard axioms, except
for the lean-zip compressor theorem, which inherits lean-zip's
`bv_decide` proofs. The Verus link adds about 800 trusted lines of Lean:
the VIR reader and its semantics. The Lean spec is also run against zlib,
vdeflate and lean-zip on the differential test corpora
(`difftest/deflate/lspecdiff.py`, `lspecenc.py`, and `--lspec` on the
zlib/gzip suites).

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
  times zlib's, and compresses to within 0.25% of zlib's sizes at every level.
  Its near-optimal mode (`deflate_opt`), on a held-out set never used for
  tuning, is 0.07% to 0.29% larger than zopfli per set (0.02% smaller on
  one), and smaller than libdeflate -12 on four sets of five, with the
  same proof as the other levels. It does worse on files under 4 KB
  ([bench/deflate/HELDOUT.md](bench/deflate/HELDOUT.md));
* vbrotli decodes at 0.84 to 1.07 of Google's C decoder at quality 11;
* vwebp's lossy decoder, built with LTO, is at parity with libwebp (SSE2).

Each crate's README has the numbers, the machine and the method.

## What is trusted

The Verus verifier and the Rust compiler; the spec of each format, which
is tested, not proved, against the standard (below); and in `vsimd`, the
lane-by-lane specs of the SSE2 intrinsics, each checked against the CPU
through a proved model (`vsimd/tests/validate.rs`). Each crate's README
lists what else it trusts, if anything. There is no `assume` anywhere.

For DEFLATE, zlib and gzip, the Lean spec can stand in for the Verus spec
as the thing to read. The link then also trusts Lean's kernel and the VIR
reader and semantics in `lspec/Lspec/VIR` (see
[lspec/README.md](lspec/README.md)). vpuff trusts Rocq, VST, CompCert's C
semantics and rocq-lean-import (see [vpuff/README.md](vpuff/README.md)).

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
cargo verus verify --release     # 2,851 obligations, 0 errors, a few minutes
```

The crates depend on Verus's `vstd` at the version that release pins
(`Cargo.toml`); plain `cargo build` compiles the same code with the proofs
erased. The SIMD paths are for x86-64; elsewhere portable code, proved the
same way but not yet tested on other CPUs, runs instead. 64-bit targets
only.

The Lean spec and its bridges need Lean 4.34.0 ([elan](https://github.com/leanprover/elan)
picks it from `lspec/lean-toolchain`); the lean-zip package needs 4.35.0-rc2,
lean-zip's version:

```bash
(cd lspec && lake build)          # the spec, its theorems, the Verus bridge
(cd lspec/leanzip && lake build LeanZipEq LeanZipEnc)
lspec/Lspec/Bridge/gen-vdeflate.sh --check   # Verus's VIR is what is committed
```

vpuff builds in a Docker image with Rocq 9.3, CompCert, VST and
rocq-lean-import (`vpuff/docker`, then `vpuff/rocq/build.sh`).

`docs/spec/get.sh` fetches the standards the specs are written from.

## Related

[vasn](https://github.com/zhouxt1/vasn) is verified ASN.1 PER (5G, LTE and
ETSI ITS) on the same bit layer.

## License

MIT; see [LICENSE](LICENSE). `vbrotli/data/dictionary.bin` and the Brotli
test vectors in `vbrotli/tests/data` are Google's, under the MIT license
(see the READMEs next to them). `vpuff/c/puff.c` and `puff.h` are Mark
Adler's, under the zlib license (in `puff.h`), altered as marked at the top
of `puff.c`.
