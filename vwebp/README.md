# vwebp: a verified WebP decoder, lossless and lossy

`vwebp` decodes the WebP lossless bitstream (VP8L, RFC 9649 section 3), and
its decoder is proved in Verus to compute the RFC's image:
`dec::vp8l_x(buf, max_pixels)` returns exactly `spec::vp8l(lbits(buf))`,
the image, the bits it took and the `strict` flag, or `Bad` exactly when
the spec has no image, or `TooBig` when the header asks for more than
`max_pixels` pixels. It never panics. There is no `assume` and no raised
resource limit; the only `external_body` are two run-time CPU checks in
the lossy token parser (see "Lossy images"). The lossless decoder alone
was 177 obligations; with everything below `tools/webp/vv` checks 1016 in
a few minutes (on top of vdeflate's and vbrotli's, which it reuses).

## The spec

`spec.rs` is RFC 9649 section 3 as a function of the stream's LSB-first
bits: the header, the transforms (predictor, color, subtract green, color
indexing, each at most once), the entropy-coded sub-images, the meta prefix
codes, the prefix codes (simple and normal code length codes), LZ77 with
the 120-entry distance map, the color cache, and the inverse transforms,
last one first. Its bit fields and canonical codes are vdeflate's; a code
of one symbol is vbrotli's `dsym`, read with no bits.

Where the RFC does not say what a decoder does, the spec is libwebp
1.6.0's decoder; each such place says `LIBWEBP:`, and the list is at the
top of `spec.rs` and in [difftest/webp](../difftest/webp/README.md). The
flag `strict` is false when the stream relies on something libwebp accepts
and the RFC's text rules out (a single-symbol code of length other than
1, a simple-code symbol outside the alphabet).

The spec was first written as plain Rust (`vwebp-tool/src/specdec.rs`) and
tested against libwebp on 110,000 streams, then transcribed function by
function.

## The decoder

| module | what | proved to compute |
|---|---|---|
| `huff.rs` | canonical codes of up to 4096 symbols: vdeflate's symbol lists and bit-at-a-time decoder with its bound raised from 1024 (the green alphabet has up to 2328 symbols), and a table of each code's 10-bit (at most) windows, whose misses hold the code so far for longer codes | `decode_sym` |
| `code.rs` | reading and checking code lengths (simple, normal, `max_symbol`, repeats), a code's symbols | `read_code`, `code_ok`, `dsym` |
| `pix.rs` | prefix code groups; literals, LZ77 copies (overlapping), the color cache, from a 64-bit window into a preallocated image | `read_codes`, `read_groups`, `decode_pixels` |
| `img.rs` | color cache bits, entropy-coded images, meta prefix codes | `entropy_coded_image`, `spatially_coded_image` |
| `inv.rs` | pixel arithmetic (a byte at a time in 32-bit words), the 14 predictors, the inverse transforms in place, by rows and tiles | `inv_predictor`, `inv_color`, `inv_subtract_green`, `inv_color_indexing` |
| `invx.rs` | subtract-green and the color transform four pixels at a time in SSE2 (x86-64) | `inv_subtract_green`, `inv_color` |
| `tr.rs` | reading the transforms; the inverses, last first | `read_transforms`, `inverses` |
| `dec.rs` | the whole bitstream | `vp8l` |

## The container

`cspec.rs` is RFC 9649 section 2 for still images: the RIFF header, the
simple lossless format (a VP8L chunk), and the extended format (VP8X, then
any chunks, then the image chunk, whose size must be the canvas's). The
image's bitstream is its chunk's payload and no more (libwebp reads past
it: see difftest/webp). `riff::webp_x(file, max_pixels)` is proved to
compute it: the image, or that the file is lossy or animated (not decoded
here), or `Bad` exactly when the spec has none; with a flag `lib`, false
where libwebp's container parsing refuses what the RFC allows (a VP8X
chunk longer than 10 bytes, a missing padding byte in an extended file).
189 obligations in all.

## Animation

`aspec.rs` is animated WebP with lossless frames (RFC 9649 2.7.1.1): ANIM
and ANMF parsing as the RFC has it, and the canvases a reader shows, one
per frame, with their timestamps, as libwebp's WebPAnimDecoder makes them
(the RFC's canvas assembly is not exact): a transparent start and
disposal, its key-frame rule, its integer blend. `anim::webp_anim_x(file,
max_pixels)` is proved to compute it (231 obligations in all). It was
written as an executable model first (`difftest/webp/animmodel.py`),
checked against WebPAnimDecoder, then transcribed.

## Lossy images (VP8)

`vp8::dec::vp8_x(frame, max_pixels)` decodes a VP8 key frame, the image
of a lossy WebP file, and is proved to return exactly `vp8::spec::vp8`'s
Y'CbCr 4:2:0 planes (`Bad` exactly when the spec has none; `TooBig` by the
header). `vp8::file::webp_lossy_x(file, max_pixels)` adds the container and
the ALPH chunk's alpha (raw, or a lossless image-stream decoded by the
verified VP8L code), proved to compute `vp8::fspec::webp_lossy`.

The spec is RFC 6386's reference decoder (the RFC's section 20, which it
says defines the bitstream), key frames only, written as a Verus spec in
dixie's order of work: the bool decoder with dixie's `unsigned int`s, the
headers, every macroblock's modes, then macroblock by macroblock its tokens
and its reconstruction (intra prediction from the pixels so far, the
inverse transforms with their 16-bit first passes), then the loop filter.
It follows the RFC's code where its narrative differs, and where dixie has
quirks (it refuses a clamping type of 1; its dequantizer cache gives a
segment whose index is -1 factors of 0, in the first frame). The executable
transcription `vwebp-tool/src/vp8spec.rs` was checked against the reference
decoder itself (built from the RFC's text) and against libwebp before the
spec was written, and every point where libwebp departs from the reference
decoder is written down (difftest/webp/README.md, "Lossy images").

The decoder's parts each prove their step against the spec's: `bd` (the
bool decoder, reading ahead through a 64-bit window as libwebp's does, and
proved to give dixie's 32-bit `value` exactly, garbage high bits of
malformed streams included), `hdr`, `modes`, `tok` (tokens and dequantization), `xf`
(inverse DCT and WHT), `recon` (prediction and residuals, over a plane
module that views a flat buffer as rows), `lf` (the loop filter), `dec`,
and `fspec`/`file` for files. With them (and the RGB output stage,
`rgb`/`rgbx`/`api`, and the lossless decoder) the crate is 1016 obligations, still with no `assume` or
raised resource limit. Its only `external_body` are two run-time CPU checks
(`dec::tokens_step`, `tok::block_x_fast`) that choose the token parser
compiled for BMI2 and LZCNT, as libwebp picks its kernels by CPU; both
versions are the one verified body.

### SIMD

On x86-64 the decoder's hot loops run in SSE2, through `vsimd`
(../vsimd/README.md), whose intrinsics are the one trusted base: each is
`external_body` with a contract that says what it computes, checked against
the CPU, lane values exhaustively, through a proved model. Everything built
on them is proved to compute the same spec as the scalar code:

* `lfx`: the loop filter, all of it (luma and chroma, both directions, the
  simple, subblock and macroblock filters), 16 lines at once after
  libwebp's `dec_sse2.c`. A vertical edge's lines are rows, so they are
  transposed into columns and back; a macroblock's three inner vertical
  edges share one transpose. The 8-bit saturating arithmetic libwebp uses
  is proved to be the RFC's integers (`lemma_lane4`, `lemma_lane6`).
* `xfx`: the inverse DCT added to the prediction. The first pass is in
  16-bit lanes, where the reference decoder wraps to `short`s; the second
  is in 32-bit lanes, where it does not, so it is exact on the frames where
  libwebp's 16-bit pass overflows. A block with only a DC adds a constant;
  one with nothing is skipped.
* `predx`: 16 x 16 and 8 x 8 prediction a row at a time.
* `bd`: renormalization by the range's leading zeros, with no branch on
  whether to shift or take in a byte, and signs decoded without a branch.

Elsewhere (and on other targets, where `lf`, `recon` and `xf` keep their
scalar code) the decoder is the same.

The `lib` flag of a lossy image (libwebp gives the same planes) is
verified for the container and the alpha; the frame's own part is the
executable spec's (`vp8spec::Notes`), not verified.

## Tested

`cargo test -p vwebp` needs nothing but Rust: it checks 609 inputs frozen
from the differential tests below (`difftest/webp/mkvec.py`, our generators
and cwebp's output on our images only), each where
libwebp or RFC 6386's reference decoder agrees with the verified decoder
(or the difference is one the README explains), through the verified
VP8L, VP8, container and lossy-file decoders.

The verified decoder (`vwebp-tool batch`) and libwebp 1.6.0 agree on every
lossless image of libwebp-test-data, 56,000 streams of cwebp's and their
mutants, and 55,000 streams of our structure-aware generator
([difftest/webp](../difftest/webp/README.md)). The container decoder
agrees with libwebp on every file of libwebp-test-data and 45,000 generated
files and mutants, except in the ways libwebp departs from the RFC, each
recognized by recomputing libwebp's image from the bytes it read. The
animation decoder gives WebPAnimDecoder's canvases and timestamps on
10,000 generated animations and mutants, with the same kind of exceptions.

The verified lossy decoder (`vwebp-tool batch-vp8`, `batch-lossy-file-v`)
agrees with RFC 6386's reference decoder on the 88 lossy frames of
libwebp-test-data, 48,000 frames of cwebp's and their mutants and 20,000
generated frames, and with libwebp wherever the `lib` flag says it should;
on whole files, 7,593 files from cwebp (2,262 with alpha) and their
mutants.

## Not yet

Not covered: lossy frames in animations, incremental decoding. RGB(A)
output (`rgb`, libwebp's convention: fancy upsampling, its YUV->RGB
arithmetic, alpha, premultiplication) is verified against a spec of
libwebp's convention, not of an RFC.

## Speed, lossless

Single-threaded decoding of whole lossless files to ARGB, one core of a
Xeon Gold 6448H shared with other jobs, each decoder behind the batch
protocol of difftest/webp (`bench/webp/lbatch` for vwebp, `wdec` for
libwebp 1.6.0 with SSE2), measured by `bench/webp/ab_lossless.py`:
paired runs in alternating order, child CPU time, the geometric mean of
the per-image median ratios (KODAK=24 REPS=6). Images from
`bench/webp/get_lossless.sh`, all `cwebp -lossless`: Kodak's 24, six of
imagecompression.info's photographs (6 to 18 megapixels), four synthetic
graphics.

| | photos | Kodak | graphics | all |
|---|---|---|---|---|
| vwebp now vs 68c81be (bit-at-a-time codes) | 3.19x | 3.02x | 2.20x | 2.94x |
| vwebp now vs libwebp 1.6.0 | 1.13x | 1.26x | 1.17x | 1.22x |
| best MP/s, vwebp / libwebp | 40.6 / 35.6 | 43.6 / 34.2 | 129.1 / 105.6 | |

What made it: table-driven codes (1.5x), the pixel loop's window and
preallocated image (1.14x), transforms in place by rows and tiles with
bytewise arithmetic in 32-bit words (1.22x), then smaller steps (the
long-code fallback resumed from the table, unchecked reads where proved
in bounds, trivial-literal groups) and SSE2 for subtract-green and the
color transform (1.09x). The predictor then got SSE2 where a mode
needs nothing from the left (0, 2, 3, 4: four pixels a store) and, for
mode 11 (Select), the distances from the row above four at a time before
the pixels go in order (together 1.015x; graphics 1.05x). What is left
of the predictor is the chain through each pixel's left neighbour in the
modes that use it: 11 above all (in a 6-megapixel photo 2.8 of 6
million pixels, then 12 with 1.6), whose step is L's distance, a
comparison and a select, as in libwebp's SSE2. Batching rows so the
transforms run while the pixels are in cache (libwebp's 16 rows) is not
done.

## Speed, lossy

Single-threaded decoding to Y'CbCr, one core of a Xeon Gold 6448H, each
decoder behind the batch protocol of difftest/webp (child CPU time, the
same frame K and 2K times, best of 5; the machine was shared), cwebp -q 75.
Photos: the 13 camera images of imagecompression.info's 8-bit set (6 to 39
megapixels); Kodak: its 24 images. MP/s:

| decoder | photos | Kodak |
|---|---|---|
| vwebp, verified, SSE2 (2026-09-30, bd-wide) | 125.3 | 90.5 |
| vwebp, verified, SSE2 (2026-09-29, main) | 96.3 | 76.2 |
| libwebp 1.6.0, SSE2 | 120.8 | 98.0 |
| FFmpeg n9.0.2 vp8, x86 assembly | 114.6 | 82.0 |
| libwebp 1.6.0, C only | 70.9 | 59.9 |

From an earlier run of all of them (the same method, vwebp's rows from
builds a little older): FFmpeg without assembly 81.9 and 58.8, image-webp
(Rust) 53.6 and 52.6, Go x/image 44.8 and 24.1, Wuffs std/vp8 45.4 and
41.0 (Wuffs' planes differ from the others on 5 of the images), and vwebp
before SIMD 35.6 and 30.3. Every other decoder's planes equal vwebp's.

The first vwebp row is from bench.py on 2026-09-30 (libwebp's rows in that
run: 120.8 and 97.3). bench.py's best-of times move by several percent on
this shared machine; paired against libwebp with bench/webp/ab.py (which
now gives libwebp's `ydec` the whole file), on the photos and six Kodak
images, libwebp is **1.056x** as fast as this build without LTO (best
114.3 against 111.6 MP/s; the same build against itself reads 1.004), and
with LTO vwebp is **1.006x** as fast as libwebp (best 114.0 against 110.6):
at parity. On 2026-09-29 libwebp was 1.25x as fast. (libwebp is built as
its makefile.unix builds it, -O2 without LTO; its functions mostly share
translation units, which LTO would change little.) What changed, each timed with ab.py (paired runs, geometric
mean of per-image medians):

| change | speedup |
|---|---|
| the bool decoder reads through a 64-bit window, 3 bytes at a time (its view is proved to give dixie's 32-bit `value`, garbage high bits of malformed streams included) | 1.029 |
| `mb_tokens_x` inlined | 1.017 |
| unchecked reads where the proofs bound the index (`vsimd::mem`) | 1.012, 1.007 |
| crop in place, not into a new buffer (its page faults were 8% of the time) | 1.108 |
| the token loop in libwebp's shape (`GetCoeffsFast`), libwebp's bool comparison | 1.016 |
| no call or panic path left in the token loop | 1.018 |
| which blocks are a DC alone, from where their tokens end (in place of scanning the coefficients) | 1.025 |
| the token parser compiled for BMI2/LZCNT, chosen at run time per macroblock | 1.024 |
| built with LTO and one codegen unit (`bench/webp/vbatch`; the workspace's `release-lto` profile) | 1.044, 1.060 |

(`bench/webp/vbatch` also stopped writing through Rust's line-buffered
stdout, which scanned every plane for a newline: 1.010, the harness only.)

Tried and not kept, measured the same way: the reader in a local copy
(kept in registers, 0.99), the refill out of line (1.00), the loop filter
a row behind decoding (1.00: it is not bound by memory), `block_x` inlined
(0.95), neighbour gathering for 4x4 prediction with row offsets (0.97),
DC blocks built rather than copied (0.96), a CPU check per block (0.98).
The bool decoder takes 3 bytes at a time, not libwebp's 7: its window must
hold all 32 bits of the spec's `value`. Entropy decoding is now at
libwebp's cost per bool; what remains of the gap on small images is spread
over reconstruction, modes and per-macroblock work.
