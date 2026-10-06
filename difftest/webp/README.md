# Differential testing of the WebP decoders

Lossless (VP8L) first; lossy (VP8) is [its own section](#lossy-images-vp8) below.

The spec is RFC 9649 section 3 (the VP8L bitstream) as a decoding
function. It is written first as plain Rust (`vwebp-tool/src/specdec.rs`),
with every step a function of the bits and a position, and tested here
against libwebp before any proof is written. Where the RFC does not say what
a decoder does, the spec follows libwebp 1.6.0 (listed below). Where libwebp
accepts a stream the RFC's text rules out, the spec decodes it too and its
`strict` flag is false.

`build.sh` builds libwebp v1.6.0 from source (`build/dwebp`, `cwebp`,
`webpinfo`, and `wdec`, libwebp behind the batch protocol of
`vwebp-tool batch-*`) and fetches libwebp-test-data at a pinned commit.


| script | what | result |
|---|---|---|
| `corpus.py` | every file of libwebp-test-data; the 43 lossless ones decoded (the 88 lossy, alpha and animated ones skipped) | 43 identical images |
| `wdiff.py [-n N] [--seed S]` | images of eleven kinds (noise at 1-8 bits per channel, gradients, palettes of 1-256 colors, runs, stripes, tiles, tiny, flat, random alpha, smooth with noise) encoded by cwebp with every `-z` preset, `-q`/`-m` pairs, `-exact`, `-near_lossless`, and 3 mutants of each (bit flips, many in the first 40 bytes; truncations; extensions; overwritten bytes) | 56,000 streams (seeds 1-10): 0 failures |
| `gen.py [-n N] [--seed S]` | our own VP8L writer, simulating the decoder as it writes: transforms in any order (and repeated), predictor images with every green value, color tables of every size with indexes past the table, color caches of every size and invalid ones, entropy images with unused groups and over 1000 groups, prefix codes as random complete trees written as simple or normal codes (runs of 16/17/18, `max_symbol`, single-symbol code length codes) and, on purpose, incomplete, over-subscribed, empty, single-symbol of length other than 1, simple symbols outside the alphabet; LZ77 copies with every kind of distance, overlapping, before the start and past the end; then some truncated or extended. Half the streams are meant to be valid | 54,000 streams (seeds 1-11): 0 failures, 0 streams meant valid refused |
| `cdiff.py [-n N] [--seed S]` | the container, through the verified container decoder (`vwebp-tool batch-file`, `vwebp::riff::webp_x`): every file of libwebp-test-data, edge files built by hand, and gen.py's streams in files of many shapes (simple; extended with VP8X of 10 or more bytes, reserved bits and flags, ICCP/ALPH/EXIF/XMP/unknown chunks before and after the image, odd sizes, canvases that match or not, the Animation flag; lossy chunks; data after the RIFF; a missing padding byte) and 2 mutants of each (header bytes flipped, sizes off by a little, truncations). Every difference from libwebp must be one of the ways listed below, checked: libwebp's image recomputed from the bytes it read | 45,000 files (seeds 2-6): 0 unexplained; every kind of difference seen |
| `agen.py [-n N] [--seed S] [--tool batch-anim]` | animations: frames from gen.py's streams at even offsets on a canvas, every dispose and blend method, durations, ANIM background and loop count, chunks before, between, after and inside frames, reserved VP8X bits, frames without a bitstream; and a mutant of each (header bytes, sizes, ANMF flags and offsets, truncations). Through libwebp's WebPAnimDecoder (`adec`) and the executable model (`animmodel.py`) or the verified decoder (`vwebp::anim::webp_anim_x`); canvases and timestamps compared frame by frame. Differences must be libwebp's readings, recomputed (`libwebp_view`) | model: 4,800 files; verified decoder: 10,000 files (seeds 1-10), 0 unexplained |
| `mkvec.py [-n N] [--seed S]` | freezes 609 inputs, at most 2.5 KB each, into `vwebp/tests/data/vectors.txt`: bare VP8L streams (wdiff, gen) where libwebp gives the same image or also refuses; bare VP8 frames (ldiff, gen8) where RFC 6386's reference decoder agrees; lossless files (cdiff) where libwebp agrees or cdiff.py explains the difference; lossy files with alpha (lfile) where libwebp agrees. Nothing from libwebp-test-data, which has no license to redistribute it under. `cargo test -p vwebp` then checks each through the verified decoders, with no libwebp | run again when the spec changes |
| `all.sh` | all three, small (about 5 s); `TOOL=batch` for the verified decoder | |

`--tool batch` runs the verified decoder (`vwebp::dec::vp8l_x`) instead of
the executable spec. On it: the 43 corpus images, 56,000 wdiff.py streams
(seeds 1-10) and 55,000 gen.py streams (seeds 1-11), 0 failures.

With `VW_COVER=1`, `vwebp-tool batch-spec` prints how often each part of
the spec ran. On `gen.py`'s streams every counter is reached except code
16 before any nonzero length, which the corpus reaches.

Both decoders are given each stream bare, and libwebp gets it wrapped in a
simple lossless RIFF file (`wlib.riff`): libwebp's API refuses any input
shorter than a RIFF header, 12 bytes, bare bitstream or not
(`ParseHeadersInternal`, VP8_STATUS_NOT_ENOUGH_DATA). Odd-length streams
get a zero byte appended for both (`wlib.even`), for the first finding
below.

## Findings

### libwebp decodes past the end of the VP8L chunk

libwebp's lossless decoder is given the rest of the input, not the chunk:
`DecodeInto` sets `io.data_size = headers.data_size - headers.offset`, and
`VP8LDecodeHeader` initializes the bit reader with it; the chunk size
(`headers.compressed_size`) is checked against the RIFF size and then not
used. So a VP8L stream that runs past its chunk goes on decoding from what
follows:

* the RIFF padding byte of an odd-sized chunk. `wdiff.py`'s first run
  found 77 truncated mutants that libwebp decoded and the spec refused; all
  had odd length, each needed 1 to 8 bits past its end, and the pixels
  libwebp produced depend on the padding byte's value (0x00 vs 0xff);
* the chunks after it: a VP8L chunk cut short by 4 bytes, followed in a
  VP8X file by an unknown chunk whose tag is the 4 missing bytes, decodes
  to the intact image; with the tag `ABCD` it decodes to another one;
* bytes after the RIFF: a simple file whose VP8L chunk is cut short by 2
  or 4 bytes, followed (outside the RIFF size) by the missing bytes,
  decodes to the intact image.

RFC 9649 2.3 and 2.7 give the chunk's payload as Chunk Size bytes, so an
image's bits are those bytes, and the container spec (`vwebp/src/cspec.rs`)
bounds the stream by the chunk. A file whose image's bits run past its
chunk has no image there and has one in libwebp (cdiff.py's `overrun`:
libwebp's image is the spec's image of the payload extended by the file's
next bytes). Decoders that respect the chunk (to be checked: image-webp,
FFmpeg, Wuffs) and libwebp then see different images in the same file.

libwebp does bound the chunk itself by the RIFF data: a VP8L chunk whose
size runs past the RIFF is refused, in simple and extended files alike.

### libwebp reads a RIFF with no chunk header as a bare bitstream

When the data after `WEBP` is not a VP8, VP8L or VP8X chunk, libwebp takes
it as a bare VP8 or VP8L bitstream (`ParseVP8Header`, "Raw VP8/VP8L
bitstream (no header)"), a form its comments call "not a valid WebP format:
only allowed for internal purpose". So `RIFF size WEBP` followed by a VP8L
bitstream with no chunk header decodes (cdiff.py's edge file `raw`, and
mutants whose first chunk tag was flipped). The RFC's WebP file is
chunks; the spec refuses it.

### The VP8X chunk and the padding byte

* The RFC's VP8X: "Future specifications may add more fields. Unknown
  fields MUST be ignored." libwebp refuses a VP8X chunk of any size but
  10 (`ParseVP8X`, "Wrong chunk size"). The spec takes 10 or more, and its
  `lib` flag is false for more.
* An odd-sized image chunk whose padding byte is missing (the RIFF ends
  with the payload): libwebp takes it in a simple file and refuses it in
  an extended one (`ParseOptionalChunks` counts the chunk with its padding
  against the RIFF size). The spec takes both, with `lib` false for the
  second.

### Animation: where libwebp departs from the RFC

The spec's canvas assembly is libwebp's (the RFC's is not exact), and
agen.py checks it frame by frame. Its parsing follows the RFC, and there
libwebp takes more:

* **An ANMF chunk's size is not used past its image chunks.** libwebp's
  demuxer reads a frame's ALPH and bitstream chunks and resumes top-level
  parsing right after them (`ParseAnimationFrame`, `StoreFrame`), only
  checking they fit the size. An ANMF whose size claims more bytes than it
  has decodes; the RFC's chunk structure does not allow it.
* **Padding bytes read as data**: a frame's odd-sized VP8L chunk is
  decoded with its padding byte after it (the fragment is the padded
  chunk), and an ANIM chunk of 5 bytes is read as 6, its padding byte
  taken as the high byte of the loop count.
* **An ANMF without a bitstream chunk is dropped** (it gets no frame
  number, so it is not added), where the RFC's frame data has one.
* **VP8X reserved bits set** ("Readers MUST ignore this field"): the
  demuxer refuses the file (`IsValidExtendedFormat`, `~ALL_VALID_FLAGS`).
  The still-image decoder ignores them. The spec's `lib` flag says so.
* **The alpha hint changes the canvases.** A frame's "has alpha" is its
  VP8L header's alpha hint, which decides whether it is a key frame
  (drawn without blending), so two animations with the same pixels
  composite differently: a full-canvas frame of pixels 0x80ff0000 over
  an opaque one gives 0x80ff0000 with the hint 0 and 0xff7f007e with the
  hint 1. RFC 3.4: the hint "SHOULD NOT impact decoding". The spec
  follows libwebp here, as for all of canvas assembly.

## Where the RFC is silent: the spec follows libwebp

Each is marked `LIBWEBP:` in specdec.rs, and none separates the spec from
libwebp in these tests.

* **Invalid prefix codes.** RFC 3.7.2.1 says "the described tree must be a
  complete binary tree", and that a single leaf "is marked with the length
  of 1". It does not say what a decoder does otherwise. libwebp
  (`BuildHuffmanTable`) refuses all-zero lengths and, with two or more
  symbols, anything but a complete code (Kraft sum exactly 1); it accepts a
  single symbol of *any* length, read with no bits. The spec does the same;
  a single symbol of length other than 1 clears `strict`.
* **Simple-code symbols outside the alphabet.** The second symbol of a simple
  code is 8 bits; the distance alphabet has 40 symbols. libwebp drops a
  symbol past the alphabet (writing past `alphabet_size` in a buffer sized
  for the largest alphabet, then building from the first `alphabet_size`);
  the RFC's `code_lengths[symbol1] = 1` has no such entry. The spec drops it
  and clears `strict`.
* **`max_symbol` counts tokens.** "A prefix table is then built ... and used
  to read up to max_symbol code lengths": libwebp counts code length code
  *symbols* read, a repeat (16, 17, 18) counting as one
  (`ReadHuffmanCodeLengths`). A repeat past the alphabet is an error.
* **Predictor modes 14 and 15, and green values of 16 or more.** Table 2 has
  14 modes. libwebp takes the mode from the green value's low 4 bits and
  runs modes 14 and 15 as mode 0 (`VP8LPredictorsAdd[14]`, `[15]`, "padding
  security sentinels").
* **The color cache hash** `(0x1e35a7bd * color) >> (32 - bits)` is taken
  mod 2^32 (libwebp's `VP8LHashPix`).
* **LZ77 copies from before the first pixel or past the last** are errors
  (libwebp `DecodeImageData`).
* **Unused prefix code groups** (numbers below the largest in the entropy
  image that no tile uses) are read and must be valid, like used ones
  (libwebp reads them with no table and checks them the same, also on its
  remapping path for more than 1000 groups).

Also as libwebp, and as the RFC says: a transform type seen twice is an
error; a color index past the table is transparent black; color cache
bits outside 1..11 are an error; trailing bits after the last pixel are
ignored.

## Lossy images (VP8)

The spec for a lossy image is RFC 6386's reference decoder ("dixie",
section 20 of the RFC), restricted to key frames: RFC 6386 section 1 says
"The bitstream is defined by the reference source code and not this
narrative." `vwebp-tool/src/vp8spec.rs` transcribes it as plain Rust, to the
decoded Y'CbCr 4:2:0 planes (the RGB conversion is not part of VP8);
`vwebp-tool/src/lossy.rs` adds the container and the ALPH chunk's alpha
(RFC 9649), with cspec.rs's container rules. Its tables
(`vwebp-tool/src/vp8tab.rs`) are printed by compiling the RFC's own headers
(`tools/webp/vp8tables.sh`).

Oracles, all run on the same bytes:

* `rfc/build.sh` builds the reference decoder from the RFC's text
  (`docs/spec/get.sh` fetches it) into `build/rfc/rdec`: `extract.py` cuts
  section 20 into files. The listing does not build as printed: it includes
  `vpx_codec.h`, `vpx_encoder.h` and `vpx_config.h`, which it does not
  print (taken from libvpx v0.9.7, 2011, or left empty); `vpx_image.h`
  spells `VPX_IMGFMT_RGB555` where `vpx_image.c` uses `VPX_IMG_FMT_RGB555`;
  and `tokens.c` declares `short coeffs` for a pointer (RFC erratum 3395).
  `rdec.c` also sets the error handler's `setjmp` flag, which nothing in the
  listing sets: without it an error does not end the frame, decoding
  carries on past it, and 97 of the first 900 mutants crashed it
  (out-of-bounds reads in the loop filter and the bool decoder's set-up).
  `rdec` decodes each frame in a child process, so a crash is a result.
* libwebp 1.6.0 (`ydec.c`: `WebPDecode` to MODE_YUVA, no RGB conversion).

| script | what | result |
|---|---|---|
| `lcorpus.py` | the 88 lossy frames of libwebp-test-data (vp80-00-comprehensive, intra, segmentation, partitions, sharpness, lossy_alpha, ...), bare | reference decoder, libwebp and ours: 88 identical |
| `ldiff.py [-n N] [--seed S]` | wdiff.py's eleven kinds of image encoded lossy by cwebp (random `-q`, `-m`, `-segments`, `-sns`, `-f`, `-sharpness`, `-strong`/`-nostrong`, `-af`, `-preset`, `-partition_limit`, `-sharp_yuv`), and 3 mutants of each frame (bit flips, often in the header and first partition; truncations; extensions; a different first partition size; overwritten bytes) | 48,000 frames (seeds 2-7): 0 failures; FFmpeg agrees with the reference decoder on all 12,000 encoder outputs |
| `gen8.py [-n N] [--seed S]` | random key frames from a boolean encoder (RFC 6386 7.3): header fields over their whole ranges (segmentation with absolute or delta values and extreme adjustments, both filter types, levels 0-63, sharpness, filter deltas, 1-8 token partitions, quantizer deltas, probability updates to any value, 0 included, skip probability), then random mode and token bits, some biased towards 1 (long runs of the largest coefficients); now and then hidden, reserved bits set, a short, 1-byte or empty partition, a partition size past the end, a partition starting with 0xff | 20,000 frames (seeds 2-6): 0 failures |
| `lfile.py [-n N] [--seed S]` | whole files through `vwebp-tool batch-lossy-file`: every file of libwebp-test-data, and images with and without alpha encoded lossy by cwebp (random `-alpha_method`, `-alpha_filter`, `-alpha_q`, `-exact`, `-noalpha`), and 3 mutants of each (the ALPH header byte's fields, the alpha truncated or extended, a second ALPH, chunks added or dropped, the VP8X flags, canvas and size, the frame) | 6,393 files (seeds 1-3): 0 failures; 1,885 decoded with alpha |
| `all.sh` (the lossy part) | lcorpus.py, and ldiff.py, gen8.py and lfile.py small | |

`--tool batch-vp8` (lcorpus, ldiff, gen8) and `--tool batch-lossy-file-v`
(lfile) run the verified decoder (`vwebp::vp8::dec::vp8_x`,
`vwebp::vp8::file::webp_lossy_x`) instead of the executable spec. On it:
the 88 corpus frames, 48,000 ldiff.py frames (seeds 2-7), 20,000 gen8.py
frames (seeds 2-6) and 7,593 lfile.py files (seeds 1-3, 2,262 with alpha),
0 failures.

A failure is: ours and the reference decoder disagree on a frame (verdict or
any sample); or ours sets its `lib` flag and libwebp's planes (and, for
files, alpha) differ from ours; or the reference decoder refuses an encoder's
output. `lib` is the conjunction of `vp8spec::Notes`, the points where
libwebp's code parts from the reference decoder's, each recorded when the
spec meets it. Where libwebp and the reference decoder differ, the scripts
print which notes explain it; no difference has been left unexplained. A
note is not always a difference (the level of an edge whose filter changes
nothing, say): `lib` is exact for refusals and conservative for pixels.

Frames are given to all decoders at even length (`llib.even`), for the last
finding below.

### Where libwebp parts from the reference decoder

No encoder output reaches any of these: each needs a frame no encoder
writes. Where FFmpeg is named, it was run on the same frames
(`ldiff.py`/`gen8.py` seed 21, frames with that one note).

* **libwebp refuses** (the reference decoder decodes):
  * a hidden frame (`show_frame` 0: "Frame not displayable"; FFmpeg outputs
    nothing either);
  * a partition read past its end: the reference decoder shifts in zeros
    (RFC 7.3), libwebp's reader stops ("Premature end-of-file"). The spec
    models libwebp's reader exactly (`Bool::lib_eof`: a read that starts
    with every byte loaded and fewer than 8 bits left, `shifts >= 8n - 7`, or
    an empty partition that some row reads);
  * an empty last partition (ParsePartitions wants `part_start < buf_end`;
    FFmpeg refuses too).
* **The reference decoder refuses** (libwebp decodes): the color space or
  clamping type bit set. dixie supports neither ("Reserved bits not
  supported"), though the narrative (9.2) defines clamping type 1 as valid
  ("no clamping is necessary"); libwebp ignores both bits. Every frame the
  reference decoder refused and libwebp decoded (ldiff.py seeds 2-7: 46;
  gen8.py seeds 2-6: 629) was this (`llib.why_refused`).
* **Different planes**:
  * *Segments without segment data.* A key frame with segmentation on and
    no segment data: dixie (and FFmpeg, 60 of 60) takes the segments' values
    as deltas of 0, so each segment gets the frame's quantizer and filter
    level; libwebp's `ResetSegmentHeader` sets `absolute_delta`, so its
    segments get quantizer index 0 and filter level 0.
  * *Filter level clamping.* dixie clamps a macroblock's filter level to
    0..63 after the segment's adjustment and again after the deltas;
    libwebp only after the deltas (FFmpeg sided with dixie on 104 frames,
    with libwebp on 16).
  * *Inner edges.* dixie filters a macroblock's inner edges if any block,
    the Y2 block too, had a token other than an immediate end of block;
    libwebp if a Y or chroma block has a coefficient past the first or a
    nonzero first one (the Y blocks' from the inverse WHT). They differ when
    the Y2 block's tokens give an inverse WHT of all zeros.
  * *16-bit transforms.* dixie keeps the first pass of the inverse DCT and
    WHT in `short`s; libwebp's C code keeps `int`s, its SSE2 code 16-bit
    lanes throughout. They differ when an intermediate leaves 16 bits, which
    needs coefficients beyond what quantization gives (FFmpeg: 68 of 69 with
    dixie).
  * *A partition starting with 0xff.* The bool decoder's value then starts
    outside its interval (`value >= range << 8`, which no encoder produces)
    and stays there. dixie's 32-bit `value` overflows and wraps; libwebp's
    64-bit window, its C and SSE2 builds, and FFmpeg all gave different
    planes on the first such frame.
  * *A 1-byte partition.* dixie's `init_bool_decoder` reads nothing from a
    partition of fewer than 2 bytes; libwebp reads the byte.
  * *dixie's dequantizer cache.* dixie recomputes a segment's factors only
    if its quantizer index changed or `delta_update`; the cache starts at
    index -1 with factors 0. So in a first frame, a segment whose index
    comes to -1 (the frame's index 0 with a delta of -1, or an absolute
    -1) with no quantizer deltas keeps factors 0 and every coefficient
    dequantizes to 0; libwebp clamps -1 to 0. (The same condition is RFC
    erratum 8717, reported, for later frames.) The spec follows the RFC as
    printed.

### libwebp decodes past the end of the VP8 chunk

As for VP8L (above), libwebp's VP8 decoder takes the rest of the input as
the frame, not the chunk (`io.data_size` in DecodeInto), so its last token
partition runs on into the RIFF padding byte, later chunks and bytes after
the RIFF. A truncated 19-byte frame the reference decoder refuses
(`sz <= first_partition_size + 10`) was decoded by libwebp from its 20th
byte, the padding. Where the spec's `lib` flag is set this changes nothing:
libwebp then stops inside the frame.

### Alpha

`lossy.rs` decodes the ALPH chunk as RFC 9649 2.7.1.2 says: raw, or an
image-stream of the image's size decoded by the lossless spec
(`specdec::image_stream`, alpha in green), then unfiltered. libwebp also
refuses an ALPH header with its reserved bits set or preprocessing past 1,
which the RFC says to ignore: `lib` is false for those. Every ALPH chunk
of the corpus and of cwebp under every alpha method, filter and quality
decoded to libwebp's alpha plane.

## Other decoders

The same streams were also run through FFmpeg, image-webp, Go's x/image,
Wuffs, ImageSharp and TwelveMonkeys. That comparison and what it found
will be published once the findings are reported upstream.
