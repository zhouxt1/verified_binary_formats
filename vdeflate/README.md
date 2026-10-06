# vdeflate: a verified DEFLATE, zlib and gzip decoder and compressor

vdeflate decodes DEFLATE (RFC 1951), zlib (RFC 1950) and gzip (RFC 1952)
streams, whole or in pieces, with proofs in Verus that it computes what the
RFCs say, and compresses to all three, whole or in pieces, with proofs that
what it writes decodes, by the same spec, to its input. Streaming, both
ways, runs in bounded memory. It is built on `vbits`, the bit layer the
repository's other codecs share, with the LSB-first view DEFLATE packs its
bits in (`vbits/src/lsb.rs`).

## Using it

```rust
use vdeflate::inflate::{inflate_raw, Error};
use vdeflate::wrap::{inflate_zlib, inflate_gzip_file, deflate_gzip};
use vdeflate::enc2::{deflate_level, level};

// Decoding: Ok((data, bytes or bits taken, zlib_accepts)), or Err(Bad | TooBig).
let (data, _bits, _) = inflate_raw(&raw_stream, 1 << 30)?;
let (data, _used, _) = inflate_zlib(&zlib_stream, 1 << 30)?;
let data = inflate_gzip_file(&gz_file, 1 << 30)?;      // every member

// Compressing (whole inputs under 256 MB): zlib's levels 1 to 9.
let raw = deflate_level(&data, level(6)).unwrap();
let gz = deflate_gzip(&data, level(9)).unwrap();

// Streaming, any length, in bounded memory.
use vdeflate::deflater::ZDeflater;
let (mut z, mut out) = ZDeflater::new(level(6), true).unwrap();   // gzip
for piece in pieces { out.extend(z.feed(piece)); }
out.extend(z.finish());

use vdeflate::zstream::{ZInflater, ZStatus};
let mut d = ZInflater::new(true, 1 << 30);                        // gzip
let mut data = Vec::new();
for piece in pieces {
    let (d2, r) = d.feed(piece, &mut data);
    d = d2;
    match r? { ZStatus::Done { n, .. } => break, ZStatus::NeedMore => {} }
}
```

`examples/usage.rs` runs these calls (`cargo run --release -p vdeflate
--example usage`); `vdeflate-tool` drives all of it from the command line
for the tests and benchmarks.

## The spec

`spec.rs` is RFC 1951 as a decoding function over the stream's bits:
`inflate(b)` is the output, the number of bits the stream took, and whether
zlib 1.3 also accepts the stream. It reads the RFC as leniently as the RFC
allows, and where zlib is stricter the stream decodes the same with the flag
off:

* an incomplete Huffman code: the RFC does not forbid one; zlib refuses any
  but a lit/length or distance code with a single code of length 1;
* HDIST > 29 (31 or 32 distance codes): the RFC allows up to 32, zlib 30.

In the format model of our EXI codecs (to be published; a relation between values and
bits, with sound and complete decoding), DEFLATE's relation is
`deflate_rel(a, c)`: the bits `c` are, exactly, a stream of `a`. `inflate`
is sound and complete for it (`agree.rs`): the bits it consumes are a
stream of what it returns (`lemma_inflate_sound`), and a stream decodes to
what it is a stream of whatever follows it (`lemma_inflate_complete`). So a
DEFLATE stream delimits itself, which is what zlib and gzip framing and
streaming rely on. There is no canonical encoding (any compressor's output
is as good as any other's), so the model's canonical-encoding flag has no
counterpart; the spec's flag is zlib's acceptance instead.

Refused by the RFC, and so by the spec: over-subscribed codes, HLIT > 29,
lit/length symbols 286 and 287, distance symbols 30 and 31, a distance back
past the first byte, a dynamic block with no end-of-block code, a repeat
code 16 with nothing to repeat, a run of lengths past HLIT + HDIST, a stored
block whose NLEN is not LEN's complement, block type 3. Huffman codes are
RFC 1951 3.2.2's canonical codes, and a symbol is the one whose code the bits
start with, trying lengths from 1 up.

`wrap.rs` specifies zlib and gzip over bytes around it: headers (for gzip
FEXTRA, FNAME, FCOMMENT and FHCRC), and trailers checked against Adler-32 and
CRC-32, themselves specified from their definitions (CRC-32 bit by bit).

## The theorems

For every input (`inflate.rs`, `wrap.rs`):

* `inflate_raw(buf, max_out)` returns `Ok((out, bits, zlib))` exactly when
  `inflate(lbits(buf)) == Some((out, bits, zlib))`; `Err(Bad)` only when the
  spec has no result; `Err(TooBig)` only when the spec's output is longer
  than `max_out` (or there is none). `inflate_raw_into` is the same into a
  caller's buffer. `inflate_zlib` and `inflate_gzip` are the same for
  `zlib_decode` and `gzip_decode`, and `inflate_gzip_file` for
  `gzip_file`: one or more members to the end of the input, as `gzip -d`
  reads a file; `inflate_zlib_dict` for `zlib_decode_dict`, a zlib stream
  with a preset dictionary (FDICT: the dictionary's Adler-32 in the header,
  and the DEFLATE stream decoded as if the dictionary came before it,
  `inflate_raw_after`).
* It never panics, and does not overflow.

For streaming (`stream.rs`): `Inflater::feed(chunk, sink)` takes the next
piece of input, decodes as far as it allows, and appends the output to
`sink`. Its verdict holds for every stream that starts with all the input so
far:

* `Done { bits, zlib }`: every such stream decodes (by the spec) to all the
  output sent to the sink, in `bits` bits;
* `NeedMore`: the input so far is not a whole stream, and the output sent so
  far starts the output of every stream that does start with it;
* `Bad`: no stream that starts with the input so far decodes;
* `TooBig`: every one that does has output longer than the limit.

So however a stream is cut into pieces, feeding them in turn ends in `Done`
exactly when the spec decodes the whole of it, with its result. Between
pieces the decoder keeps only the input it has not finished with (after
`NeedMore`, less than one step: a symbol is at most 48 bits, a dynamic
header at most 7100) and the last 32768 bytes of output, which is as far
back as a distance reaches.

`ZInflater::feed` (`zstream.rs`) is the same for zlib streams and gzip
members: its verdict holds for every byte stream that starts with the input
so far. `Done { n }`: each is, by `zlib_decode` (`gzip_decode`), all the
output sent, in `n` bytes; `Bad`: none decodes; `TooBig`: each that does
has more output than the limit; `NeedMore`: the input so far is not a whole
member. So feeding a member in any pieces ends in `Done` with its
`zlib_decode` (`gzip_decode`) result, or `TooBig`. It keeps the
header until it is whole (a gzip header's name and comment have no bound),
then what the `Inflater` keeps, then at most 8 trailer bytes, and carries
Adler-32 or CRC-32 along the output.

For compression (`enc.rs`, `enc2.rs`, `wrap.rs`), for every input of less
than 2^28 bytes:

* `deflate(data)` (and `deflate_level(data, level(n))`, for zlib's levels
  1 and 6) returns a stream that every stream starting with it decodes (by
  the spec) to `data`, with the zlib flag on, in bits that end in its last
  byte (`deflate_ok`);
  `deflate_fixed` the same with fixed codes only;
* `deflate_zlib(data, lv)` and `deflate_gzip(data, lv)` return `o` with
  `zlib_decode(o)` (and `gzip_decode(o)`) `== Some((data, o.len(), true))`:
  the trailers are right, the stream takes all of `o`, and zlib accepts it.

For streaming compression (`deflater.rs`): `Deflater::feed(chunk)` returns
the output it has finished and `finish()` the rest; however the input is cut
into pieces, all the output in order satisfies `deflate_ok` for all the
input. Between calls it keeps at most 131,330 bytes of input (`win_max`: 32K
to 64K already compressed, for matches to reach back into, and at most 64K
and a match's length not yet compressed), the hash chains and less than a
byte of output. `ZDeflater` is the same inside a zlib stream or a gzip
member: the header from `new`, then every piece of output, then `finish`'s,
is `o` with `zlib_decode(o)` (or `gzip_decode(o)`) `== Some((input,
o.len(), _))`; Adler-32 and CRC-32 are carried along the input
(`adler_run_x`, `crc_run_x` with `lemma_crc_run_append`).

So zlib accepts everything vdeflate writes, as far as the spec's flag says
what zlib accepts (which the differential tests check): a dynamic block is
written only when its three codes pass zlib's rule (`zlib_ok_x`: complete,
or empty, or a single code of length 1), with 30 distance codes at most;
otherwise the block goes out fixed or stored.

`cargo verus verify -p vdeflate` checks 665 obligations with 0 errors, in
about 15 s. There is no `assume`, `admit`, `external_body` or raised rlimit
in the crate (the primitives it takes from vsimd are trusted there; see
"What is trusted").

## How it is proved

* `huff.rs`: the canonical code table (`puff.c`'s: codes per length and
  symbols sorted by length), and a bit-at-a-time decoder proved to compute
  the spec's search, without needing prefix-freeness. A 1024-entry table
  for codes of up to 10 bits, built one window length at a time (a window of
  `k + 1` bits has the entry of its first `k` if that has a code, else a code
  of exactly `k + 1` bits or none), each entry proved to be the spec's symbol
  for its window. Longer codes fall back to the bit-at-a-time decoder
  (`decode_from`, which can start at any length: `build_table_c` also gives
  each window without a code the code of its bits so far, which vbrotli's
  tables keep so that a miss resumes past the table's width).
* `inflate.rs`: the block decoder. The bits come from a 56-bit window kept
  across symbols (one length, its extra bits, a distance code and its extra
  bits fit in 48). The output is a buffer with scratch space after it, so
  literals are stores and matches copy 8 bytes at a time when the distance
  allows (and from the least multiple of the distance that does, when it is
  shorter), proved against a characterisation of LZ77 copying.
* `step.rs`: the spec in steps (a symbol, a block header, a stored or
  dynamic header), with lemmas that a step depends only on the bits it reads
  and reads a bounded number of them, that a block decodes the same from
  the last 32K of output, and `shift.rs`: that decoding from bit `p` is
  decoding from bit `p - k` of the stream with its first `k` bits dropped.
  `agree.rs`: a stream that has another's bits up to where the other's
  decoding ends decodes the same (so a verdict of the streaming zlib and
  gzip decoder on a prefix is not undone by more input).
  The symbol loop (`syms_run`) is proved for every stream that starts with
  the input it has, which is what streaming needs; the whole-buffer decoder
  is that loop with its input taken as the whole stream.

* `enc.rs`: an LSB-first bit writer, proved to append the bits it is
  given; canonical codes from code lengths, and the lemma that a symbol's
  code, bit-reversed and written, decodes back to it under the spec's
  search (no shorter code of the canonical code is a prefix of it).
* `enc2.rs`: LZ77 tokens from hash chains with zlib's parameters (at level
  6: 128 deep, stop at 128, lazy matching below 16, a quarter of the chain
  after a match of 8, chains of four-byte hashes with a table of three-byte
  ones as libdeflate has; at level 1: 4 deep, stop at 8, no lazy matching,
  three-byte hashes), each carrying a proof that it is a literal or a match
  the output so far already has. Per block (up to 32768 tokens), Huffman code
  lengths from the symbol counts, limited to 15 and repaired to a complete
  code, then checked at run time (not over-subscribed, end-of-block coded,
  every token's symbols coded); a block goes out with fixed codes when the
  check fails or fixed codes are smaller, and stored (its bytes as they
  are, up to 65535) when that is smaller still. The header writes the
  lengths as zlib does (runs of zeros as 17 and 18, repeats as 16) with a code length
  code over all 19 symbols (lengths 1 to 7, so every op has a code, which
  keeps the proof from depending on which ops occur); each op is proved to
  extend what `read_lens` reads by the lengths it stands for. The block's
  symbols are proved to decode by the lemmas above, and the stream by
  induction over blocks. Nothing needs the heuristics to be right.
* `wrap.rs`: the zlib and gzip framing around it, with Adler-32 and CRC-32
  computed by the functions the decoder already checks against.
* `deflater.rs`: the same blocks from a sliding window. The bit writer
  carries the bytes already handed out as a ghost prefix, so the writing
  proofs, which speak of all the bits from the start of the stream, did not
  change; the writers take the input as a ghost sequence, and a token found
  in the window is a token of the whole input (`lemma_toks_lift`).

## Proof engineering

What made the proofs go through, and what did not:

* The spec is a function, and every streaming theorem is about all the
  streams that start with the input so far (`is_prefix(b, f) ==> ...`).
  Decoding a piece is then the same proof as decoding the whole: the
  whole-buffer decoder is the streaming loop with its input taken as all of
  it.
* Heuristics are not proved; their results are checked. Code lengths,
  code-length codes, the choice of block type and the length and distance
  symbol tables are computed by unverified code and checked before use (a
  failed check falls back to fixed codes), and every match is compared
  byte by byte. So tuning the compressor (lazy matching, four-byte hashes,
  levels) needed no new proofs.
* Ghost state instead of new invariants: the bit writer carries the bytes
  already handed out as a ghost prefix, so its bits are always all the bits
  from the start of the stream, and the block writers' proofs did not change
  when streaming came.
* Large recursive specs (`inflate_blocks`, `gzip_decode`, the table
  invariant) are hidden (`hide`, `#[verifier::opaque]`) wherever a function
  only passes facts about them along, with one-step unfolding lemmas where
  it needs them; functions whose goals are large get their own solver
  instance (`spinoff_prover`). No rlimit is raised.
* Loops forget what they do not restate: every fact about the variables a
  loop does not touch goes into its invariant.
* Where a fact was hard to prove and cheap to check (the output of a member
  fitting what is left of the limit, a code being one zlib accepts), the
  code checks it, and the proof uses the check.

## What is trusted

* The spec's faithfulness to the RFCs. The proofs cannot check it; the
  differential tests do (`difftest/deflate/`, below).
* Verus, Z3, the Rust compiler, and the vstd specifications of the few std
  functions used (`Vec` push/resize/truncate/append, `copy_within`,
  `mem::swap`).
* From `vsimd` (`../vsimd`), the contracts of the primitives the decoder
  and the checksums call: `mem::vset`, `copy8`, `copy16`, `store_u64le`,
  `load_u64le` (unchecked accesses, in bounds by their preconditions,
  which Verus checks at every call), and the SSE2 intrinsics of Adler-32
  (`loadu`, `setzero`, `from_bytes`, `to_bytes`, `unpacklo_epi8`,
  `unpackhi_epi8`, `sad_epu8`, `madd_epi16`, `add_epi32`). Each is
  `external_body` in vsimd, not here, and `vsimd/tests/validate.rs` checks
  each against the CPU through its proved model.

Not trusted: the compressor's heuristics (match finding, code lengths,
the choice of block type). What they produce is checked before it is
written, or cannot be wrong (every match is compared byte by byte).

## Results

`cargo test -p vdeflate` needs nothing but Rust: it checks 386 streams
frozen from the differential tests below (zlib's verdict, data and end for
each, `difftest/deflate/mkvec.py`), whole and in pieces, round trips at
every level, and the checksums against bit-at-a-time implementations at
the lengths where their fast paths change.

Differential tests (`difftest/deflate/README.md`): 120,000 streams zlib
wrote and their mutants, and 480,000 streamed decodes of them in random
pieces, against zlib: 0 disagreements, and every stream decoded with the
zlib flag off is one zlib refuses. 26 hand-built streams at the points where
decoders differ; 6,000 zlib and gzip streams against Python's zlib. Against
zlib, miniz_oxide and libdeflate together: libdeflate 1.26.1 decodes three
kinds of stream that the RFC and zlib refuse (see there).

Speed, on Silesia compressed by zlib -6 and on the image data (IDAT) of six
Kodak PNGs, one core of an AMD Ryzen 9 9950X3D, the fastest of 10 rounds
(`bench/deflate`, decoders timed in turn), in MB/s of output (2026-10-05,
branch `deflate-speed`):

| file | vdeflate | into a buffer | zlib | miniz_oxide | libdeflate | into ÷ libdeflate |
|---|---|---|---|---|---|---|
| dickens | 1003 | 1127 | 508 | 580 | 1356 | 0.83 |
| mozilla | 908 | 1017 | 554 | 597 | 1282 | 0.79 |
| mr | 1099 | 1121 | 580 | 710 | 1394 | 0.80 |
| nci | 2383 | 3566 | 1775 | 1547 | 4450 | 0.80 |
| ooffice | 667 | 680 | 374 | 464 | 856 | 0.79 |
| osdb | 1310 | 1342 | 688 | 881 | 1718 | 0.78 |
| reymont | 1416 | 1472 | 623 | 751 | 1814 | 0.81 |
| samba | 1568 | 1628 | 811 | 962 | 2019 | 0.81 |
| sao | 626 | 640 | 484 | 492 | 799 | 0.80 |
| webster | 994 | 1302 | 583 | 665 | 1588 | 0.82 |
| xml | 2567 | 2794 | 1279 | 1654 | 3461 | 0.81 |
| x-ray | 537 | 547 | 366 | 398 | 682 | 0.80 |
| kodim01 | 624 | 634 | 426 | 415 | 780 | 0.81 |
| kodim04 | 605 | 613 | 450 | 472 | 797 | 0.77 |
| kodim08 | 540 | 547 | 399 | 421 | 726 | 0.75 |
| kodim13 | 533 | 538 | 374 | 365 | 653 | 0.82 |
| kodim20 | 912 | 920 | 511 | 570 | 1136 | 0.81 |
| kodim23 | 646 | 652 | 467 | 481 | 839 | 0.78 |

`vdeflate` is `inflate_raw` (a new `Vec`, as miniz_oxide's
`decompress_to_vec`): 1.27 to 1.89 of miniz_oxide. "Into a buffer" is
`inflate_raw_into` with a buffer reused across calls, as zlib and libdeflate
are timed here: 1.32 to 2.36 of zlib, 0.75 to 0.83 of libdeflate. Before
the branch, on the same machine, into a buffer was 0.48 to 0.65 of
libdeflate (dickens 741, kodim01 459). See "The fast loop" below. The
tables earlier in this file's history were measured on another machine
(an Intel Xeon), so they do not compare with these. For lean-zip, measured
on that machine, see below.

The checksums, one core, on dickens: CRC-32 3.7 GB/s (eight bytes a step;
it was 0.66), Adler-32 21 GB/s (sixteen bytes a step in SSE2; it was 5.2).
libdeflate's, with PCLMULQDQ and AVX2/VNNI, are 68 and 96 GB/s. Through
vpng (our verified PNG decoder, to be published), six Kodak images decode at 115 MP/s (78 before the branch).

Compression (on the Xeon of the earlier decoding tables), Silesia, one core (`VD_LEVEL=n vdeflate-tool --compress`;
zlib 1.3 through Python's `zlib.compress`; the faster of two runs, in the
same session), sizes in bytes:

| file | level 6 | MB/s | zlib -6 | MB/s | level 1 | MB/s | zlib -1 | MB/s |
|---|---|---|---|---|---|---|---|---|
| dickens | 3,858,717 | 20 | 3,871,628 | 17 | 4,581,211 | 58 | 4,585,612 | 84 |
| mozilla | 19,166,690 | 26 | 19,089,118 | 27 | 20,693,873 | 55 | 20,577,220 | 78 |
| mr | 3,685,652 | 21 | 3,675,935 | 20 | 3,850,491 | 70 | 3,828,360 | 99 |
| nci | 3,187,517 | 70 | 3,200,182 | 87 | 4,627,205 | 207 | 4,624,591 | 233 |
| ooffice | 3,093,299 | 23 | 3,097,288 | 20 | 3,294,461 | 38 | 3,290,526 | 56 |
| osdb | 3,664,007 | 39 | 3,695,164 | 38 | 4,066,207 | 64 | 4,076,385 | 90 |
| reymont | 1,845,783 | 16 | 1,860,865 | 20 | 2,376,513 | 72 | 2,376,424 | 97 |
| samba | 5,463,441 | 38 | 5,451,399 | 43 | 6,349,391 | 81 | 6,329,449 | 120 |
| sao | 5,322,068 | 19 | 5,331,793 | 18 | 5,568,688 | 31 | 5,567,768 | 46 |
| webster | 12,192,284 | 28 | 12,213,941 | 28 | 14,972,996 | 72 | 14,991,236 | 98 |
| x-ray | 6,024,185 | 26 | 6,045,111 | 20 | 6,028,416 | 37 | 6,033,926 | 40 |
| xml | 691,732 | 60 | 687,991 | 60 | 967,376 | 151 | 965,242 | 183 |
| total | 68,195,375 | | 68,220,415 | | 77,376,828 | | 77,246,739 | |

`deflate_level(data, level(n))` takes zlib's parameters for each level
(`deflate` is level 6). Level 6 is 0.04% smaller than zlib -6 in all, at
0.80 to 1.34 of its speed per file (about the same over all of Silesia);
level 1 is 0.17% larger than zlib -1, at 0.67 to 0.92 of its speed. Every
level over all of Silesia (size in bytes, seconds for all twelve files):

| level | vdeflate | s | zlib | s |
|---|---|---|---|---|
| 1 | 77,376,828 | 3.3 | 77,246,739 | 2.4 |
| 2 | 75,116,237 | 3.4 | 74,994,548 | 2.6 |
| 3 | 73,062,810 | 4.6 | 72,966,202 | 3.3 |
| 4 | 70,354,274 | 4.7 | 70,989,992 | 3.4 |
| 5 | 68,759,368 | 5.9 | 69,151,486 | 4.7 |
| 6 | 68,195,375 | 7.2 | 68,220,415 | 7.2 |
| 7 | 67,995,836 | 9.0 | 67,935,737 | 8.8 |
| 8 | 67,832,270 | 13.8 | 67,685,986 | 14.1 |
| 9 | 67,799,056 | 19.1 | 67,643,201 | 17.9 |

Levels 4 and 5 are smaller than zlib's (the four-byte chains), the rest
within 0.25%; levels 6 to 9 run at zlib's speed, 1 to 5 at about 0.75 of it.
On `encdiff.py`'s small random inputs (mostly 1 KB to 64 KB), level 6 is
0.7% larger than zlib -6 and level 1 0.4% larger than zlib -1; 3 MB of
random bytes come to 3,000,460 bytes (zlib -6: 3,000,920). zlib decodes
all of it, at both levels, raw, zlib and gzip (`difftest/deflate/encdiff.py
--wrap`, `VD_LEVEL`), with 0 failures; `gzip -d` decodes the gzip output;
miniz_oxide and libdeflate decode it too (`encall.py`: 4,500 files and
Silesia, all four decoders give back the input).
The streaming compressor (`VD_STREAM=N`: pieces of 1 to N bytes) on 1,000
inputs for each N in 1, 7, 300, 70000 at both levels, and on Silesia in
pieces of up to 64K: zlib decodes all of it, 0 failures; Silesia comes to
68,097,062 bytes (blocks end at 64K of input), keeping at most 131,005
bytes of input. `ZDeflater` in zlib and gzip, 700 inputs for each N in 1,
300, 70000: 0 failures; webster in 64K pieces as gzip passes `gzip -t`.

Later (2026-09-28), two changes carried over from the Brotli decoder's
speed work: Adler-32 is summed without a remainder inside each 64 KB (the
sums stay below 2^42 in 64 bits) and sixteen bytes at a time from a slice
of sixteen, reduced once per 64 KB (`adler_run_x`; each step keeps the
sums congruent to the spec's); and the streaming decoder takes input
pieces, sends output and drops used input with one copy each
(`extend_from_slice`) instead of a push per byte; and `inflate_raw` takes
its first buffer from `vec!` (fresh pages come zeroed and are not filled
again). 3 MB of dickens as zlib (level 6), in instructions: whole-buffer
`inflate_zlib` 141.3M to 108.4M;
`ZInflater` in pieces of up to 64 KB 205.7M to 117.1M. `difftest/deflate/
all.sh`: 0 failures.

## Size

Lines of each kind (`tools/loc.py`, by brace tracking: spec functions and
`requires`/`ensures`/`invariant`/`decreases` clauses are spec; proof
functions, `proof` blocks and `assert`s are proof; the rest of the code is
exec; comments and blank lines are not counted):

| part | files | spec | proof | exec |
|---|---|---|---|---|
| RFC 1951 spec | `spec.rs` | 298 | 9 | 0 |
| bits (LSB view) | `vbits/src/lsb.rs` | 34 | 243 | 39 |
| decoder | `huff.rs`, `inflate.rs`, `step.rs`, `shift.rs`, `agree.rs` | 445 | 1,800 | 715 |
| streaming decoder | `stream.rs` | 238 | 796 | 424 |
| zlib and gzip, whole, both ways | `wrap.rs` | 281 | 276 | 301 |
| zlib and gzip, streaming decoder | `zstream.rs` | 145 | 302 | 246 |
| compressor | `enc.rs`, `enc2.rs` | 593 | 861 | 951 |
| streaming compressor, raw and wrapped | `deflater.rs` | 121 | 113 | 189 |
| total (with `lib.rs`) | | 2,155 | 4,400 | 2,879 |

Proof is 1.5 times the exec code. Verification takes about 15 s on one
machine (505 obligations; 665, in about 20 s, after the speed work of
`deflate-speed`, which the line counts above do not include).

## Against lean-zip

lean-zip (Lean 4, github.com/kim-em/lean-zip at 2f7a63f, built here with its
toolchain v4.35.0-rc2 and its default LTO flags; driver `LzTime.lean`
calling its production `Zip.Native.Inflate.inflate` and `deflateRaw`), on
the same machine as the tables above, fastest of 10 runs (decoding) or 2
(compressing).

Decoding the same zlib -6 Silesia streams, MB/s (vdeflate is `inflate_raw`,
which like lean-zip's `inflate` allocates its output):

| file | lean-zip | vdeflate | ratio |
|---|---|---|---|
| dickens | 168 | 290 | 1.72 |
| mozilla | 165 | 316 | 1.92 |
| mr | 177 | 374 | 2.11 |
| nci | 648 | 766 | 1.18 |
| ooffice | 125 | 258 | 2.06 |
| osdb | 209 | 410 | 1.97 |
| reymont | 164 | 396 | 2.41 |
| samba | 271 | 493 | 1.82 |
| sao | 110 | 235 | 2.12 |
| webster | 206 | 307 | 1.49 |
| x-ray | 93 | 206 | 2.21 |
| xml | 482 | 760 | 1.58 |

vdeflate decodes 1.18 to 2.41 times as fast. Compressing, sizes in bytes:

| file | lean-zip -6 | MB/s | vdeflate 6 | MB/s | lean-zip -1 | MB/s | vdeflate 1 | MB/s |
|---|---|---|---|---|---|---|---|---|
| dickens | 3,866,688 | 25 | 3,858,717 | 20 | 4,684,894 | 150 | 4,581,211 | 58 |
| mozilla | 18,891,004 | 23 | 19,166,690 | 26 | 22,247,838 | 178 | 20,693,873 | 55 |
| mr | 3,598,727 | 28 | 3,685,652 | 21 | 4,081,860 | 192 | 3,850,491 | 70 |
| nci | 3,181,189 | 75 | 3,187,517 | 70 | 4,474,435 | 536 | 4,627,205 | 207 |
| ooffice | 3,089,434 | 20 | 3,093,299 | 23 | 3,506,542 | 124 | 3,294,461 | 38 |
| osdb | 3,662,822 | 36 | 3,664,007 | 39 | 4,038,239 | 226 | 4,066,207 | 64 |
| reymont | 1,879,442 | 28 | 1,845,783 | 16 | 2,568,089 | 195 | 2,376,513 | 72 |
| samba | 5,428,436 | 39 | 5,463,441 | 38 | 6,948,114 | 249 | 6,349,391 | 81 |
| sao | 5,349,719 | 18 | 5,322,068 | 19 | 5,751,357 | 99 | 5,568,688 | 31 |
| webster | 12,186,137 | 37 | 12,192,284 | 28 | 15,366,624 | 168 | 14,972,996 | 72 |
| x-ray | 6,036,525 | 19 | 6,024,185 | 26 | 6,551,112 | 74 | 6,028,416 | 37 |
| xml | 692,061 | 44 | 691,732 | 60 | 1,024,862 | 386 | 967,376 | 151 |
| total | 67,862,184 | | 68,195,375 | | 81,243,966 | | 77,376,828 | |

At level 6, lean-zip's output is 0.5% smaller (it has block splitting and
adaptive per-input parameters), and vdeflate is 0.57 to 1.38 times as fast
(these compression runs are from the same session as the zlib ones above).
At level 1, vdeflate's output is 4.8% smaller and lean-zip is 2.0 to 3.5
times as fast. lean-zip has no streaming in either direction and no bound
on memory.

## Not done

* Writing preset dictionaries (FDICT streams are decoded, not written);
  several gzip members in the streaming decoder (the whole-buffer
  `inflate_gzip_file` reads them all).
* The remaining gap to libdeflate (0.75 to 0.83): per match about 70
  instructions to its 50; much of the rest is building and packing two
  tables per block (some 5% on dickens). BMI2 (`shrx`, `bzhi`) was tried
  and gave nothing measurable; libdeflate's subtables for codes past 12
  bits, and CRC-32 by carry-less multiplication, are not done.

## The fast loop

`inflate::fast_run` is entered from `syms_run` whenever at least 8 bytes of
input and room for a longest copy (plus 16 bytes) remain, and returns at
end-of-block or at anything it leaves to `syms_run` (errors, the ends of
the input or output); its contract is `syms_run`'s, so the streaming decoder
uses it too.

* The bit window `w` of `k` bits ends at `q`, a byte boundary; the bit
  position is `q - k` and is only ghost. Each step refills without a branch
  from the byte at `q`, to 56 to 63 bits. Past its `k` bits the window holds
  only the stream's bits or zeros (`win_hi`), so the refill ORs the new 64
  bits in without clearing the old ones (`lemma_refill_or`); after a refill
  all 64 bits are the stream's, and the ghost `s` counts those past `k`.
* The entry for the next symbol is looked up as soon as the window is past
  the last one, before the refill, which keeps the window's low bits
  (`lemma_low12`): the refill is off the lookup's path, and a run of
  literals that ends at a match does not look the entry up twice. This
  was the largest single step (10 to 19%).
* Up to three literals per refill (`lit_take`), or one other symbol
  (`match_take`).
* Per block, the lit/length table is packed for 12-bit windows
  (`pack_lit12`): codes of up to 12 bits, most of the long ones, are one
  lookup; its ghost entries `et` say what each packed entry is (`lt_ok`).
  A length or distance entry holds its base, code length and total bits,
  the total in the low byte so that the shift past a symbol takes the entry
  as its count; one test (`>= 2^30`) finds end-of-block and missing
  entries (`NO_LIT`). A code past 12 bits goes to `other1`, out of line,
  which resumes the canonical search at 11 bits from what the 10-bit table
  kept (`decode_resume`).
* Copies are whole 16-byte moves from 16 or more back and 8-byte ones from
  8 to 15, the first 32 bytes without a test of the length; below 8 back,
  moves step by the distance until a multiple of it is in place
  (`fast_copy`). Literals are stored, and the input loaded, without bounds
  checks (`vsimd::mem`, trusted, in bounds by their preconditions).

Measured and kept only with paired timing (`tools/deflate/ab`, and
`bench/deflate` runs interleaved): refilling from the bit position before
every symbol was 20% slower than the old loop despite fewer instructions
(the load was on the critical path), and helper functions taking `&mut`
state kept `k` in memory until the position was made ghost. Tried and
dropped: BMI2 (no gain), 8-byte copies from 16 or more back (3% slower), a
table of masks for the extra bits (1 to 3% slower). Removing the copies
altogether changed nothing: the samples at the copy's store are where the
loop waits, not what it waits for.
