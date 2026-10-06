# Differential testing of vbrotli

The spec (`vbrotli/src/spec.rs`) is RFC 7932 as a decoding function; the
verified decoder (`vbrotli::dec::brotli_x`) is proved to compute it. What these tests check is
the spec: that it says what the RFC says, and that it agrees with Google's
decoder (C library v1.2.0, `build/gdec`, built from source by `build.sh`).
Every suite runs the verified decoder whole (`--tool batch`) and
streaming (`--tool batch-stream`, each stream fed in random pieces of 1 to
`VB_STREAM` bytes), and
`vbrotli-tool batch-spec`, a transcription of spec.rs into plain Rust
function by function (`vbrotli-tool/src/specdec.rs`), which was how the
spec was tested before the decoder was proved.

`all.sh` runs every suite at a small size, for all three, and fails if any
does.

| script | what | result |
|---|---|---|
| `bdiff.py [-n N] [--seed S]` | data of nine kinds (repository text, UTF-8 text, binary, random, runs, small alphabets, long repeats, dictionary words with punctuation, empty and tiny) compressed by Google's encoder at every quality (0-11), window (10-24), block size and mode, and 3 mutants of each (bit flips, some near the headers; truncations; extensions; overwritten bytes); verdicts, data and bytes consumed compared with Google's decoder | 96,000 streams (6 seeds of 4,000 and their mutants), through each of the two: 0 failures |
| `edge.py` | 31 hand-built streams at rules Google's encoder never exercises: metadata meta-blocks (reserved bit, fill bits, length bytes, as the last), uncompressed fill bits, WBITS patterns including 0010001, length nibbles, fill bits after the last meta-block, simple codes with a repeated or out-of-range symbol, dictionary references (of length 2, past MLEN, from the first byte), inserts past MLEN | RFC, Google and the spec agree on all |
| `bdiff.py --tool batch-stream` | the same streams through the streaming decoder in random pieces | 96,000 streams (piece sizes up to 50 to 10,800 bytes) and 16,000 (up to 1, 7, 300, 70,000): 0 failures |
| `silesia.py` | Silesia compressed at qualities 1, 5, 9, 11 (window 22) and quality 5 at windows 16 and 24, decoded by vbrotli and Google, with rough timings | 72 streams: all decode to their files |
| `mkvec.py [-n N] [--seed S]` | freezes 307 streams (Google's test vectors up to 12 KB, edge.py's, bdiff's on small data, with mutants) and Google's verdict, data and end for each into `vbrotli/tests/data/vectors.txt`, keeping a stream only where vbrotli and Google agree as bdiff.py requires; `cargo test -p vbrotli` then checks them, whole and streamed, with no Google decoder | run again when the spec changes |
| `dict.py` | the static dictionary against RFC 7932 Appendix A (and its CRC-32) and Google's `dictionary.bin` | identical |

After the speed work of 2026-09-28 (16-byte copies, dictionary words and
code lengths written and read in place, the bit window's bound, streaming
by whole commands) the suites were run again on the new decoders: all.sh;
`bdiff.py` with 48,000 streams through `batch` (seeds 21 to 23) and
16,000 + 12,000 through `batch-stream` (pieces up to 1, 300, 70,000, 3,007
and 3,104 bytes); `silesia.py`; the 72 Silesia streams streamed in 64 KB
pieces; `edge.py` streamed: 0 failures. On the branch's final state:
96,000 streams through `batch` (seeds 101 to 104) and 96,000 through
`batch-stream` (seeds 111 to 114, pieces of up to 550 to 700 bytes): 0
failures.

With `VB_COVER=1`, `batch-spec` prints how often each part of the spec ran.
On 2,000 of `bdiff.py`'s compressed streams, everything is reached but
metadata meta-blocks, which `edge.py` covers: every simple code shape, code
length codes of one symbol, extended repeats of 16 and 17, context maps
with run lengths and inverse move-to-front, block switches by each kind of
symbol, every kind of distance code, NPOSTFIX > 0, and 46,674 dictionary
words (21,596 with a transform other than identity).

## Where the RFC and Google's decoder differ

No stream in these tests separates them. Reading decode.c (v1.2.0):

* Google does not check that NTREES is the number of distinct context map
  values, nor that NBLTYPES is the largest block type used plus one. The
  RFC states both as "must"s, not as grounds to reject; the spec reads them
  as constraints on encoders and does not check them either.
* Google refuses a dictionary word that transforms to nothing at a
  distance of at most 120; the RFC does not. The spec decodes it with the
  flag off. With the RFC's dictionary layout this cannot happen: a word
  transforms to nothing only under a transform of id 42 or more, which
  puts the distance past 42 x 1024.
