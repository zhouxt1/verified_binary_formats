# Differential testing of vdeflate

vdeflate's decoders are proved to compute its spec (`vdeflate/src/spec.rs`),
so what these tests check is the spec: that it says what RFC 1951 (and 1950,
1952) says, and where it and zlib part, that they part as intended. The spec
decodes the RFC's reading and flags the streams zlib 1.3 also accepts.

`all.sh` runs every suite below at a small size (about 30 s) and fails if
any does.

| script | what | result |
|---|---|---|
| `zdiff.py [-n N] [--stream]` | streams zlib writes (every level, strategy, window, memory level, with sync and full flushes) and their bit-flipped, truncated and extended mutants, against zlib; `--stream` also decodes each in random pieces (1 byte, up to 7, 300, 70000) with the bounded-memory `Inflater` and compares with the whole-buffer decode | 120,000 streams (6 seeds of 5,000 and their mutants), 480,000 streamed decodes: 0 failures. Every stream decoded with the zlib flag off is one zlib refuses |
| `edge.py` | 27 hand-built streams where decoders differ, each with the RFC's verdict and zlib's | all as intended |
| `wrapdiff.py` | zlib and gzip streams (gzip with FEXTRA, FNAME, FCOMMENT, FHCRC) and mutants, against Python's zlib; with `VD_STREAM=N`, through the streaming `ZInflater` in pieces of 1 to N bytes | 6,000: 0 failures; streaming, 1,000 seeds' worth for each N in 1, 7, 300, 70000: 0 failures |
| `encdiff.py [-n N] [--wrap raw\|zlib\|gzip]` | vdeflate's compressor on zdiff's kinds of data (text, binary, random, runs, empty); zlib must decode its raw, zlib or gzip output to the input with nothing left over | 3,000 inputs in each format: 0 failures |
| `encall.py [-n N]` | vdeflate's compressor output (level 6, level 1, streamed) decoded by vdeflate, zlib, miniz_oxide and libdeflate | 4,500 files and Silesia at level 6: all four give back the input |
| `gzmulti.py [-n N]` | gzip files of 1 to 5 members and their mutants, `inflate_gzip_file` against zlib reading member after member | 6,000 files: 0 failures |
| `zdict.py [-n N]` | zlib streams with a preset dictionary (zlib's `zdict=`), mutants, wrong dictionaries, and plain streams, `inflate_zlib_dict` against zlib | 4,000 streams: 0 failures |
| `mkvec.py [-n N] [--seed S]` | freezes 386 of these streams (edge.py's, zdiff's and wrapdiff's, small, with mutants) and zlib's verdict, data and end for each into `vdeflate/tests/data/vectors.txt`, keeping a stream only where vdeflate and zlib agree as the suites require; `cargo test -p vdeflate` then checks them, whole and streamed, with no zlib | run again when the spec changes |
| `lspecdiff.py [-n N] [--leanzip TOOL]` | the Lean spec (`lspec/Lspec/Deflate/Spec.lean`) run against vdeflate (so against the Verus spec), zlib, edge.py's vectors and, with `--leanzip`, lean-zip's spec decoder; see `lspec/README.md` | 12,026 streams (`-n 3000 --seed 7`): 0 failures, Lean == vdeflate on every one |
| `lspecenc.py [-n N]` | vdeflate's compressors (levels 1, 6, 9, fixed, streaming) against `Bridge.CompressesTo`, the Lean reading of their contract: each output, alone and followed by random bytes, decodes by the Lean spec to the input with the zlib flag, ending in its last byte | 1,000 outputs (`-n 200`): 0 failures |
| `odiff.py` | vdeflate against zlib, miniz_oxide 0.8 and libdeflate 1.26.1 together, on `edge.py`'s vectors and zdiff-style streams and mutants | below |

## Where the decoders differ

On 12,026 streams (`odiff.py -n 3000 --seed 5`, at commit 153e104), all four
agree on 12,002. (The streams' data samples the repository's own files, so
the counts move a little as they change.) The rest, and the edge vectors
behind them:

| stream (`edge.py`) | RFC 1951 | vdeflate | zlib 1.3 | miniz_oxide 0.8 | libdeflate 1.26.1 |
|---|---|---|---|---|---|
| a single 1-bit distance code, and a distance coded with the unused bit 1 | invalid (no such code) | refuses | refuses | refuses | **decodes**, as distance 1 ("aaaa") |
| no distance codes at all, and a length used | invalid | refuses | refuses | refuses | **decodes**, as distance 1 ("aaaa") |
| HLIT = 30 (287 lit/length codes) | invalid (HLIT is 257 - 286) | refuses | refuses | refuses | **decodes** |
| HDIST = 31 (32 distance codes, 30 and 31 unused) | valid | decodes, zlib flag off | refuses | refuses | decodes |
| a single 2-bit distance code (incomplete) | valid | decodes, zlib flag off | refuses | **decodes** | refuses |
| two 2-bit distance codes; an incomplete lit/length code; an incomplete code length code | valid | decodes, zlib flag off | refuses | refuses | refuses |

libdeflate's first two are by design: `build_decode_table` in its
`deflate_decompress.c` maps a code with one codeword of length 1, or with none,
to a complete code in which that symbol (symbol 0, for none) has both
codewords, "for performance" and to avoid deciding whether '0' or '1' is the
right one. It does not check HLIT's range (`decompress_template.h` reads
`257 + 5 bits`), which is the third. They are parser differentials all the
same: the same bytes are an error to zlib and data to libdeflate. 9 of the
12,026 streams were such mutants: libdeflate decoded them and the other three
refused.

Python's `gzip` module is more lenient than the RFC: it decodes a member
whose FLG byte has a reserved bit set (e.g. `1f 8b 08 80 ...`), which RFC
1952 2.3.1.2 says a decoder must refuse; zlib refuses it ("unknown header
flags set"), `gzip -d` refuses it ("has flags 0x80 -- not supported"), and
so does vdeflate. `gzmulti.py` therefore takes zlib as the reference.

## Speed

`bench/deflate` times vdeflate against zlib (through flate2), miniz_oxide and
libdeflate on Silesia compressed by zlib -6, in turn on one core. See
`vdeflate/README.md`.
