# vbrotli: a verified Brotli decoder

vbrotli decodes Brotli streams (RFC 7932), whole or in pieces, with a proof
in Verus that it computes what the RFC says. Streaming runs in bounded
memory. As far as we know it is the first verified
Brotli decoder. It is built on `vbits`' LSB-first bit view and on
vdeflate's canonical prefix codes, which Brotli shares with DEFLATE.

## Using it

```rust
// Ok((data, bytes the stream took)), or Err(Bad | TooBig).
let (data, used) = vbrotli::decompress(&stream, 1 << 30)?;

// Into a buffer kept from stream to stream: the data is buf[..n].
let mut buf = Vec::new();
let (n, used) = vbrotli::decompress_into(&stream, 1 << 30, &mut buf)?;

// In pieces of any size, in bounded memory.
let mut d = vbrotli::Decompressor::new(1 << 30);
let mut data = Vec::new();
for piece in pieces {
    match d.feed(piece, &mut data)? {
        vbrotli::Status::Done { bits } => break,
        vbrotli::Status::NeedMore => {}
    }
}
```

`cargo run --release -p vbrotli --example usage` runs these on a small
stream. `vbrotli-tool dec FILE` does the same from the command line;
`vbrotli-tool batch` drives it for the tests.

## The spec

`spec.rs` is RFC 7932 as a decoding function over the stream's bits:
`brotli(dict, b)` is the output, the number of bits the stream took, and
whether Google's decoder (1.2.0) also accepts the stream. It covers the
whole format: WBITS; meta-block headers (ISLAST, ISLASTEMPTY, MNIBBLES,
MLEN, ISUNCOMPRESSED, metadata); simple and complex prefix codes (the code
length code in its fixed code, repeats of 16 and 17 that extend each
other); block types and counts; NPOSTFIX and NDIRECT; context modes and
context maps (runs of zeros, inverse move-to-front); insert-and-copy
commands; distances with the ring of the last four; and dictionary
references with the 121 transforms.

The static dictionary is a parameter. The spec holds for any byte sequence
laid out as the RFC's (`dict_ok`: 122,784 bytes, words of lengths 4 to 24,
2^NDBITS[len] of each), and nothing in it depends on what the words are.
The decoder is handed Google's `dictionary.bin`, which a test checks byte
for byte against the RFC's Appendix A. The transforms, the context lookup
tables and NDBITS are part of the spec: `tables.rs` is generated from the
RFC's text (`tools/brotli/gentables.py`, which checks the RFC's CRC-32s of
them), and each table is a spec sequence and an exec constant proved equal.

The spec rejects a stream exactly where the RFC says a decoder should
("should be rejected as invalid", "must be zero", "must not be used"), and
where the RFC's algorithm has no step to take: a block count used up in a
category with one block type (possible only after 2^24 commands that
output nothing). Two "must"s constrain encoders and are not checked, as
Google's decoder does not check them either: that NTREES is the number of
distinct values of a context map, and that NBLTYPES is the largest block
type used plus one. Neither changes what a stream decodes to.

Where Google's decoder is stricter, the stream decodes the same with the
flag off: it refuses a dictionary word that transforms to nothing at a
distance of at most 120. With the RFC's layout this cannot happen (a word
transforms to nothing only under a transform of id 42 or more, which puts
the distance past 42 x 1024), so on every stream the spec and Google's
decoder agree, as far as the tests and a reading of decode.c show.

## The theorem

For every input and output limit (`dec.rs`), `brotli_x(dict, buf,
max_out)` with `dict_ok(dict)`:

* returns `Ok((out, bits, google))` exactly when `brotli(dict, lbits(buf))
  == Some((out, bits, google))`;
* returns `Err(Bad)` only when the spec has no result;
* returns `Err(TooBig)` only when the spec's output is longer than
  `max_out` (or there is none). The limit is checked before each
  meta-block against its MLEN, so the output buffer never grows past it.
* It never panics, and does not overflow.

`cargo verus verify -p vbrotli` checks 395 obligations with 0 errors, in
about 22 s (the streaming decoder included). There is no `assume`,
`admit`, `external_body` or raised rlimit in the crate.

## How it is proved

The decoder has one exec function for each spec function, in the same
order, each proved to compute its spec function on `lbits(input)`; a spec
recursion becomes a loop whose invariant is that the spec's result from
the loop's state is the result from the start.

* `code.rs`: bit fields and prefix codes. A `Dec` decodes a symbol as the
  spec's `dsym` does: vdeflate's table (generalized for this crate to
  alphabets of 1024 symbols, and to tables only as wide as the code's
  longest code) or, for a code of one symbol, no bits.
* `br.rs`: a window of up to 56 bits kept across fields and symbols in the
  command loop, with `need`, `take` and `sym` proved against `getbits` and
  `dsym` (vdeflate's `win_k` reasoning).
* `hdr.rs`: block counts, context maps (the inverse move-to-front proved
  against the spec's recursive definition), categories and the whole
  header. `XHdr` carries the facts the command loop needs: every context
  map value names a code that exists, modes are below 4, each code's
  alphabet has its size.
* `dict.rs`: dictionary words (DOFFSET proved equal to the spec's
  recursion, one length at a time) and the transforms.
* `cmd.rs`: block switches, literal context IDs, literals, distances,
  copies and dictionary references, and the command loop, with the spec's
  lexicographic measure (output left, bits left, commands left in the
  block). The output is the start of a buffer grown once per meta-block,
  so literals are stores and copies are vdeflate's `copy_match`, 8 bytes
  at a time. A block type whose contexts all map to one code skips the
  context (`XHdr.triv`, proved against the context map). The ring only ever holds distances within the window, which
  bounds every distance below 2^30.
* `dec.rs`: meta-blocks and the stream, and the output limit: a meta-block
  with data outputs at least MLEN bytes, and later meta-blocks never shrink
  the output.

Streaming rests on three more pieces:

* `moves.rs`: every step of the spec depends only on the bits it reads,
  wherever they are. `same(b1, p1, b2, p2, n)` says bits `p1..p1 + n` of
  `b1` are bits `p2..p2 + n` of `b2`, at an offset that keeps byte
  alignment; for each bit reader (fields, symbols, prefix codes, context
  maps, the header, block switches, literals, a command's head and tail) a
  lemma moves its result from one to the other, and another bounds the bits
  it reads. With offset 0 this is decoding the input so far as every stream
  that extends it; with a whole-byte offset it is decoding after dropping
  the input already used. The bound makes a failure final: a step that
  fails with that many bits in hand fails on every extension.
* `sspec.rs`: the spec from the middle of a stream. For each place the
  decoder can stop (a meta-block's start, metadata or raw bytes part way,
  a compressed header, a command's start, a command's literals, the fill
  bits after the last meta-block) a continuation `cont` gives what the
  stream decodes to from there; lemmas that one step from each leads to the
  next (a command's head to its literals, literals split into batches, a
  meta-block's header to its body), and that the output only grows (which
  is what `NeedMore` promises about output already sent).
* `stream.rs`: the decoder's invariant is that for every stream `f`
  extending the input so far, `brotli(dict, f)` is the continuation from
  its phase, position and state (or, once it has failed, that the failure
  holds for every such `f`). One method per phase makes a step and carries
  the invariant; `feed` runs them until one needs more input, and ends by a
  measure (input left, room left under the limit, the command block's
  count, a phase rank). The command code is the whole-buffer decoder's,
  over a window of the output: `pre + out.take(n)`, `pre` the output
  already dropped (ghost). After a command's head, `run_cmds` goes on
  with whole commands (literals, tail, the next head) from one bit window
  while each is there: each part commits a state the invariant holds for,
  by the same lemmas as the steps, and at anything else (input short, the
  meta-block's end, a failure to decide) it stops and the steps take over.

## Proof engineering

* The spec is split where the proofs needed it (`cmd_head`, `cmd_tail`,
  `cmd_step`, `dict_ref`), without changing what it says, so each exec
  function has a spec function of its own size; the command loop is one
  step iterated, and its state is one struct updated in place.
* Arithmetic stays linear: products and quotients by 2^NPOSTFIX are case
  splits on NPOSTFIX, so each is by a constant.
* Constant tables are proved equal to the spec's by `by (compute)`, except
  where the spec's recursion is too deep for it (DOFFSET, p2), which is
  done one entry at a time by ordinary reasoning.
* Large specs are hidden (`hide`) where a function only passes them along,
  and `Dec`'s table invariant is opaque outside `code.rs`, so lists of codes
  can be reasoned about whole; quantifiers over them trigger on the element
  (`#![trigger v[i]]`).
* One fact was cheaper to check than to prove: that inverse move-to-front
  keeps context map values below NTREES. The spec refuses a map that breaks
  it, marked as not reached, and the decoder checks it once per map.
* The streaming invariant's quantifier over all extensions is one opaque
  predicate over the values it depends on (`promise`), carried from phase
  to phase by three lemmas (the same continuation, none, or too long), so
  each step's proof sees only its own facts. `cont` is stated for each
  phase by its own lemma with the other phases hidden.
* Verus fails (an internal error) when a function hides a spec function it
  never mentions, or one already opaque; hides are kept to the functions
  that use them.

## What is trusted

* The spec's faithfulness to RFC 7932. The proofs cannot check it; the
  differential tests do (`difftest/brotli/`).
* That the decoder is handed the RFC's dictionary (`vbrotli/data/
  dictionary.bin`; `difftest/brotli/dict.py` checks it).
* Verus, Z3, the Rust compiler, and the vstd specifications of the few std
  functions used (`Vec` push/set/truncate/extend_from_slice, slices and
  their `copy_within`/`copy_from_slice`).

## Results

`cargo test -p vbrotli` needs nothing but Rust: it checks 307 streams
frozen from the differential tests below (Google's verdict, data and end
for each, `difftest/brotli/mkvec.py`), whole, into a buffer and in pieces.

Differential tests (`difftest/brotli/README.md`), with Google's C decoder
(1.2.0) as the oracle:

* Google's 45 test vectors: all decoded, by the verified decoder and by an
  executable transcription of the spec.
* 96,000 streams (Google's encoder on nine kinds of data at every quality,
  window, block size and mode, and their mutants), each through the
  verified decoder and through the executable spec: 0 disagreements in
  verdict, data or bytes consumed.
* 31 hand-built streams at the rules the encoder never exercises
  (metadata, fill and reserved bits, WBITS 0010001, length nibbles, simple
  codes, dictionary references): the RFC, Google and vbrotli agree on all.
* Silesia at qualities 1, 5, 9 and 11 (window 22) and at quality 5 with
  windows 16 and 24: all 72 streams decode to their files.
* The streaming decoder, fed each stream in random pieces: 96,000 bdiff
  streams (piece sizes up to 50 to 10,800 bytes) and 16,000 more (up to 1,
  7, 300 and 70,000 bytes), the 31 edge vectors at each of those sizes, the
  45 test vectors in pieces of 13 bytes, and Silesia (48 streams) in pieces
  of up to 64 KB: 0 disagreements. Between pieces it held at most 29 KB of
  input and, at window 24 (a 16 MB window), 41 MB of output buffer. After
  the speed work (whole commands per step) the bdiff runs at pieces of 1,
  300 and 70,000 bytes and all 72 Silesia streams in 64 KB pieces were
  repeated: 0 disagreements.

Speed (`bench/brotli`: vbrotli against Google's C decoder, 1.2.0, built
from the pinned source, and the Rust `brotli-decompressor` crate; each
round times every decoder once, in turn, and the table gives each one's
fastest of 10 rounds, in MB/s of output). Google's decoder and the Rust
crate write into a buffer given to them, reused from round to round;
vbrotli is timed the same way (`decompress_into`, "into"), and also as
`decompress`, which returns a new `Vec` each time ("vec": the allocation
and its zeroing cost 5 to 40%), and as the streaming decoder fed 64 KB
pieces ("stream"). Silesia at quality 11, window 22; the host is shared,
so figures move by about 10% from run to run:

| file | into | vec | stream | Google (C) | Rust crate | into / Google | into / Rust |
|---|---|---|---|---|---|---|---|
| dickens | 361 | 300 | 274 | 409 | 370 | 0.88 | 0.98 |
| mozilla | 253 | 206 | 185 | 270 | 237 | 0.94 | 1.06 |
| mr | 281 | 259 | 188 | 280 | 252 | 1.00 | 1.12 |
| nci | 1150 | 735 | 678 | 1261 | 1083 | 0.91 | 1.06 |
| ooffice | 180 | 176 | 154 | 190 | 164 | 0.94 | 1.10 |
| osdb | 350 | 328 | 283 | 327 | 302 | 1.07 | 1.16 |
| reymont | 486 | 478 | 361 | 575 | 472 | 0.85 | 1.03 |
| samba | 440 | 375 | 308 | 490 | 432 | 0.90 | 1.02 |
| sao | 165 | 154 | 138 | 154 | 144 | 1.07 | 1.15 |
| webster | 421 | 312 | 288 | 499 | 422 | 0.84 | 1.00 |
| x-ray | 148 | 139 | 122 | 152 | 141 | 0.98 | 1.06 |
| xml | 842 | 810 | 690 | 990 | 829 | 0.85 | 1.02 |

(Earlier in this round "into" ran at 0.72 to 0.94 of Google's speed and
0.85 to 1.05 of the Rust crate's; before it, with the new-`Vec` API only,
the same files ran at 0.51 to 0.84 of Google's speed and 0.60 to 0.90 of
the Rust crate's.)

At qualities 1, 5 and 9 (window 22, 7 rounds) "into" is 0.52 to 1.70 of
Google's speed and 0.94 to 2.35 of the Rust crate's: binary data (sao,
x-ray, osdb, ooffice, mr) is at 0.88 to 1.70, faster than Google's decoder
at most qualities; text with long matches (dickens, webster, reymont, xml,
samba at quality 5 and 9) at 0.61 to 0.81; nci, runs of long copies at
about 1 GB/s, at 0.52 to 0.59 in that run (0.8 to 1.0 in quieter runs of
nci alone: Google's figure there moves by 25%). Streaming is 0.45 to 1.39
of Google's one-shot speed.

A 4 KB stream (dickens, quality 11) decodes at 0.77 of Google's speed and
1.20 of the Rust crate's: per meta-block work (reading the prefix codes and
building their tables) weighs more there. Uncompressed meta-blocks copy at
about 10 GB/s (1.5 to 2 times Google's decoder).

What made the difference, measured in instructions (callgrind; `tools/
brotli/icount` on 3 MB of dickens at quality 11, `tools/brotli/icmp` for
a small corpus against Google's decoder, `tools/brotli/asm` for the count
of each instruction of a function; Google's decoder takes 52.6M):

| change | instructions |
|---|---|
| first version: a `Vec` pushed byte by byte, every field read afresh | 194.6M |
| output buffer with room, stores for literals, 8-byte copies (vdeflate's `copy_match`) | 192.6M (and faster: fewer reallocations) |
| the command loop's state updated in place, small functions inlined | 162.2M |
| a 56-bit window kept across fields and symbols (`br.rs`) | 135.1M |
| literal runs without block checks, trivial contexts, shifts | 134.4M |
| tables only as wide as each code's longest code | 132.4M (4 KB streams: about a third less) |
| the command code shared with the streaming decoder | 135.4M |
| copies 16 bytes at a time, the first outside a loop | 110.1M |
| dictionary words written straight into the output (no `Vec` per word) | 103.9M |
| the window holds only bits of the stream, so one compare checks a field (no separate bounds check); command lengths from masked tables | 99.0M |
| distance codes' bases and extra bits from a table per header | 99.4M (1 to 2% less on the other files) |
| literals keep the last two bytes in registers | 98.7M (x-ray: 4%, sao: 8% less) |
| dictionary parts copied as slices; zero vectors by `vec!` | 97.7M |
| code lengths through the bit window; a code's table width and one-symbol case from its counts; symbol lists up to the last code | 97.1M (16 KB streams: 5 to 7% less) |
| the first output buffer from `vec!` (allocator-zeroed pages, not filled again) | 94.1M |
| table entries in the decoder's format: one comparison per symbol (a code's length, 63 for none, or its one symbol with length 0) | 91.9M |
| a symbol refills the window only when its entry is longer than the bits held | 91.1M |
| the table index masked (no bounds check per symbol) | 89.6M |
| every table 10 bits wide (repeated once built), so the mask is a constant | 88.8M |
| a command with no literals reads no context bytes; a short distance code picks its ring entry by branches (the ring stays out of memory); one table per header holds each distance code's base and extra bits, direct codes included (one load, one bounds check) | 81.3M |
| command lengths from tables by row (an insert code by `c / 8`, a copy code by `8 * (c / 64) + c % 8`): no cell lookups | 78.7M |
| a table miss resumes the search past the table's bits, from the code its entry holds (`decode_from`; the slow path from 2.0M to 0.25M) | 77.4M (mr 2.4%, samba 2% less) |
| no block type and count codes for a category of one block type (never read; six 10-bit tables a meta-block fewer) | 77.9M (16 KB streams: 4.5% less) |

The streaming decoder (d3m in 64 KB pieces) went from 229.7M to 104.0M:
input pieces and output sent with one copy each instead of a push per
byte (185.3M); whole commands run in one step from one bit window
(`run_cmds`) instead of three steps each with the step loop, the phase
round trip and a window load between them (129.8M); the phase kept in a
local through a run (117.7M); its first output buffer from `vec!`
(114.2M); and the symbol and command changes above (104.0M). The table
miss change then moved it to 109.1M (the loop's registers again), though
its speed did not move beyond the host's noise. Then 98.6M: from a
command boundary, whole commands run through the whole-buffer decoder's
`command_x` with the state in locals (`run_fast`), stored once when a
command is not all there (the state before it is kept and the phase steps
go on from it); `lemma_step_advance` carries the streaming promise over
one `cmd_step`. By the clock streaming gained 2 to 7%. (The whole-buffer
loop's code did not change, but moving it to another 16-byte boundary cost
"into" 4 to 6% until functions were aligned to 64 bytes: code layout
alone moves these figures by that much.)

Tried and left out: a 704-entry command table and a 1024-entry context
table (right, but proving them with `by (compute)` brings the whole array
into the solver's context: slow and near its limit). Several changes that
do less work made the whole-buffer command loop slower, by 2 to 30%, as
the compiler's register allocation of that one large function moved (the
hot path gained spills): passing the distance ring by reference, a refill
that appends bytes to the window (inline or not), keeping the window's end
instead of its position, moving block switches, the literal loop, short
copies or a whole command out of line, boxing the decoders' tables, the
context modes as two 256-entry tables chosen per block (1 to 3% fewer
instructions on binary files, 1% more on text; streaming 3% fewer), the
ring as four slots and an index (5% more), a check before a literal run
that each store fits (2% more), the last two bytes from one slice (1%
more), long copies clear of their source as one move (`copy_within`: text
8% slower by the clock, nci no faster), and the table-miss path behind a
five-argument wrapper (4% more whole, 4% less streaming). A slow path that
started at the table's width by re-reading the bits (`decode_long`) lost
more in the loop than it saved; the one kept takes the code from the
table's entry and runs out of line. Even a change outside the loop can move it: building a code's
symbol list from the list of its symbols with a code (collected while
reading the lengths, so no pass over the alphabet; proved) cut the
header's work by a quarter but added 12 instructions to each command. With BMI2 (x86-64-v3) both decoders run about 2.5% fewer
instructions.

What is left is spread over each command's steps (about 240 instructions
a command against Google's 190 in all): bounds checks the compiler cannot
drop, spills in the command loop, and a `p` kept beside the window.

## Size

Lines of each kind (`vdeflate/tools/loc.py`):

| part | files | spec | proof | exec |
|---|---|---|---|---|
| RFC 7932 spec | `spec.rs` | 825 | 12 | 29 |
| tables | `tables.rs` | 27 | 45 | 9 |
| prefix codes, bit window | `code.rs`, `br.rs` | 162 | 207 | 397 |
| header | `hdr.rs` | 164 | 185 | 299 |
| dictionary | `dict.rs` | 37 | 154 | 77 |
| commands | `cmd.rs` | 170 | 162 | 402 |
| stream (whole) | `dec.rs` | 44 | 97 | 214 |
| steps move and are bounded | `moves.rs` | 30 | 936 | 0 |
| the spec from the middle | `sspec.rs` | 171 | 583 | 17 |
| streaming decoder | `stream.rs` | 345 | 823 | 632 |
| total (with `lib.rs`) | | 1,975 | 3,204 | 2,117 |

Proof is 1.5 times the exec code; streaming is about 60% of the proof.
## Not done

* A ring buffer for the output (streaming now keeps up to two windows and
  a meta-block).
* Speed: two-level tables (an 8-bit root, as Google's decoder has) to
  build fewer entries per code and to decode codes longer than 10 bits
  without the bit-at-a-time search; building a code's tables in fewer
  passes (small inputs); the streaming path's remaining per-command
  bookkeeping (about 30% over the whole-buffer decoder).
* An encoder.
