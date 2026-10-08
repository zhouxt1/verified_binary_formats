# lspec: canonical specs in Lean

The specs here are meant to be the judge that implementations in any verifier
answer to: Verus (vdeflate), Lean (lean-zip) and Rocq/VST for C (vpuff). Each
implementation proves it computes its own verifier's copy of the spec, and the
copies are tied back to the Lean definition (see "Bridges" below). The Lean spec
is also where theorems *about* the format are proved, so a reviewer can read
theorems instead of every definition.

DEFLATE (RFC 1951) and its containers, zlib (RFC 1950) and gzip (RFC 1952), are here so far.

## Layout

| file | what |
|---|---|
| `Lspec/Deflate/Spec.lean` | the spec: `inflate : Bits → Option Decoded`, one definition per RFC clause, with the **open points**, the places where the text is silent or ambiguous and a choice had to be made |
| `Lspec/Deflate/Wrap.lean` | zlib and gzip around `inflate`: Adler-32, CRC-32, `zlibDecode`, `zlibDecodeDict` (a preset dictionary), `gzipHeader`, `gzipDecode` (one member), `gzipFile` (members to the end), with their own **open points** |
| `Lspec/Deflate/Theorems.lean` | the RFC's own examples and tables, checked: 3.2.2's two worked examples, the 3.2.6 fixed-code table, the 3.2.5 length/distance tables' ranges, the fixed codes complete |
| `Lspec/Deflate/Prefix.lean` | 3.2.2's canonical codes are prefix-free for any lengths, so `decodeSym` returns exactly the one symbol whose code begins the bits (`decodeSym_code_iff`) |
| `Lspec/Deflate/Guards.lean` | the "not reached" guards (there for termination) hold whenever they are tested |
| `Lspec/Deflate/Puff.lean` | zlib's puff.c Huffman decoding (count/symbol tables, bit at a time) as a model, proved equal to `decodeSym (code lens)` (`decode_eq`), with puff's counts and Kraft check (`blCount_eq_cnt`, `kraft_eq_kr`) |
| `Lspec/Deflate/PuffExport.lean` | the facts `vpuff/` uses in Rocq about Huffman decoding, stated as equations with `Bool` conditions |
| `Lspec/Deflate/InflateExport.lean` | the same for the rest of `inflate`: unfolding equations, puff's length/distance tables as formulas, puff's code checks equal to `zlibOk` |
| `Lspec/Bridge/vir2lean.py`, `vir.py` | translate Verus spec functions from Verus's own VIR (`--log vir-simple`) into Lean, one fixed rule per VIR node |
| `Lspec/Bridge/Vstd.lean` | **the trusted model** of Verus spec code: integers as `Int`, vstd's `Seq` (a cons list in this vstd) as `List` with vstd's own recursions, Verus's unspecified values as a parameter `u : Unspec`, type invariants on integer parameters |
| `Lspec/Bridge/VDeflate.lean` | generated: `vdeflate/src/spec.rs` and `wrap.rs` in Lean (55 functions); `gen-vdeflate.sh --check` regenerates it from a fresh Verus run and compares |
| `Lspec/Bridge/vdeflate_hints.lean` | termination hints for the generated file (checked by Lean, not trusted) |
| `Lspec/Bridge/DeflateEq.lean` | **`Bridge.verus_inflate_eq`**: for every `u`, the Verus spec's `inflate` is `Deflate.inflate`, on verdict, data, bit count and zlib flag |
| `Lspec/Bridge/WrapEq.lean`, `WrapDeep.lean` | the same for `vdeflate/src/wrap.rs`: Adler-32, CRC-32, `zlib_decode`, `zlib_decode_dict`, `gzip_decode`, `gzip_file` |
| `Main.lean` | `lspec deflate FILE`, `lspec deflate --batch` and `lspec wrap --batch`, the specs run on files |
| `leanzip/LsDecode.lean` | a batch driver for lean-zip's spec decoder, for the cross-check below |

## Build

Lean 4.34.0, core only (no Mathlib):

    cd lspec && lake build              # checks every proof, builds bin/lspec

Every theorem uses only `propext`, `Quot.sound` and `Classical.choice`. There is
no `native_decide` and no `sorry`.

## The spec's shape

`inflate b` gives the data, the number of bits the stream took, and whether
zlib 1.3 also accepts the stream. It reads the RFC as leniently as the text
allows. Where zlib is stricter (incomplete codes, HDIST > 29), the stream
decodes the same and the flag is off. That is the same decision as
`vdeflate/src/spec.rs`, so the two can be compared exactly.

The definitions stay in a fragment that other verifiers' logics express
directly: total, first-order functions over `Nat`, `Bool`, `UInt8`, `Option`,
pairs and arrays, with structural or measured recursion. Declarative facts
("the unique symbol whose code…") are theorems, not definitions.

## Validation (`difftest/deflate/lspecdiff.py`)

The spec is executable, about 3 µs per output byte. `lspecdiff.py` runs it on
zdiff.py's streams (zlib output at every setting, plus bit-flipped, truncated
and extended mutants) and on edge.py's hand-built vectors, and checks:

- **Lean spec == vdeflate**, on every stream: the same verdict, zlib flag,
  output, length and bit count. vdeflate's decoder is proved to compute
  `vdeflate/src/spec.rs`, so this compares the Lean spec with the Verus spec.
- **Lean spec against zlib**: zlib decodes a stream iff the spec does with the
  flag on, to the same output, stopping at the same byte.
- **edge vectors**: each gets its RFC verdict, and the flag matches zlib.
- with `--leanzip TOOL`, **lean-zip's spec** (`Deflate.Spec.decode`, kim-em/lean-zip
  written independently from the RFC, with the #2586 fix): whatever it decodes
  the Lean spec decodes, and whatever the Lean spec decodes with the flag on it
  decodes, to the same output and bit count.

Results on 2026-10-06:

| run | streams | result |
|---|---|---|
| `-n 3000 --seed 7` | 12,026 | 0 failures; Lean == vdeflate on all; 13 + 5 decoded with the flag off, all refused by zlib |
| `-n 100 --leanzip … --leanzip-max 5000` | 297 compared with lean-zip | the same everywhere except edge vector "HLIT = 30": lean-zip decodes it, the RFC's range (257-286) and this spec refuse it (open point 4) |
| same, 2026-10-08, lean-zip with the #2586 fix | 301 compared with lean-zip | 0 failures; the same everywhere except edge vector "HDIST = 31": lean-zip refuses it like zlib, this spec decodes it with the flag off |

The lean-zip driver is `lsdecode` in the `leanzip/` package: `lake build
lsdecode` there with lean-zip's toolchain (v4.35.0-rc2) gives
`leanzip/.lake/build/bin/lsdecode`. lean-zip's spec is List-based and quadratic in the output size,
so `--leanzip-max` (default 20000 bytes) limits which streams it gets.

### zlib and gzip (`wrapdiff.py`, `gzmulti.py`, `zdict.py` with `--lspec`)

`lspec wrap --batch` prints what `vdeflate-tool --batch-wrap` prints, so with `--lspec`
each of the three wrapper tests also requires the Lean spec's line to equal vdeflate's,
on top of vdeflate agreeing with zlib. Results on 2026-10-08:

| run | streams | result |
|---|---|---|
| `wrapdiff.py -n 1000 --seed 2 --lspec` | 3,000 zlib streams and gzip members (all optional header fields, FHCRC, mutants) | 0 failures; Lean == vdeflate on all, both == zlib |
| `gzmulti.py -n 500 --seed 2 --lspec` | 500 multi-member gzip files | 0 failures; Lean == vdeflate on all |
| `zdict.py -n 500 --seed 2 --lspec` | 500 zlib streams with preset dictionaries | 0 failures; Lean == vdeflate on all |

## Bridges

### Verus (done): `Bridge.verus_spec_eq`

```lean
theorem verus_spec_eq (O : Oracle) (hO : WellTyped O) (b : Deflate.Bits) (v : Val) :
    RunsTo V.vdeflateProg O "vdeflate::spec::inflate" [enc (.seq .bool) b.toList] v ↔
      v = enc (.opt (.tup [.seq (.int (.u 8)), .int .nat, .bool]))
        ((Deflate.inflate b).map fun d => (outV d.out, (d.bits : Int), d.zlib))
```

Read it as: by the VIR semantics, `vdeflate::spec::inflate` on the bits `b` runs to exactly
one value, the Lean spec's result. `V.vdeflateProg` is `vdeflate/src/spec.rs` as Verus itself
elaborated it: its VIR, read by Lean. The theorem holds for every well-typed choice of the
values Verus leaves unspecified. vdeflate's Verus proofs show its decoders compute
`spec::inflate`, so with this theorem they compute the Lean spec. No `sorry`; only
`propext`, `Classical.choice`, `Quot.sound`.

The exec contracts use a few more spec functions, and they are bridged the same way
(`Bridge/ContractsEq.lean`, `Bridge/VerusDeep.lean`):

| vdeflate contract | Lean reading | theorem |
|---|---|---|
| decoders: `inflate(lbits(buf@))` | `Deflate.inflateBytes buf` | `verus_inflate_bytes_eq` (with `verus_lbits_eq`: `lbits` is `Deflate.bitsOf`) |
| compressors: `deflate_ok(data@, o@)` | `Bridge.CompressesTo data o` | `verus_deflate_ok_eq` |
| `inflate_zlib`: `zlib_decode(buf@)` | `Deflate.zlibDecode buf` | `verus_zlib_decode_eq` |
| `inflate_zlib_dict`: `zlib_decode_dict(buf@, dict@)` | `Deflate.zlibDecodeDict buf dict` | `verus_zlib_decode_dict_eq` |
| `inflate_gzip`: `gzip_decode(buf@)` | `Deflate.gzipDecode buf` | `verus_gzip_decode_eq` |
| `inflate_gzip_file`: `gzip_file(buf@)` | `Deflate.gzipFile buf` | `verus_gzip_file_eq` |

The zlib and gzip rows are in `Bridge/WrapEq.lean` (shallow = Lean spec, about 800 lines)
and `Bridge/WrapDeep.lean` (the VIR statements). The checksums are where the two specs are
written differently. Verus recurses on the last byte and reduces Adler-32's sums once at the
end; `Wrap.lean`, like the RFCs, runs forward and reduces at every step. `adler32_eq` and
`crc32_eq` show both equal to one left fold.

`CompressesTo data o`: the bits of `o`, followed by anything, decode by the Lean spec to
`data` with the zlib flag on, ending at a bit `q` in `o`'s last byte. So
`enc2::deflate_level`, `Deflater` and the other compressors are proved against the Lean spec
too. `difftest/deflate/lspecenc.py` checks it by running them: 1,000 outputs (levels 1, 6, 9,
fixed codes, streaming), each also followed by random bytes, all decode by the Lean spec as
`CompressesTo` says.

**What the link trusts**, beyond Lean's kernel and what vdeflate's proofs already trust
(Verus, Z3, rustc, vstd), all of it Lean:

| file | what | lines |
|---|---|---|
| `Lspec/VIR/Syntax.lean` | the S-expression reader, and the converter from VIR to the AST, one case per VIR form | ~430 |
| `Lspec/VIR/Load.lean` | `vir_program`: reads `vdeflate.vir` at build time into a constant | ~25 |
| `Lspec/VIR/Sem.lean` | the semantics: values, their types, `Seq` operations, operators, the big-step `Eval` | ~190 |
| `Lspec/VIR/Ty.lean` | VIR types and the Lean types they denote | ~40 |
| `Bridge/Vstd.lean`, the `Seq` recursions | vstd's `SeqInner` recursions, used by the semantics | ~80 |
| `VirSubset.lean` | extracts the reachable functions from Verus's log, with the same reader | ~50 |

Not trusted, because Lean checks it:

* **The Python translator** (`vir2lean.py`). It writes the shallow definitions
  (`VDeflate.lean`) and, per function, a proof that each one computes what `Eval` gives its
  VIR (`VDeflateValid.lean`).
* **The step lemmas** those proofs use (`VIR/Enc.lean`, `VIR/Steps.lean`).
* **Determinism** of `Eval` (`VIR/Det.lean`).
* **The DEFLATE proof** `DeflateEq.lean` (`verus_inflate_eq`, shallow = Lean spec), and the
  zlib/gzip one, `WrapEq.lean`.

`gen-vdeflate.sh --check` reruns Verus and regenerates `vdeflate.vir` (55 functions),
`VDeflate.lean` and
`VDeflateValid.lean`, and they come out byte for byte the same.

The semantics follows Verus's encoding (checked against its source, `vir/src/ast_to_sst.rs`,
`sst_to_air.rs`, `prelude.rs`):

* `Clip` per the prelude's clip axioms;
* `Truncate` arithmetic (`nat` `+`, `*`) clipped to its range, as `ast_to_sst.rs` does;
* Euclidean `div`/`mod`;
* `arbitrary::<A>()` per type;
* quantifiers over the values of the binder's type (`has_type`);
* unsigned `&`, `>>` and `^` as the bitwise operations, clipped to their type. Verus leaves
  these uninterpreted in SMT except for range axioms. The amount of a `>>` may also be a
  non-negative constant of a signed type (`c >> 1` types `1` as `i32`);
* vstd's `skip` and `take` as their definitions, `subrange(n, len)` and `subrange(0, n)`;
* integer parameters in range.

`Sem.lean`'s header lists the rules.

### Rocq/VST (done): `vpuff/`

zlib's `puff.c`, a whole inflate, is proved in VST against a contract that
mentions the Lean spec's own `Deflate.inflateBytes`: `puff()` returns 0 exactly
when the spec decodes the input with the zlib flag on and the output fits, and
then produces the spec's output and the input bytes the stream took
(`vpuff/rocq/Puff.v`, `puff_lean`). The spec comes into Rocq through
rocq-lean-import from Lean's kernel export (`lean4export`), so there is no
hand-written Rocq copy of it that is trusted: the Rocq mirror the C proofs use
is proved equal to the import. The facts that need math are proved here in Lean
(`Puff.lean`, `InflateExport.lean`); Rocq does the program logic. puff.c has
three small changes for verification (no `longjmp`, no static tables). See
`../vpuff/README.md` for those and for what it trusts.

### lean-zip (done): `LeanZipEq.leanzip_decode_eq`, `LeanZipEnc.leanzip_deflateRaw`

`leanzip/` is a separate Lake package on Lean 4.35.0-rc2, lean-zip's version. It depends on
`lspec` and on lean-zip at 2f7a63f plus our fix for kim-em/lean-zip#2586: commit d14fbee0 on
branch `feat/2586-symbol-counts` of our fork, github.com/zhouxt1/lean-zip (not submitted
upstream). The fix makes lean-zip's spec and native decoders reject
a dynamic header with more than 286 literal/length or 30 distance codes, as zlib does; at
2f7a63f lean-zip accepted HLIT 30/31 and HDIST 30/31, which was the one place it differed
from this spec. `LeanZipEq.lean` (about 1,600 lines) proves:

```lean
-- LeanZipSpec.inflate is Deflate.inflate with the HLIT check widened to
-- nlit ≤ 286 && ndist ≤ 30; nothing else changed
theorem leanzip_decode_eq (data : ByteArray) :
    Deflate.Spec.decode (bytesToBits data) =
      (LeanZipSpec.inflate (Deflate.bitsOf data.data)).map (fun d => d.out.toList)
theorem leanzip_goR_eq (data : ByteArray) :   -- also the bits left over
    decode.goR (bytesToBits data) [] =
      (LeanZipSpec.inflate (Deflate.bitsOf data.data)).map
        (fun d => (d.out.toList, (bytesToBits data).drop d.bits))
theorem LeanZipSpec.inflate_spec : LeanZipSpec.inflate b = some d → Deflate.inflate b = some d
theorem LeanZipSpec.inflate_of_zlib :
    Deflate.inflate b = some d → d.zlib = true → LeanZipSpec.inflate b = some d
theorem inflate_of_decodesTo : DecodesTo data out →
    ∃ d, Deflate.inflateBytes data.data = some d ∧ d.out = out.data
theorem decodesTo_of_inflate :
    Deflate.inflateBytes data.data = some d → d.zlib = true → DecodesTo data ⟨d.out⟩
```

So two specs written independently from RFC 1951 agree exactly on every stream zlib accepts.
Whatever lean-zip decodes, this spec decodes the same. The one difference left is HDIST 30
and 31 (31 or 32 distance codes): RFC 1951 allows them, this spec decodes them with its zlib
flag off, and lean-zip, like zlib, refuses them. Everything else matches exactly, including
the cases where both specs read the RFC leniently: incomplete codes, length 258 as 284 + 31,
and unchecked padding bits.

Along the way the proof shows lean-zip's canonical codes are this spec's (`codeFor_eq`), its
first-prefix table decoding is `decodeSym` (`decode_eq`), and its decode-then-resolve LZ77
is this spec's interleaved `inflateSyms` (`syms_eq`). It also places one difference of
style: lean-zip makes the end-of-block check when the symbols are read, not at the header,
which changes no verdict (`inflateSyms_no_eob`).

lean-zip's compressor goes through the same bridge. `LeanZipEnc.lean` composes lean-zip's
`isValidStreamFor_deflateRaw` (one stream that its spec decodes to the input) with
`leanzip_goR_eq` and `LeanZipSpec.inflate_spec`:

```lean
theorem leanzip_deflateRaw (data : ByteArray) (level : UInt8) :
    ∃ d, Deflate.inflateBytes (deflateRaw data level).data = some d ∧
      d.out = data.data ∧ (deflateRaw data level).size * 8 < d.bits + 8
```

It does not cover the zlib flag (`d.zlib`), which vdeflate proves for its own output.

`leanzip_deflateRaw` inherits 91 `_native.bv_decide` axioms from lean-zip's compressor
proofs, so it trusts Lean's compiler as well as its kernel. The decoder theorems above use
only `propext`, `Classical.choice` and `Quot.sound`.

Build: `cd lspec/leanzip && lake build` with the 4.35.0-rc2 toolchain on PATH. It builds
`lspec` with that toolchain too.
