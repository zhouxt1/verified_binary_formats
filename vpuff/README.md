# vpuff: C against the Lean DEFLATE spec, in Rocq/VST

A second backend for the Lean spec in `lspec/`, after Verus (vdeflate) and Lean
(lean-zip). The C code is Mark Adler's `puff.c` (zlib `contrib/puff`), a whole
inflate: stored, fixed and dynamic blocks. It has three small changes for
verification (below), listed at the top of `c/puff.c`.

The contract is stated against the Lean spec itself. Its definitions come into
Rocq from Lean's own kernel export, through rocq-lean-import, and a Rocq mirror
of the spec over `Z` and lists is proved equal to them. No step depends on
testing.

## The result

`rocq/Puff.v`:

```coq
Theorem puff_lean : semax_body Vprog Gprog f_puff puff_lean_spec.
Theorem puff_bodies :   (* every function in puff.c, against the same Gprog *)
  semax_body Vprog Gprog f_bits bits_spec /\ ... /\ semax_body Vprog Gprog f_puff puff_lean_spec.
```

`puff_lean_spec` says, for an input `bytes` of at most 2^30 bytes and an output
buffer of `outlen` bytes (or `dest = NULL`, puff's mode that only measures the
output):

* puff returns 0 exactly when `Deflate.inflateBytes bytes` (`lean_inflate`) is
  `some (o, nb, true)`, i.e. the spec decodes the input with the zlib flag on,
  and `o` fits in the buffer;
* it then writes `o` to `dest`, sets `*destlen` to its length and `*sourcelen`
  to `(nb + 7) / 8`, the bytes the stream took;
* otherwise it returns nonzero.

The zlib flag is the spec's record of whether zlib would accept the stream:
the spec decodes some streams that zlib refuses (an incomplete code with one
length-1 code, a distance code over 30 symbols, ...). puff refuses the same
ones, and this is proved (`zlibOk` in the dynamic block's contract).

The sizes keep puff's unsigned counters from wrapping. In the measuring mode
the input is limited to 2,000,000 bytes, so the output stays below 2^31. A real
output buffer has at least one byte, since puff compares `dest` with `NULL` and
in C that needs a valid pointer.

## The changes to puff.c

From `c/puff.c`'s header; none changes what `puff()` returns or produces on
success. `c/test/run.sh` compares the two versions on 12,000 random and mutated
streams (return code, output, consumed input): no differences.

1. **No `setjmp`/`longjmp`**, which VST cannot verify. Running out of input sets
   a flag `s->eof`; every caller of `bits()` checks it and returns 2, as the
   `longjmp` did.
2. **`fixed()` builds its tables on every call** in local arrays, instead of once
   into static arrays guarded by a static flag.
3. **`bits()` calls come out of larger expressions** so the `eof` check can
   follow them.

## How it is put together

| layer | file | proved in |
|---|---|---|
| the spec: `inflate`, its blocks, `decodeSym`, `code`, `zlibOk` | `lspec/Lspec/Deflate/Spec.lean` | (definitions) |
| puff's Huffman algorithm (count/symbol tables, bit at a time) equals `decodeSym (code lens)`; its counts and Kraft check equal `blCount` and `kraft` | `lspec/Lspec/Deflate/Puff.lean` | Lean |
| the facts the Rocq side uses, as equations with `Bool` conditions: unfolding equations of `inflate`'s pieces, puff's length/distance tables as formulas, puff's code checks equal to `zlibOk`, ... | `lspec/Lspec/Deflate/PuffExport.lean`, `InflateExport.lean` | Lean |
| the spec, the model and those theorems in Rocq | `rocq/LeanSpec.ndjson`, `rocq/LeanSpec.v` | Lean export, then the Rocq kernel |
| Lean's `Nat`, `Bool`, arrays related to Rocq's `Z` and lists | `rocq/LeanNat.v`, `rocq/Bridge.v` | Rocq |
| a mirror of `inflate` over `Z` and lists, proved equal to the imported `Deflate.inflateBytes` (`inflateZ_eq`) | `rocq/Inflate.v`, `rocq/InflateEq.v` | Rocq |
| each C function meets its contract, stated against the mirror (and, for one symbol, the imported `decodeSym`) | `rocq/Spec_puff.v`; `rocq/Verif_*.v` with their `*Lemmas.v`, `P2_*.v`, `Codes_Dist30.v` | Rocq/VST |
| composition: `puff_spec` with the mirror replaced by the Lean function (`funspec_sub`) | `rocq/Puff.v` | Rocq/VST |

The functions and their contracts (`Spec_puff.v`):

| function | contract |
|---|---|
| `bits(s, n)` | the next `n` bits, least significant first; at end of input sets `eof` |
| `stored(s)` | the spec's `stored` at the current bit |
| `construct(h, lens, n)` | negative exactly when `Deflate.notOversub` refuses; 0 exactly when the code is complete or empty; the tables `decode` needs |
| `decode(s, h)` | `Deflate.decodeSym (code lens) (bitsOf bytes)` at the current bit |
| `codes(s, lc, dc)` | `inflateSyms` with the two codes |
| `fixed(s)` | `inflateSyms` with the fixed codes |
| `dynamic(s)` | `dynHeader`, failing where its zlib flag is off, then `inflateSyms` |
| `puff(...)` | `inflateBytes`, as above |

The math about the spec, such as why puff's `first`/`count` arithmetic finds the
canonical code, is proved in Lean, where the spec lives. One fact is proved in
Rocq instead: puff builds the fixed distance code from 30 lengths where the
spec has 32, and the two decode alike below 30 (`Codes_Dist30.v`).

## What it trusts

* **Lean's kernel**, for the Lean theorems. `export.sh` turns every exported
  theorem into an axiom with the same statement, so Rocq does not re-check their
  proofs. Re-checking would pull in Lean's string and `UInt32` library (through
  `omega`'s lemmas), which rocq-lean-import handles badly (see below).
  `Print Assumptions puff_bodies` lists 97 such statements:
  * `decode_eq` and `blCount_eq_cnt` from `Puff.lean`;
  * 22 from `PuffExport.lean` and 32 from `InflateExport.lean`;
  * 41 Lean core lemmas and proof terms that the imported definitions use
    inside their termination proofs and decidability instances.
* **`lean4export`** (leanprover, pinned in `export.sh`) and **`prep.py`**. `prep.py`
  turns theorems into axioms, keeps the declarations the spec reaches, and
  renumbers ids.
* **rocq-lean-import's translation** and its hand-written declarations in
  `Lean.v`: `Eq`, `Nat` (with literals built by doubling), `Nat.le`, `Or`, `And`
  and `Quot`. The importer declares everything else from Lean's terms, and
  Rocq's kernel checks it.
* **Rocq's kernel with definitional UIP**, which the importer turns on to model
  Lean's proof irrelevance.
* **VST and CompCert's Clight semantics** (32-bit x86), with VST's usual
  axioms: `prop_ext`, `functional_extensionality_dep`, `classic`,
  `Extensionality_Ensembles` and two from `ClassicalDedekindReals`. Also
  `clightgen`, which turns `puff.c` into `puff.v`.

Nothing about DEFLATE is in the trusted part. Compare the Verus bridge
(`lspec/README.md`), where the Lean semantics of Verus's VIR is ours and
trusted.

What the result does not cover: termination (VST proves partial correctness,
though every loop in puff is bounded), and stack use (puff needs under 2K, and
the proof assumes it is there).

## Build

```sh
./export.sh --check         # LeanSpec.ndjson is a fresh export (needs lspec's Lean 4.34)
docker build -t vst-rli:9.3 docker
rocq/build.sh               # make in the image: clightgen, then all .v files, ~1 hour
c/test/run.sh               # puff.c against zlib's puff.orig.c (gcc, python3)
```

The image is Rocq 9.3 with rocq-lean-import, CompCert 3.18 (32-bit) and
VST 2.17 (`docker/Dockerfile`).
* The image runs as uid 1000 and writes the build into `rocq/`. If that
  user can't write there (another uid, or rootless Docker, which maps it
  to a different host uid), make the directory writable first:
  `chmod -R a+w rocq`.
* VST and CompCert declare Rocq ≤ 9.2, and the importer needs ≥ 9.3, so their
  version checks are off; both build with warnings only.
* The importer is at 546979b, the first commit that reads lean4export's NDJSON,
  plus `docker/rocq-lean-import-9.3.patch`, a shim for an API change that came
  after 9.3.

## Notes

* **The importer and current Lean.** rocq-lean-import pre-declares `UInt32` as
  a wrapper around `Fin`, but Lean now builds it on `BitVec`, so Lean's strings
  and chars fail to import. Lean 4.34's kernel reads a string literal as
  `String.ofList [Char.ofNat c, ...]`, so the fix would be to translate
  literals that way and drop the `UInt32`/`Char` pre-declarations. A second
  obstacle: the imported `Nat` is unary, so checking Lean's `Char` code
  overflows on 2^32. This is why theorems come in as axioms, and why
  `PuffExport.lean` has its own `lgetD`: `List.getD` reaches strings through
  the panic message of `getElem!`.
* **Evaluating imported definitions.** `Eval lazy` works on the imported terms.
  `vm_compute` gets stuck, because the VM lacks UIP's special reduction.
* **Working with imported terms in Rocq.**
  * Lean's `Prop`s are `SProp`s. Only equality turns back into a Rocq
    proposition (`LeanNat.of_leq`, by definitional UIP); `Lean.v` provides the
    same for `<=`.
  * One-step equations of Lean's structural recursions hold by `reflexivity`.
    Lean's well-founded recursions do not unfold in Rocq, so `InflateExport.lean`
    exports their unfolding equations, and the mirror recurses on fuel.
  * Lean's `Bool` has `false` first, so `destruct` yields its cases in the
    opposite order to Rocq's.
  * After importing, `Lean.v`'s notation scopes need closing
    (`Close Scope Nat_scope. Close Scope lean_scope.`).
* **VST.** A `WITH` clause takes at most 22 binders. A function returning
  needs its local arrays back exactly at their addresses, so a callee's
  contract must not hide them behind an existential.
