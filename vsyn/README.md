# vsyn: a verified interpreter for bitstream syntax tables

Video standards describe their headers as syntax tables (H.264 and H.265
section 7.3, AV1 section 5): syntax elements with their descriptors,
conditions, loops and arrays sized by earlier values. `vsyn` takes those
tables as data and runs them with one interpreter, proved once, so a table
transcribed from the standard needs no proof of its own.

* `ir`: the tables as data, and the arithmetic of their conditions;
  `eg`, `avd`: the descriptors (Exp-Golomb, fixed-width, leb128, ...) as
  prefix codes.
* `sem`: what a table means, as a spec decoder and a spec encoder.
* `rt`: the theorems, for every table: `theorem_enc_dec` (a well-formed
  trace's encoding decodes back to it) and `theorem_dec_enc` (whatever
  decodes is the encoding of a well-formed trace, bit for bit), the same
  for a structure at the front of its data, `theorem_canon`, and
  `theorem_rigid` (a table without descriptor choices gives each value one
  encoding).
* `bits`, `xir`, `xdec`, `xenc`: the executable reader, writer, decoder and
  encoder, proved equal to the spec.
* `raw`: the tables as a compiler writes them.

`vsync` compiles tables written in the standards' own notation (`.syn`
files, see `vh26x-tool/syn/`) into `raw` tables; `vsyn-tool` holds the
unverified helpers around a trace (naming its values, explaining a
rejection, drawing random well-formed traces for fuzzing). `vh26x` is the
first user.

```bash
cargo verus verify -p vsyn
```
