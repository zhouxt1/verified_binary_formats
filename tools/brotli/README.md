# tools/brotli

Scripts for working on vbrotli. The host they were written on had no
`perf`, so speed work went by instruction counts from callgrind.

| script | what it does |
|---|---|
| `vv CRATE [ARGS]` | verify a crate with Verus (`cargo verus verify -p CRATE`) |
| `gentables.py RFC.txt` | generate `vbrotli/src/tables.rs` from the text of RFC 7932 |
| `icount [FILE.br] [--annotate]` | instructions to decode one stream with `vbrotli-tool dec` (default `/tmp/d3m.br`: 3 MB of dickens at quality 11); with `--annotate`, per source line in `target/ann.txt` |
| `icmp [FILE.br...]` | the same for vbrotli and for Google's decoder (`difftest/brotli/build/gdec`), side by side, with the ratio; default `/tmp/d3m.br` and `/tmp/bb/*.br` |
| `asm PATTERN [MIN] [FILE.br]` | instructions executed at each instruction of the functions whose names match PATTERN (`target/asm.txt`: count, address, instruction; `cgasm.py` joins callgrind's per-instruction counts with `objdump`) |

Counts include the process's start-up (about 200K instructions for both
decoders), and callgrind counts each byte of a `rep movsb`/`rep stosb` as an
instruction, so large `memcpy`/`memset` calls weigh more than they cost.

Two cautions from the 2026-09 speed work:

* The whole-buffer command loop is one large function (`commands_x` with
  everything inlined). Small changes to anything inlined into it move the
  compiler's register allocation, often by more than the change saves
  (several changes that did less work made it 2 to 30% slower). Measure
  every change, on text and on binary data (`icmp` covers both).
* Constant tables are proved with `by (compute)`, but the array is then in
  the solver's context: 256 entries are cheap, 704 or 1024 are slow and
  near the rlimit. Pad small tables to a power of two and index with a mask
  instead (no bounds check, cheap proof).
