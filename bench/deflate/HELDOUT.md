# Held-out evaluation of vdeflate's compressors

**Rule.** Ratio and speed claims are reported on these sets, which are never
used for tuning. Every setting of `opt::deflate_opt` (and of the levels) was
chosen on Silesia, which is the *dev* set. Nothing is chosen, kept, or
reverted because of a number on these sets. A change made after looking at
them needs a new held-out set before it is claimed.

This file was committed before any compressor was run on these sets.

## The sets (fixed 2026-10-07)

| set | files | bytes | source |
|---|---|---|---|
| canterbury | 14 | 13,970,266 | Canterbury `cantrbry.tar.gz` and Large Canterbury `large.tar.gz` (corpus.canterbury.ac.nz) |
| enwik8 | 1 | 100,000,000 | mattmahoney.net/dc/enwik8.zip |
| source | 328 | 5,700,277 | every nonempty file of zlib 1.3.1 (zlib.net/fossils) and Lua 5.4.6 (lua.org/ftp), each a file |
| web | 8 | 1,774,372 | cdnjs: jQuery 3.7.1 (`.js`, `.min.js`), Bootstrap 5.3.3 (css, bundle js), D3 7.9.0, React DOM 18.3.1, lodash 4.17.21, three.js r128 |
| png | 24 | 28,325,376 | Kodak's 24 images (r0k.us/graphics/kodak): each PNG's IDAT data inflated, i.e. the filtered rows a PNG encoder deflates |

`heldout_sets.py DIR` builds them from the downloads in `DIR/dl`;
`heldout.sha256` has every file's SHA-256 and size.

## What is compared

* vdeflate `opt::deflate_opt` with `opt_max()` as of commit d920dce
  (`VD_OPT=1 vdeflate-tool --compress`), and level 9;
* zopfli 1.0.3 (github.com/google/zopfli, tag `zopfli-1.0.3`, built with its
  Makefile), `zopfli --deflate`, default 15 iterations;
* libdeflate -12 and zlib -9 (raw DEFLATE).

All sizes are raw DEFLATE bytes. Reported per set: total bytes, and per file
the wins/losses of `deflate_opt` against each baseline and the median ratio,
so that one large file does not decide the result. Every output of
`deflate_opt` is decoded by zlib, and checked against the Lean spec
(`difftest/deflate/lspecenc.py`'s check: `CompressesTo`) on all sets but
enwik8.

## Results

(Appended after the run, unedited.)

Run 2026-10-07 from 3:02 PM EDT, `heldout_run.py` (output below as printed;
per-file sizes in `heldout_results.json`). "opt" is `deflate_opt`; ratios
are opt / baseline; times are one core for opt, all 64 cores for zopfli.

```
   opt vs vd9    total -5.795%   files won 14 / tied 0 / lost 0   median ratio 0.9508
   opt vs zl9    total -5.733%   files won 14 / tied 0 / lost 0   median ratio 0.9510
   opt vs ld12   total +0.071%   files won 11 / tied 0 / lost 3   median ratio 0.9984
   opt vs zopfli total -0.017%   files won 4 / tied 0 / lost 10   median ratio 1.0010
== enwik8: 1 files, 100000000 bytes; opt 104.5 s, zopfli 227.0 s (parallel); zlib-decode failures 0, Lean-spec failures n/a
   opt vs vd9    total -4.068%   files won 1 / tied 0 / lost 0   median ratio 0.9593
   opt vs zl9    total -3.989%   files won 1 / tied 0 / lost 0   median ratio 0.9601
   opt vs ld12   total -0.317%   files won 1 / tied 0 / lost 0   median ratio 0.9968
   opt vs zopfli total +0.074%   files won 0 / tied 0 / lost 1   median ratio 1.0007
== png: 24 files, 28325376 bytes; opt 29.1 s, zopfli 7.0 s (parallel); zlib-decode failures 0, Lean-spec failures 0
   opt vs vd9    total -4.366%   files won 24 / tied 0 / lost 0   median ratio 0.9581
   opt vs zl9    total -5.077%   files won 24 / tied 0 / lost 0   median ratio 0.9532
   opt vs ld12   total -0.286%   files won 21 / tied 0 / lost 3   median ratio 0.9978
   opt vs zopfli total +0.158%   files won 3 / tied 0 / lost 21   median ratio 1.0015
== source: 328 files, 5700277 bytes; opt 10.5 s, zopfli 3.1 s (parallel); zlib-decode failures 0, Lean-spec failures 0
   opt vs vd9    total -3.547%   files won 309 / tied 15 / lost 4   median ratio 0.9745
   opt vs zl9    total -3.108%   files won 289 / tied 19 / lost 20   median ratio 0.9789
   opt vs ld12   total -0.314%   files won 104 / tied 43 / lost 181   median ratio 1.0007
   opt vs zopfli total +0.210%   files won 9 / tied 13 / lost 306   median ratio 1.0048
== web: 8 files, 1774372 bytes; opt 1.9 s, zopfli 1.7 s (parallel); zlib-decode failures 0, Lean-spec failures 0
   opt vs vd9    total -4.502%   files won 8 / tied 0 / lost 0   median ratio 0.9594
   opt vs zl9    total -4.220%   files won 8 / tied 0 / lost 0   median ratio 0.9630
   opt vs ld12   total -0.190%   files won 6 / tied 0 / lost 2   median ratio 0.9982
   opt vs zopfli total +0.292%   files won 1 / tied 0 / lost 7   median ratio 1.0022
```

By file size, all sets together (opt against libdeflate -12 and zopfli):

| size | files | vs ld12: won/lost, median, total | vs zopfli: won/lost, median, total |
|---|---|---|---|
| < 4 KB | 130 | 14/87, 1.0019, +0.19% | 4/117, 1.0080, +0.85% |
| 4-16 KB | 105 | 45/47, 1.0000, -0.10% | 2/99, 1.0026, +0.46% |
| 16-64 KB | 90 | 43/46, 1.0002, -0.04% | 2/88, 1.0050, +0.52% |
| 64 KB-1 MB | 22 | 18/4, 0.9981, -0.48% | 5/17, 1.0017, +0.08% |
| > 1 MB | 28 | 23/5, 0.9978, -0.28% | 4/24, 1.0013, +0.09% |

What it says:

* Every output decodes (zlib: all 375; the Lean spec's `CompressesTo`: all
  but enwik8, 374).
* Against libdeflate -12, `deflate_opt` is smaller in total on four sets of
  five (enwik8 -0.32%, png -0.29%, source -0.31%, web -0.19%), larger on
  canterbury (+0.07%, though smaller on 11 of its 14 files). It wins on
  files above 64 KB (41 of 50) and loses on files below 4 KB (87 of 130,
  median +0.19%).
* Against zopfli 1.0.3 it is larger on every set but canterbury (-0.02%),
  by +0.07% (enwik8) to +0.29% (web), and on most files; the gap is 0.1% on
  files above 64 KB and 0.5 to 0.9% below 64 KB.

So the dev-set result (Silesia: -0.09% libdeflate -12, +0.17% zopfli) holds
up for large inputs and is optimistic for small ones. Any change made for
small files after this run needs a new held-out set before it is claimed.
