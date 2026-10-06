# Lossy WebP decoding speed

These scripts reproduce the speed table of vwebp/README.md: vwebp's verified
VP8 decoder against libwebp (and, where their harnesses are built, FFmpeg,
image-webp, Go's x/image and Wuffs),
single-threaded, decoding lossy WebP to Y'CbCr planes.

| | |
| --- | --- |
| `get_images.sh` | Downloads Kodak's 24 images and imagecompression.info's 8-bit photographs, and encodes them with cwebp -q 75 into `images/` |
| `vbatch/` | vwebp's verified decoder (`vp8::dec::vp8_x`) behind the batch protocol of difftest/webp's harnesses |
| `bench.py` | Every decoder on every image: first its planes against libwebp's, then the time per frame, as the difference between decoding the frame 2K times and K times, over K (so process start-up and reading cancel), in child CPU time (user + system), best of 5. `ONLY=a,b` keeps the decoders whose names contain one of them; `VW_BIN` names another vwebp harness |
| `ab.py A=path B=path` | Two decoders compared image by image in paired runs, alternating which goes first: the geometric mean of the per-image median ratios. On a shared machine this is the measure to trust for a change of a few percent (the same binary against itself reads 1.00); wall-clock runs one after the other were off by up to 20% |
| `get_lossless.sh`, `gen_graphics.py` | Lossless images (cwebp -lossless) into `images/lossless/`: Kodak, six photographs, four synthetic graphics |
| `lbatch/` | vwebp's verified lossless decoder (`riff::webp_x`) behind wdec's batch protocol |
| `ab_lossless.py A=path B=path` | ab.py for lossless files: pixels compared first, then paired timing per set (photos, Kodak, graphics); `KODAK=n`, `REPS=n` |
| `results_head.txt`, `results_all.txt` | The recorded runs behind the table: the current build with the two SIMD references, and an earlier run of every decoder |

## Running

```
../../difftest/webp/build.sh          # libwebp (ydec, ydec-c, cwebp)
./get_images.sh
(cd vbatch && cargo build --release)
python3 bench.py
python3 ab.py old=path/to/vbatch new=vbatch/target/release/vbatch
./get_lossless.sh
(cd lbatch && cargo build --release)
KODAK=24 REPS=6 python3 ab_lossless.py libwebp=../../difftest/webp/build/wdec vwebp=lbatch/target/release/lbatch
```

The recorded runs were on a Xeon Gold 6448H shared with other jobs; the
ratios between decoders measured in one run are what to compare, not the
absolute numbers across runs.
