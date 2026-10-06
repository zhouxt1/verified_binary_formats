#!/bin/bash
# Every WebP differential suite, small: the corpus, cwebp's streams and
# their mutants, the structure-aware generator, and the container (always
# through the verified decoder); then the lossy ones (the executable spec,
# against RFC 6386's reference decoder and libwebp). Run after
# build.sh and `cargo build --release -p vwebp-tool`. Fails if any suite does. TOOL=batch-spec (default) picks the
# lossless decoder under test.
set -eo pipefail
cd "$(dirname "$0")"
T=${TOOL:-batch-spec}
python3 corpus.py --tool $T | tail -1
python3 wdiff.py -n 500 --seed 1 --tool $T | tail -1
python3 gen.py -n 3000 --seed 1 --tool $T | tail -1
python3 cdiff.py -n 500 --seed 1 | tail -1
python3 agen.py -n 200 --seed 1 --tool batch-anim | tail -1
python3 lcorpus.py | tail -1
python3 ldiff.py -n 200 --seed 1 | tail -1
python3 gen8.py -n 1000 --seed 1 | tail -1
python3 lfile.py -n 100 --seed 1 | tail -1
echo "all.sh ($T): OK"
