#!/bin/sh
# Differential test of puff.c (vpuff's altered copy) against puff.orig.c (zlib
# upstream): same return code, output size, input size and output hash on
# random zlib streams and mutants, with full, NIL, exact and short buffers.
set -eu
cd "$(dirname "$0")"
gcc -O2 -o /tmp/puff-orig harness.c -include ../puff.orig.c
gcc -O2 -o /tmp/puff-mod harness.c -include ../puff.c
for seed in ${SEEDS:-1 2 3}; do
  python3 gen.py "$seed" 2000 > /tmp/puff-s.bin
  /tmp/puff-orig < /tmp/puff-s.bin > /tmp/puff-o.txt
  /tmp/puff-mod < /tmp/puff-s.bin > /tmp/puff-m.txt
  echo "seed $seed: $(wc -l < /tmp/puff-o.txt) streams, $(diff /tmp/puff-o.txt /tmp/puff-m.txt | grep -c '^<' || true) differ"
done
