#!/bin/bash
# Every Brotli suite, small, for the executable spec and the verified decoders (whole and streaming).
set -eo pipefail
cd "$(dirname "$0")/../.."
difftest/brotli/build.sh >/dev/null
cargo build -q --release -p vbrotli-tool
python3 difftest/brotli/dict.py
for tool in batch-spec batch batch-stream; do
  echo "== $tool"
  python3 difftest/brotli/edge.py --tool $tool | tail -1
  python3 difftest/brotli/bdiff.py -n 1500 --seed 11 --tool $tool
done
T=target/bref/brotli/tests/testdata
[ -d difftest/brotli/build/brotli/tests/testdata ] && T=difftest/brotli/build/brotli/tests/testdata
n=0; for f in $T/*.compressed*; do
  target/release/vbrotli-tool spec $f 2>/dev/null | cmp -s - ${f%.compressed*} || { echo "FAIL spec $f"; exit 1; }
  target/release/vbrotli-tool dec $f 2>/dev/null | cmp -s - ${f%.compressed*} || { echo "FAIL dec $f"; exit 1; }
  python3 - "$f" <<EOP || { echo "FAIL stream $f"; exit 1; }
import sys, struct, subprocess
f = sys.argv[1]; data = open(f, "rb").read(); want = open(f.split(".compressed")[0], "rb").read()
p = subprocess.run(["target/release/vbrotli-tool", "batch-stream"], input=struct.pack("<I", len(data)) + data,
                   capture_output=True, env={"VB_STREAM": "13"})
assert p.stdout[0] == 1 and p.stdout[14:] == want
EOP
  n=$((n+1)); done; echo "Google's test vectors: $n decoded"
echo all passed
