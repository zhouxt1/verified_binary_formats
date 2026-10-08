#!/bin/sh
# Regenerate the Verus side of the bridge from vdeflate/src/spec.rs:
#  1. verify vdeflate with Verus logging its VIR (Verus from tools/get-verus.sh);
#  2. vdeflate.vir: the spec functions reachable from vdeflate::spec::inflate (in the
#     decoders' contracts), vdeflate::enc2::deflate_ok (the compressors'), and the zlib
#     and gzip wrappers' zlib_decode, zlib_decode_dict, gzip_decode and gzip_file, extracted
#     by `lake exe virsubset` (Lean, the same reader the trusted loader uses);
#  3. VDeflate.lean and VDeflateValid.lean: the shallow definitions and their validation
#     proofs, by vir2lean.py (not trusted: Lean checks the proofs).
# With --check, regenerate into target/vir-log and fail if anything differs from the
# committed files.
set -e
cd "$(dirname "$0")/../../.."
log=$PWD/target/vir-log
bash -c "cargo clean -p vdeflate >/dev/null 2>&1; \
  export PATH=$PWD/tools/verus-x86-linux:\$PATH; \
  cargo verus verify -p vdeflate -- --triggers-mode silent \
    --log vir-simple --log vir-option=no_span --log-dir $log" | tail -1
dir=$PWD/lspec/Lspec/Bridge
roots="vdeflate::spec::inflate vdeflate::enc2::deflate_ok vdeflate::wrap::zlib_decode \
  vdeflate::wrap::zlib_decode_dict vdeflate::wrap::gzip_decode vdeflate::wrap::gzip_file"
out=$dir
[ "$1" = --check ] && out=$log
(cd lspec && lake build virsubset >/dev/null &&
  .lake/build/bin/virsubset $log/crate-simple.vir $out/vdeflate.vir $roots)
python3 $dir/vir2lean.py $log/crate-simple.vir $roots \
  --hints $dir/vdeflate_hints.lean -o $out/VDeflate.lean --validate $out/VDeflateValid.lean
if [ "$1" = --check ]; then
  for f in vdeflate.vir VDeflate.lean VDeflateValid.lean; do cmp $out/$f $dir/$f; done
  echo "vdeflate.vir, VDeflate.lean and VDeflateValid.lean are up to date"
fi
