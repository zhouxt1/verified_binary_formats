#!/bin/sh
# Export the Lean spec and the puff model for Rocq: rocq/LeanSpec.ndjson.
#
#   ./export.sh           regenerate rocq/LeanSpec.ndjson
#   ./export.sh --check   regenerate into a temporary file and compare
#
# Needs Lean 4.34 on PATH (lspec's toolchain). lean4export is fetched and
# built in .build/ at a fixed commit.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
lspec=$here/../lspec
L4E_REV=076e8e57707e813375e8f9da8bf989799ace9680   # "bump toolchain to v4.34.0"

l4e=$here/.build/lean4export
if [ ! -x "$l4e/.lake/build/bin/lean4export" ]; then
  mkdir -p "$here/.build"
  [ -d "$l4e" ] || git clone -q https://github.com/leanprover/lean4export "$l4e"
  (cd "$l4e" && git checkout -q "$L4E_REV" && lake build >/dev/null)
fi

# What the Rocq side uses: the spec, the model, and the facts about them.
ROOTS="
Deflate.decodeSym Deflate.code Deflate.bitsOf Deflate.notOversub Deflate.blCount
Deflate.kraft Deflate.maxBits
Deflate.inflate Deflate.inflateBytes Deflate.inflateBlocks Deflate.block Deflate.stored
Deflate.dynHeader Deflate.readCL Deflate.readLens Deflate.inflateSyms Deflate.lzCopy Deflate.getbits
Deflate.lsbVal Deflate.zlibOk Deflate.clOrder Deflate.lenTable Deflate.distTable Deflate.fixedLit
Deflate.fixedDist
Deflate.Puff.cnt Deflate.Puff.offs Deflate.Puff.kr Deflate.Puff.go Deflate.Puff.decode
Deflate.Puff.byteBit
Deflate.Puff.decode_eq Deflate.Puff.blCount_eq_cnt Deflate.Puff.kraft_eq_kr
UInt8.ofNat UInt8.toNat Array.getD Nat.testBit Deflate.Puff.Export.lgetD
"
EXPORT_THMS="ble_true le_of_ble blt_true blt_false div_add_mod mod_lt testBit_eq
uint8_toNat_ofNat uint8_toNat_zero getD_mk lgetD_nil lgetD_zero lgetD_succ
size_mk notOversub_eq cnt_zero cnt_succ offs_zero offs_one offs_succ kr_zero kr_succ
go_zero go_succ decode_def byteBit_def"
for t in $EXPORT_THMS; do ROOTS="$ROOTS Deflate.Puff.Export.$t"; done
# what the whole inflate needs (InflateExport.lean)
INFLATE_THMS="lenBase lenExtra distBase distExtra lenTable_get distTable_get puff_lit_ok puff_cl_ok
getbits_eq lsbVal_zero lsbVal_succ bitsOf_size bitsOf_getD push_mk append_mk replicate_mk setD_mk
extract_mk back_mk mk_toList lzCopy_zero lzCopy_succ inflateSyms_eq bytesAt bytesAt_zero
bytesAt_succ stored_eq readCL_def readCL_go_eq readLens_eq dynHeader_eq block_eq inflateBlocks_eq
zlibOk_eq fixedLit_size fixedLit_getD fixedDist_eq decodeSym_dist30 decodeSym_bounds inflate_def
inflateBytes_def"
for t in $INFLATE_THMS; do ROOTS="$ROOTS Deflate.InflateExport.$t"; done

out=$here/rocq/LeanSpec.ndjson
[ "${1:-}" = "--check" ] && out=$(mktemp)
raw=$(mktemp)
(cd "$lspec" && lake build Lspec.Deflate.InflateExport >/dev/null &&
  lake env "$l4e/.lake/build/bin/lean4export" Lspec.Deflate.InflateExport -- $ROOTS > "$raw")
python3 "$here/prep.py" "$raw" "$out" $ROOTS
rm -f "$raw"
if [ "${1:-}" = "--check" ]; then
  if cmp -s "$out" "$here/rocq/LeanSpec.ndjson"; then echo "LeanSpec.ndjson is up to date"; rm -f "$out"
  else echo "LeanSpec.ndjson differs from a fresh export ($out)"; exit 1; fi
fi
