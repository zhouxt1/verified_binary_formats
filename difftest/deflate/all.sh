#!/bin/sh
# Every vdeflate differential test, at a size that runs in a few minutes.
# Needs target/release/vdeflate-tool and bench/deflate's deflate-bench (for
# odiff.py and encall.py) built; prints one line per suite and exits 1 if any
# failed.
cd "$(dirname "$0")/../.." || exit 1
d=difftest/deflate
fail=0
run() {
    name=$1; shift
    out=$("$@" 2>&1 | tail -1)
    echo "$name: $out"
    case "$out" in *"failures: 0"*|*"mismatches: 0"*) ;; *) fail=1 ;; esac
}
run zdiff            python3 $d/zdiff.py -n 1000 --stream
run edge             python3 $d/edge.py
run wrapdiff         python3 $d/wrapdiff.py -n 1000
run wrapdiff-stream  env VD_STREAM=7 python3 $d/wrapdiff.py -n 500
run gzmulti          python3 $d/gzmulti.py -n 500
run zdict            python3 $d/zdict.py -n 500
run encdiff          python3 $d/encdiff.py -n 500
run encdiff-level1   env VD_LEVEL=1 python3 $d/encdiff.py -n 300
run encdiff-level9   env VD_LEVEL=9 python3 $d/encdiff.py -n 200
run encdiff-gzip     python3 $d/encdiff.py -n 300 --wrap gzip
run encdiff-stream   env VD_STREAM=300 python3 $d/encdiff.py -n 300 --wrap zlib
run encall           python3 $d/encall.py -n 300
exit $fail
