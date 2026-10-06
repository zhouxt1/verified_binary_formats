#!/bin/bash
# Build the oracle `gdec` from Google's brotli at a pinned release (v1.2.0,
# the version of the `brotli` Python module the tests compress with).
# Output: difftest/brotli/build/gdec.
set -e
cd "$(dirname "$0")"
mkdir -p build
if [ ! -d build/brotli ]; then
  git clone -q --depth 1 --branch v1.2.0 https://github.com/google/brotli.git build/brotli
fi
B=build/brotli/c
gcc -O2 -o build/gdec gdec.c -I$B/include $B/common/*.c $B/dec/*.c -lm
echo built build/gdec
