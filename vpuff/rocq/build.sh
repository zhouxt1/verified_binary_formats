#!/bin/sh
# Build the Rocq development in the vst-rli:9.3 image (see ../docker/).
# usage: [MEMCAP=64G] ./build.sh [make targets]   (memory cap, default 128G)
set -eu
here=$(cd "$(dirname "$0")" && pwd)
docker run --rm --memory "${MEMCAP:-128G}" --memory-swap "${MEMCAP:-128G}" --ulimit stack=-1 -v "$here/..":/w -w /w/rocq --entrypoint bash vst-rli:9.3 \
  -lc "ulimit -s unlimited; make $*"
