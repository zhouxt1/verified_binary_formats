#!/bin/bash
# Build the oracle `wdec` (and dwebp, cwebp, webpinfo) from libwebp at a
# pinned release (v1.6.0), and fetch libwebp-test-data. Run inside the
# container. Output: difftest/webp/build/{wdec,ydec,adec,dwebp,cwebp,webpinfo},
# and build/rfc/rdec.
set -e
cd "$(dirname "$0")"
mkdir -p build
if [ ! -d build/libwebp ]; then
  git clone -q --depth 1 --branch v1.6.0 https://chromium.googlesource.com/webm/libwebp build/libwebp
fi
if [ ! -d build/test-data ]; then
  git clone -q https://chromium.googlesource.com/webm/libwebp-test-data build/test-data
  git -C build/test-data checkout -q 06ddd96e276c2c638a72d39d3c0f340afd61978c  # 2025-08-26
fi
L=build/libwebp
make -s -C $L -f makefile.unix -j16 examples/dwebp examples/cwebp examples/webpinfo src/demux/libwebpdemux.a \
  EXTRA_FLAGS="-DWEBP_USE_THREAD" DWEBP_LIBS= CWEBP_LIBS=  # no PNG/JPEG/TIFF: PAM/PNM in and out >/dev/null
cp $L/examples/dwebp $L/examples/cwebp $L/examples/webpinfo build/
gcc -O2 -o build/wdec wdec.c -I$L/src $L/src/libwebpdecoder.a -lm -lpthread 2>/dev/null ||
  gcc -O2 -o build/wdec wdec.c -I$L/src $L/src/libwebp.a $L/sharpyuv/libsharpyuv.a -lm -lpthread
gcc -O2 -o build/ydec ydec.c -I$L/src $L/src/libwebp.a $L/sharpyuv/libsharpyuv.a -lm -lpthread
rfc/build.sh >/dev/null  # rdec: RFC 6386's reference decoder, from the RFC's text
gcc -O2 -o build/adec adec.c -I$L/src $L/src/demux/libwebpdemux.a $L/src/libwebp.a $L/sharpyuv/libsharpyuv.a -lm -lpthread
echo built build/wdec build/ydec build/adec build/rfc/rdec
