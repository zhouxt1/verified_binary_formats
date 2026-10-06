#!/bin/bash
# Build rdec, the VP8 reference decoder of RFC 6386, from the RFC's text
# (docs/spec/rfc6386.txt; docs/spec/get.sh fetches it). Output:
# difftest/webp/build/rfc/rdec.
#
# The RFC's listing does not build as printed. What this adds, all outside
# the decoder proper:
#  * vpx_codec.h and vpx_encoder.h, which vpx_decoder.h and
#    vpx_codec_internal.h include but the RFC does not print: taken from
#    libvpx v0.9.7 (2011), the release of the RFC's time;
#  * an empty vpx_config.h, and vpx/ holding copies of the RFC's own
#    vpx_image.h and vpx_integer.h (vpx_image.c includes them from there);
#  * two typos in the listing, fixed with sed: the enum in vpx_image.h
#    spells VPX_IMGFMT_RGB555 where vpx_image.c uses VPX_IMG_FMT_RGB555, and
#    tokens.c (20.16, vp8_dixie_tokens_process_row) declares
#    `short coeffs` where the pointer `short *coeffs` is meant.
set -e
cd "$(dirname "$0")"
python3 extract.py
B=../build/rfc
V=https://raw.githubusercontent.com/webmproject/libvpx/v0.9.7/vpx
[ -s $B/vpx_codec.h ] || curl -sfL -o $B/vpx_codec.h $V/vpx_codec.h
[ -s $B/vpx_encoder.h ] || curl -sfL -o $B/vpx_encoder.h $V/vpx_encoder.h
echo '/* empty */' > $B/vpx_config.h
mkdir -p $B/vpx && cp $B/vpx_image.h $B/vpx_integer.h $B/vpx/
sed -i 's/VPX_IMGFMT_RGB555,/VPX_IMG_FMT_RGB555,/' $B/vpx_image.h $B/vpx/vpx_image.h
sed -i 's/^\(\s*\)short\(\s*\)coeffs = tokens->coeffs/\1short\2*coeffs = tokens->coeffs/' $B/tokens.c
cp rdec.c $B/
cd $B
gcc -O2 -w -I. -include vpx_encoder.h -o rdec rdec.c dixie.c dixie_loopfilter.c idct_add.c \
  modemv.c predict.c tokens.c vpx_image.c
echo built $(pwd)/rdec
