#!/usr/bin/env bash
# Fetch the standards the codecs are written against. ITU-T Recommendations
# are free to download but not ours to redistribute, so nothing here is
# committed.
set -euo pipefail
cd "$(dirname "$0")"
# RFC 1950 (zlib), 1951 (DEFLATE), 1952 (gzip), for vdeflate.
for n in 1950 1951 1952; do curl -sfL -o rfc$n.txt https://www.rfc-editor.org/rfc/rfc$n.txt; done
# RFC 7932 (Brotli), for vbrotli.
curl -sfL -o rfc7932.txt https://www.rfc-editor.org/rfc/rfc7932.txt
# RFC 9649 (WebP Image Format, 11/2024), for the WebP lossless decoder.
curl -sfL -o rfc9649.txt https://www.rfc-editor.org/rfc/rfc9649.txt
# RFC 6386 (11/2011), VP8, for the WebP lossy decoder; its section 20 is the
# reference decoder difftest/webp/rfc/build.sh builds.
curl -sfL -o rfc6386.txt https://www.rfc-editor.org/rfc/rfc6386.txt
# H.264 (V16, 06/2026) and H.265 (V11, 01/2026), for vh26x.
curl -sfL -o "T-REC-H.264-202606.pdf" \
  "https://www.itu.int/rec/dologin_pub.asp?lang=e&id=T-REC-H.264-202606-I%21%21PDF-E&type=items"
curl -sfL -o "T-REC-H.265-202601.pdf" \
  "https://www.itu.int/rec/dologin_pub.asp?lang=e&id=T-REC-H.265-202601-I%21%21PDF-E&type=items"
echo "fetched into $(pwd): rfc1950-1952, rfc7932, rfc9649, rfc6386, T-REC-H.264-202606.pdf, T-REC-H.265-202601.pdf"
