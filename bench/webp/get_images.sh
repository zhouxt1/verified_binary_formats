#!/bin/bash
# The images of README.md's speed table, encoded with cwebp -q 75 into
# images/: Kodak's 24 (r0k.us) and the 13 photographs of
# imagecompression.info's 8-bit set (its artificial image left out).
# Needs difftest/webp/build/cwebp (difftest/webp/build.sh).
set -e
cd "$(dirname "$0")"
C=../../difftest/webp/build/cwebp
mkdir -p images/kodak images/photos
for i in $(seq -w 1 24); do
  [ -f images/kodak/kodim$i.png ] || curl -s -o images/kodak/kodim$i.png https://r0k.us/graphics/kodak/kodak/kodim$i.png
done
python3 png2ppm.py images/kodak/kodim*.png
for f in images/kodak/*.ppm; do $C -quiet -q 75 "$f" -o "${f%.ppm}.webp"; rm "$f"; done
[ -f images/rgb8bit.zip ] || curl -s -o images/rgb8bit.zip https://imagecompression.info/test_images/rgb8bit.zip
(cd images/photos && python3 -c "import zipfile; zipfile.ZipFile('../rgb8bit.zip').extractall('.')" && rm -f artificial.ppm readme.txt)
for f in images/photos/*.ppm; do $C -quiet -q 75 "$f" -o "${f%.ppm}.webp"; rm "$f"; done
ls images/kodak/*.webp images/photos/*.webp | wc -l
