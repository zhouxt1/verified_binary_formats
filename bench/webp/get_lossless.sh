#!/bin/bash
# Lossless test images for ab_lossless.py, made with cwebp -lossless (its
# default effort, -q 75 -m 4) into images/lossless/: Kodak's 24, and six of
# imagecompression.info's 8-bit photographs (6 to 18 megapixels), and four
# synthetic graphics (gen_graphics.py: panels and text, a chart, icons, a
# gradient; 1024 x 768). Needs
# difftest/webp/build/cwebp and the sources of get_images.sh (IMAGES names
# another directory holding kodak/*.png or *.ppm and rgb8bit.zip).
set -e
cd "$(dirname "$0")"
C=$PWD/../../difftest/webp/build/cwebp
I=${IMAGES:-images}
O=images/lossless
mkdir -p $O/kodak $O/photos $O/tmp
for i in $(seq -w 1 24); do
  f=$I/kodak/kodim$i
  [ -f $f.ppm ] || python3 png2ppm.py $f.png
  [ -f $O/kodak/kodim$i.webp ] || $C -quiet -lossless $f.ppm -o $O/kodak/kodim$i.webp &
done
wait
for p in bridge cathedral deer fireworks flower_foveon nightshot_iso_100; do
  if [ ! -f $O/photos/$p.webp ]; then
    python3 -c "import zipfile,sys; zipfile.ZipFile(sys.argv[1]).extract(sys.argv[2], sys.argv[3])" $I/photos/rgb8bit.zip $p.ppm $O/tmp 2>/dev/null \
      || python3 -c "import zipfile,sys; zipfile.ZipFile(sys.argv[1]).extract(sys.argv[2], sys.argv[3])" $I/rgb8bit.zip $p.ppm $O/tmp
    ($C -quiet -lossless $O/tmp/$p.ppm -o $O/photos/$p.webp; rm $O/tmp/$p.ppm) &
  fi
done
wait
rmdir $O/tmp
mkdir -p $O/graphics
python3 gen_graphics.py $O/graphics-src
for f in $O/graphics-src/*.ppm; do
  $C -quiet -lossless $f -o $O/graphics/$(basename ${f%.ppm}).webp
done
rm -r $O/graphics-src
ls $O/kodak/*.webp $O/photos/*.webp $O/graphics/*.webp | wc -l
