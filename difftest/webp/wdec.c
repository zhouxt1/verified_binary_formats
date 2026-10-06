/* wdec: libwebp's decoder (v1.6.0, built from source by build.sh) behind
   the batch protocol of `vwebp-tool batch-*`.

   Records on stdin: a little-endian u32 length and that many bytes (a WebP
   file, or a bare VP8L bitstream starting with its 0x2f signature). For
   each, on stdout: a status byte (0: error, 1: success), the VP8StatusCode
   (i32), and on success the width and height (u32 each) and the pixels as
   little-endian ARGB u32s (libwebp's BGRA byte order), row by row.

   With -n N, an image of more than N pixels is an error (status 0, code
   -1), checked from the header before decoding. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "webp/decode.h"

static int rd(void* p, size_t n) { return fread(p, 1, n, stdin) == n; }
static void wr(const void* p, size_t n) { fwrite(p, 1, n, stdout); }

int main(int argc, char** argv) {
  uint64_t limit = (uint64_t)1 << 28;
  if (argc == 3 && !strcmp(argv[1], "-n")) limit = strtoull(argv[2], 0, 10);
  for (;;) {
    uint32_t len;
    if (!rd(&len, 4)) break;
    uint8_t* in = malloc(len ? len : 1);
    if (!rd(in, len)) break;
    WebPDecoderConfig c;
    WebPInitDecoderConfig(&c);
    int32_t code = WebPGetFeatures(in, len, &c.input);
    uint8_t status = 0;
    if (code == VP8_STATUS_OK &&
        (uint64_t)c.input.width * (uint64_t)c.input.height > limit) code = -1;
    if (code == VP8_STATUS_OK) {
      c.output.colorspace = MODE_BGRA;
      code = WebPDecode(in, len, &c);
      status = code == VP8_STATUS_OK;
    }
    wr(&status, 1); wr(&code, 4);
    if (status) {
      uint32_t w = c.output.width, h = c.output.height;
      wr(&w, 4); wr(&h, 4);
      for (uint32_t y = 0; y < h; y++)
        wr(c.output.u.RGBA.rgba + (size_t)y * c.output.u.RGBA.stride, (size_t)w * 4);
    }
    fflush(stdout);
    WebPFreeDecBuffer(&c.output);
    free(in);
  }
  return 0;
}
