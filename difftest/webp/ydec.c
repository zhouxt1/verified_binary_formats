/* ydec: libwebp's decoder (v1.6.0, built by build.sh) returning the
   decoded Y'CbCr planes (MODE_YUVA: no upsampling, no RGB conversion),
   behind a batch protocol.

   Records on stdin: a little-endian u32 length and that many bytes (a WebP
   file). For each, on stdout: a status byte (0: error, 1: success), the
   VP8StatusCode (i32), and on success the width and height (u32 each), an
   alpha byte (1 if the image has alpha), and the Y, U and V planes (Y is
   width x height, U and V ((width+1)/2) x ((height+1)/2)), then the A
   plane (width x height) if it has alpha, each row by row.

   With -n N, an image of more than N pixels is an error (status 0, code
   -1), checked from the header before decoding. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "webp/decode.h"

static int rd(void* p, size_t n) { return fread(p, 1, n, stdin) == n; }
static void wr(const void* p, size_t n) { fwrite(p, 1, n, stdout); }
static void plane(const uint8_t* p, int stride, uint32_t w, uint32_t h) {
  for (uint32_t y = 0; y < h; y++) wr(p + (size_t)y * stride, w);
}

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
      c.output.colorspace = MODE_YUVA;
      code = WebPDecode(in, len, &c);
      status = code == VP8_STATUS_OK;
    }
    wr(&status, 1); wr(&code, 4);
    if (status) {
      const WebPYUVABuffer* b = &c.output.u.YUVA;
      uint32_t w = c.output.width, h = c.output.height;
      uint8_t alpha = c.input.has_alpha != 0;
      wr(&w, 4); wr(&h, 4); wr(&alpha, 1);
      plane(b->y, b->y_stride, w, h);
      plane(b->u, b->u_stride, (w + 1) / 2, (h + 1) / 2);
      plane(b->v, b->v_stride, (w + 1) / 2, (h + 1) / 2);
      if (alpha) plane(b->a, b->a_stride, w, h);
    }
    fflush(stdout);
    WebPFreeDecBuffer(&c.output);
    free(in);
  }
  return 0;
}
