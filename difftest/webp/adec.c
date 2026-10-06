/* adec: libwebp's animation decoder (WebPAnimDecoder, v1.6.0) behind a
   batch protocol: records of a u32 length and a file; for each, a status
   byte (0: error, 1: success), and on success the canvas width and height,
   the loop count, the background color and the number of frames (u32
   each), then per frame its timestamp (u32) and the canvas as
   little-endian ARGB u32s (MODE_BGRA, not premultiplied). With -n N, a
   file whose canvas times frames is more than N pixels is an error. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "webp/demux.h"

static int rd(void* p, size_t n) { return fread(p, 1, n, stdin) == n; }
static void wr(const void* p, size_t n) { fwrite(p, 1, n, stdout); }

int main(int argc, char** argv) {
  uint64_t limit = (uint64_t)1 << 26;
  if (argc == 3 && !strcmp(argv[1], "-n")) limit = strtoull(argv[2], 0, 10);
  for (;;) {
    uint32_t len;
    if (!rd(&len, 4)) break;
    uint8_t* in = malloc(len ? len : 1);
    if (!rd(in, len)) break;
    WebPData data = {in, len};
    WebPAnimDecoderOptions opt;
    WebPAnimDecoderOptionsInit(&opt);
    opt.color_mode = MODE_BGRA;
    WebPAnimDecoder* d = WebPAnimDecoderNew(&data, &opt);
    WebPAnimInfo info;
    uint8_t st = 0;
    uint8_t* out = NULL;
    size_t out_len = 0;
    if (d && WebPAnimDecoderGetInfo(d, &info) &&
        (uint64_t)info.canvas_width * info.canvas_height * info.frame_count <= limit) {
      size_t canvas = (size_t)info.canvas_width * info.canvas_height * 4;
      out = malloc(info.frame_count * (canvas + 4) + 1);
      st = 1;
      for (uint32_t k = 0; k < info.frame_count; k++) {
        uint8_t* buf;
        int ts;
        if (!WebPAnimDecoderGetNext(d, &buf, &ts)) { st = 0; break; }
        uint32_t t = ts;
        memcpy(out + out_len, &t, 4);
        memcpy(out + out_len + 4, buf, canvas);
        out_len += canvas + 4;
      }
    }
    wr(&st, 1);
    if (st) {
      uint32_t hdr[5] = {info.canvas_width, info.canvas_height, info.loop_count, info.bgcolor, info.frame_count};
      wr(hdr, sizeof hdr);
      wr(out, out_len);
    }
    fflush(stdout);
    free(out);
    WebPAnimDecoderDelete(d);
    free(in);
  }
  return 0;
}
