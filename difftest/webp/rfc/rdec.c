/* rdec: the VP8 reference decoder of RFC 6386 (section 20, "Attachment
   One", extracted by extract.py) behind a batch protocol.

   Records on stdin: a little-endian u32 length and that many bytes, one
   VP8 frame (the payload of a WebP "VP8 " chunk). For each, on stdout: a
   status byte (0: error, 1: success, 2: not a key frame, which the
   reference decoder cannot start from), the vpx_codec_err_t (i32), and on
   success the width and height (u32 each) and the Y, U and V planes, each
   row by row with no padding: Y is width x height, U and V are
   ((width+1)/2) x ((height+1)/2).

   Each frame is decoded in a child process: the reference decoder is not
   memory safe on invalid input. A child that dies (a signal, or an exit
   status other than 0) is reported as status 3, with the signal number
   (or 256 + the exit status) as the code. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#include "dixie.h"

static int rd(void* p, size_t n) { return fread(p, 1, n, stdin) == n; }
static FILE* out;
static void wr(const void* p, size_t n) { fwrite(p, 1, n, out); }

static void plane(const unsigned char* p, int stride, unsigned w, unsigned h) {
  for (unsigned y = 0; y < h; y++) wr(p + (size_t)y * stride, w);
}

/* Decode one frame, writing its record to `out`. */
static void decode(const uint8_t* in, uint32_t len) {
    uint8_t status = 0;
    int32_t code = 0;
    if (len >= 1 && (in[0] & 1)) {
      status = 2;
    } else {
      struct vp8_decoder_ctx* ctx = calloc(1, sizeof *ctx);
      vp8_dixie_decode_init(ctx);
      /* Errors end the frame: vpx_internal_error longjmps back to
         vp8_dixie_decode_frame only if `setjmp` is set, which nothing in
         the RFC's listing does (its caller, the vpx_codec glue, is not in
         the RFC; libvpx's own decoders set it the same way before
         decoding). Without it an error is recorded and decoding carries
         on past it, into out-of-bounds reads and writes. */
      ctx->error.setjmp = 1;
      code = vp8_dixie_decode_frame(ctx, in, len);
      status = code == VPX_CODEC_OK;
      if (status) {
        vpx_image_t* img = &ctx->ref_frames[CURRENT_FRAME]->img;
        uint32_t w = img->d_w, h = img->d_h;
        wr(&status, 1); wr(&code, 4); wr(&w, 4); wr(&h, 4);
        plane(img->planes[PLANE_Y], img->stride[PLANE_Y], w, h);
        plane(img->planes[PLANE_U], img->stride[PLANE_U], (w + 1) / 2, (h + 1) / 2);
        plane(img->planes[PLANE_V], img->stride[PLANE_V], (w + 1) / 2, (h + 1) / 2);
      }
      if (ctx->frame_hdr.kf.w) vp8_dixie_decode_destroy(ctx);
      free(ctx);
    }
    if (status != 1) { wr(&status, 1); wr(&code, 4); }
}

int main(void) {
  for (;;) {
    uint32_t len;
    if (!rd(&len, 4)) break;
    uint8_t* in = malloc(len ? len : 1);
    if (!rd(in, len)) break;
    /* The child writes its record into a temporary file; the parent copies
       it to stdout if the child finished. */
    FILE* tmp = tmpfile();
    fflush(stdout);
    pid_t pid = fork();
    if (pid == 0) {
      out = tmp;
      decode(in, len);
      fflush(tmp);
      _exit(0);
    }
    int ws = 0;
    waitpid(pid, &ws, 0);
    if (WIFEXITED(ws) && WEXITSTATUS(ws) == 0) {
      char buf[1 << 16];
      size_t n;
      rewind(tmp);
      while ((n = fread(buf, 1, sizeof buf, tmp)) > 0) fwrite(buf, 1, n, stdout);
    } else {
      uint8_t status = 3;
      int32_t code = WIFSIGNALED(ws) ? WTERMSIG(ws) : 256 + WEXITSTATUS(ws);
      fwrite(&status, 1, 1, stdout); fwrite(&code, 4, 1, stdout);
    }
    fclose(tmp);
    fflush(stdout);
    free(in);
  }
  return 0;
}
