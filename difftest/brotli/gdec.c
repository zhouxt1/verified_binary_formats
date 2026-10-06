/* gdec: Google's brotli decoder (the C library, built from source by
   build.sh) behind the batch protocol of `vbrotli-tool batch-*`.

   Records on stdin: a little-endian u32 length and that many bytes. For
   each, on stdout: a status byte (0: error, 1: success, 2: needs more
   input), the decoder's error code (i32), the bytes of input it consumed
   (u64), and the data it produced (u32 length and bytes).

   With -n N, output past N bytes is an error (status 0, code 1). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <brotli/decode.h>

static int rd(void* p, size_t n) { return fread(p, 1, n, stdin) == n; }
static void wr(const void* p, size_t n) { fwrite(p, 1, n, stdout); }

int main(int argc, char** argv) {
  size_t limit = (size_t)1 << 30;
  if (argc == 3 && !strcmp(argv[1], "-n")) limit = strtoull(argv[2], 0, 10);
  uint8_t* out = malloc(limit + 1);
  for (;;) {
    uint32_t len;
    if (!rd(&len, 4)) break;
    uint8_t* in = malloc(len ? len : 1);
    if (!rd(in, len)) break;
    BrotliDecoderState* s = BrotliDecoderCreateInstance(0, 0, 0);
    size_t avail_in = len, avail_out = limit + 1;
    const uint8_t* next_in = in;
    uint8_t* next_out = out;
    BrotliDecoderResult r =
        BrotliDecoderDecompressStream(s, &avail_in, &next_in, &avail_out, &next_out, 0);
    uint8_t status = r == BROTLI_DECODER_RESULT_SUCCESS ? 1
                   : r == BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT ? 2 : 0;
    int32_t code = (int32_t)BrotliDecoderGetErrorCode(s);
    uint64_t used = len - avail_in;
    uint32_t n = (uint32_t)(limit + 1 - avail_out);
    if (r == BROTLI_DECODER_RESULT_NEEDS_MORE_OUTPUT) { status = 0; code = 1; n = 0; }
    wr(&status, 1); wr(&code, 4); wr(&used, 8); wr(&n, 4); wr(out, n);
    fflush(stdout);
    BrotliDecoderDestroyInstance(s);
    free(in);
  }
  return 0;
}
