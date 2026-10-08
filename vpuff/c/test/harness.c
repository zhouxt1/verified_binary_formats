/* Run puff() on each length-prefixed stream from stdin with several output
   buffer sizes (including NIL) and print the results, for comparing builds. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../puff.h"

static unsigned long fnv(const unsigned char *p, unsigned long n) {
    unsigned long h = 2166136261u;
    while (n--) h = (h ^ *p++) * 16777619u;
    return h;
}

int main(void) {
    unsigned char hdr[4];
    static unsigned char in[1 << 20], out[1 << 22];
    while (fread(hdr, 1, 4, stdin) == 4) {
        unsigned long n = hdr[0] | hdr[1] << 8 | hdr[2] << 16 | (unsigned long)hdr[3] << 24;
        if (fread(in, 1, n, stdin) != n) return 1;
        /* full space, then NIL, then exact and short buffers from the NIL size */
        unsigned long dl = sizeof out, sl = n;
        int r = puff(out, &dl, in, &sl);
        printf("%d %lu %lu %lx", r, dl, sl, r == 0 ? fnv(out, dl) : 0);
        unsigned long dn = 0, sn = n;
        int rn = puff(NIL, &dn, in, &sn);
        printf(" | %d %lu %lu", rn, dn, sn);
        if (rn == 0) {
            unsigned long sizes[2] = { dn, dn ? dn - 1 : 0 };
            for (int i = 0; i < 2; i++) {
                unsigned long d2 = sizes[i], s2 = n;
                int r2 = puff(out, &d2, in, &s2);
                printf(" | %d %lu %lu", r2, d2, s2);
            }
        }
        printf("\n");
    }
    return 0;
}
