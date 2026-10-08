#!/usr/bin/env python3
"""Hand-built DEFLATE streams at the points where decoders disagree
(incomplete codes, HDIST/HLIT limits, reserved symbols, distances), each
with the verdict RFC 1951 gives it (what vdeflate's spec says) and zlib's.

    difftest/deflate/edge.py [--write DIR]    run vdeflate and zlib on each

Each vector's `rfc` is `ok` or `bad` and `zl` is zlib 1.3's verdict; vdeflate
must return `rfc`, with its zlib flag equal to `zl` when it decodes.
"""
import argparse, os, subprocess, sys, tempfile, zlib

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TOOL = os.path.join(ROOT, "target/release/vdeflate-tool")

class W:
    def __init__(self):
        self.bits = []
    def put(self, v, n):             # LSB first (data elements)
        for i in range(n):
            self.bits.append((v >> i) & 1)
    def code(self, c, n):            # MSB first (Huffman codes)
        for i in reversed(range(n)):
            self.bits.append((c >> i) & 1)
    def align(self):
        while len(self.bits) % 8:
            self.bits.append(0)
    def bytes(self):
        b = self.bits + [0] * (-len(self.bits) % 8)
        return bytes(sum(b[i + j] << j for j in range(8)) for i in range(0, len(b), 8))

def canon(lens):
    """RFC 1951 3.2.2: symbol -> (code, length)."""
    bl = [0] * 16
    for l in lens:
        if l:
            bl[l] += 1
    code, nxt = 0, [0] * 16
    for b in range(1, 16):
        code = (code + bl[b - 1]) << 1 if b > 1 else 0
        nxt[b] = code
    out = {}
    for n, l in enumerate(lens):
        if l:
            out[n] = (nxt[l], l)
            nxt[l] += 1
    return out

ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

def dyn(w, lit, dist, cl=None, cl_syms=None, hlit=None, hdist=None, final=1):
    """A dynamic block header for `lit`, `dist`; the code lengths are sent
    literally with code length code `cl` (default: all 19 of length 5, an
    incomplete-but-valid... no: 19 codes of 5 bits is incomplete)."""
    w.put(final, 1); w.put(2, 2)
    nl = len(lit) if hlit is None else hlit
    nd = len(dist) if hdist is None else hdist
    w.put(nl - 257, 5); w.put(nd - 1, 5)
    if cl is None:
        cl = [0] * 19
        for s in range(16):
            cl[s] = 4                      # 16 codes of length 4: complete
    w.put(19 - 4, 4)
    for i in range(19):
        w.put(cl[ORDER[i]], 3)
    cc = canon(cl)
    seq = cl_syms if cl_syms is not None else [(l, None) for l in lit + dist]
    for s, extra in seq:
        c, n = cc[s]
        w.code(c, n)
        if extra is not None:
            w.put(*extra)
    return canon(lit), canon(dist)

def sym(w, cc, s):
    c, n = cc[s]
    w.code(c, n)

def lit_lens(extra=None):
    """A complete lit/length code: 256 literals of 9 bits... use 8 bits for
    0..255 minus room for 256..: lengths making a complete code."""
    lens = [0] * 286
    # 0..255: 8 bits except 2 of them 9 bits; 256..285: 9 bits -> complete?
    # Simpler: symbols 0..255 len 9 (256 * 2^-9 = 1/2), 256..285 len 9
    # (30 * 2^-9), rest to fill: make 256..285 len 9 and 226 more... keep it
    # generic: assign 9 bits to 0..285 (286/512) and top up with 8-bit ones.
    for i in range(286):
        lens[i] = 9
    # convert k symbols from 9 to 8 bits: each adds 2^-9. Need 512-286 = 226.
    for i in range(226):
        lens[i] = 8
    return lens

def lit_lens_small():
    """Only literals 'a' (97), 'b' (98), end of block, and length 257..258."""
    lens = [0] * 286
    lens[97] = 2; lens[98] = 2; lens[256] = 2; lens[257] = 3; lens[258] = 3
    return lens

VECS = []
def vec(name, rfc, zl):
    def deco(f):
        VECS.append((name, rfc, zl, f))
        return f
    return deco

@vec("complete lit, complete dist", "ok", "ok")
def _(w):
    L = lit_lens_small(); D = [1, 1]
    lc, dc = dyn(w, L, D)
    for s in (97, 98, 97):
        sym(w, lc, s)
    sym(w, lc, 257); sym(w, dc, 1)          # length 3, distance 2
    sym(w, lc, 256)

@vec("single 1-bit distance code (zlib's exception)", "ok", "ok")
def _(w):
    L = lit_lens_small(); D = [1]
    lc, dc = dyn(w, L, D)
    sym(w, lc, 97); sym(w, lc, 257); sym(w, dc, 0); sym(w, lc, 256)

@vec("single 1-bit distance code, the unused bit 1", "bad", "bad")
def _(w):
    L = lit_lens_small(); D = [1]
    lc, dc = dyn(w, L, D)
    sym(w, lc, 97); sym(w, lc, 257); w.code(1, 1); sym(w, lc, 256)

@vec("single 2-bit distance code (incomplete, not zlib's exception)", "ok", "bad")
def _(w):
    L = lit_lens_small(); D = [2]
    lc, dc = dyn(w, L, D)
    sym(w, lc, 97); sym(w, lc, 257); sym(w, dc, 0); sym(w, lc, 256)

@vec("two 2-bit distance codes (incomplete)", "ok", "bad")
def _(w):
    L = lit_lens_small(); D = [2, 2]
    lc, dc = dyn(w, L, D)
    sym(w, lc, 97); sym(w, lc, 98); sym(w, lc, 257); sym(w, dc, 1); sym(w, lc, 256)

@vec("incomplete lit/length code", "ok", "bad")
def _(w):
    L = lit_lens_small(); L[258] = 0      # 2+2+2+3 = 1/4*3 + 1/8 = 7/8
    lc, dc = dyn(w, L, [1, 1])
    sym(w, lc, 97); sym(w, lc, 256)

@vec("incomplete code length code", "ok", "bad")
def _(w):
    cl = [0] * 19
    for s in range(16):
        cl[s] = 5                         # 16/32: incomplete
    L = lit_lens_small(); D = [1, 1]
    lc, dc = dyn(w, L, D, cl=cl)
    sym(w, lc, 97); sym(w, lc, 256)

@vec("over-subscribed lit/length code", "bad", "bad")
def _(w):
    L = lit_lens_small(); L[99] = 2        # five 2/3-bit codes over 1
    lc, dc = dyn(w, L, [1, 1])
    sym(w, lc, 256)

@vec("no end-of-block code", "bad", "bad")
def _(w):
    L = lit_lens_small(); L[256] = 0; L[99] = 2
    lc, dc = dyn(w, L, [1, 1])
    sym(w, lc, 97)

@vec("no distance codes, literals only", "ok", "ok")
def _(w):
    L = lit_lens_small()
    lc, dc = dyn(w, L, [0])
    sym(w, lc, 97); sym(w, lc, 98); sym(w, lc, 256)

@vec("no distance codes, a length used", "bad", "bad")
def _(w):
    L = lit_lens_small()
    lc, dc = dyn(w, L, [0])
    sym(w, lc, 97); sym(w, lc, 257); w.code(0, 1); sym(w, lc, 256)

@vec("HDIST = 31 (32 distance codes)", "ok", "bad")
def _(w):
    L = lit_lens_small(); D = [5] * 32
    lc, dc = dyn(w, L, D)
    sym(w, lc, 97); sym(w, lc, 257); sym(w, dc, 0); sym(w, lc, 256)

@vec("HDIST = 29 (30 distance codes, zlib's maximum)", "ok", "ok")
def _(w):
    L = lit_lens_small(); D = [5] * 30 + []
    D[0] = 4; D[1] = 4                    # 28/32 + 2/16 = 1
    lc, dc = dyn(w, L, D)
    sym(w, lc, 97); sym(w, lc, 257); sym(w, dc, 0); sym(w, lc, 256)

@vec("HLIT = 30 (287 lit/length codes)", "bad", "bad")
def _(w):
    L = lit_lens_small() + [0]
    lc, dc = dyn(w, L, [1, 1])
    sym(w, lc, 256)

@vec("distance code 30 in a 32-code dynamic distance code", "bad", "bad")
def _(w):
    L = lit_lens_small(); D = [5] * 32
    lc, dc = dyn(w, L, D)
    for s in (97,) * 1:
        sym(w, lc, s)
    sym(w, lc, 257); sym(w, dc, 30); sym(w, lc, 256)

@vec("fixed block, symbol 286", "bad", "bad")
def _(w):
    w.put(1, 1); w.put(1, 2)
    w.code(0b11000110, 8)                 # 286: 280..287 are 11000000 + (s-280)
    w.code(0, 7)

@vec("fixed block, distance code 30", "bad", "bad")
def _(w):
    w.put(1, 1); w.put(1, 2)
    w.code(0x30 + 97, 8)                  # 'a'
    w.code(1, 7)                          # 257: length 3
    w.code(30, 5)
    w.code(0, 7)

@vec("fixed block, distance past the start", "bad", "bad")
def _(w):
    w.put(1, 1); w.put(1, 2)
    w.code(0x30 + 97, 8)
    w.code(1, 7); w.code(1, 5)            # length 3, distance 2 > 1 byte
    w.code(0, 7)

@vec("fixed block, overlapping copy", "ok", "ok")
def _(w):
    w.put(1, 1); w.put(1, 2)
    w.code(0x30 + 97, 8)
    w.code(1, 7); w.code(0, 5)            # length 3, distance 1
    w.code(0, 7)

@vec("repeat code 16 first", "bad", "bad")
def _(w):
    L = lit_lens_small(); D = [1, 1]
    cl = [4] * 15 + [5, 5] + [0, 0]       # 0..14: 4 bits, 15 and 16: 5 bits
    lc, dc = dyn(w, L, D, cl=cl, cl_syms=[(16, (0, 2))] + [(l, None) for l in L + D])
    sym(w, lc, 256)

@vec("a zero run across the lit/dist boundary", "ok", "ok")
def _(w):
    L = [0] * 258; L[97] = 1; L[256] = 1  # HLIT 1: 258 codes, the last unused
    D = [0, 0, 1]
    cl = [0] * 19
    cl[1] = 1; cl[17] = 2; cl[18] = 2
    seq = [(18, (97 - 11, 7)), (1, None), (18, (138 - 11, 7)), (18, (20 - 11, 7)), (1, None),
           (17, (0, 3)), (1, None)]       # 17: L[257], D[0], D[1] are zero
    lc, dc = dyn(w, L, D, cl=cl, cl_syms=seq)
    sym(w, lc, 97); sym(w, lc, 256)

@vec("stored block, LEN 0, then a fixed one", "ok", "ok")
def _(w):
    w.put(0, 1); w.put(0, 2); w.align(); w.put(0, 16); w.put(0xFFFF, 16)
    w.put(1, 1); w.put(1, 2); w.code(0x30 + 97, 8); w.code(0, 7)

@vec("stored block, nonzero padding before LEN", "ok", "ok")
def _(w):
    w.put(1, 1); w.put(0, 2); w.put(0b10101, 5); w.put(3, 16); w.put(0xFFFF ^ 3, 16)
    for c in b"abc":
        w.put(c, 8)

FIXED_LIT = [8] * 144 + [9] * 112 + [7] * 24 + [8] * 8

@vec("length 258 as symbol 284 + extra 31 (the table says 227-257)", "ok", "ok")
def _(w):
    w.put(1, 1); w.put(1, 2)
    lc = canon(FIXED_LIT)
    sym(w, lc, 97)
    sym(w, lc, 284); w.put(31, 5)           # 227 + 31 = 258
    w.code(0, 5)                             # distance 1
    sym(w, lc, 256)

@vec("stored block, NLEN wrong", "bad", "bad")
def _(w):
    w.put(1, 1); w.put(0, 2); w.align(); w.put(3, 16); w.put(3, 16)
    for c in b"abc":
        w.put(c, 8)

@vec("stored block, truncated", "bad", "bad")
def _(w):
    w.put(1, 1); w.put(0, 2); w.align(); w.put(3, 16); w.put(0xFFFF ^ 3, 16)
    w.put(ord("a"), 8)

@vec("block type 3", "bad", "bad")
def _(w):
    w.put(1, 1); w.put(3, 2); w.put(0, 13)

def zlib_verdict(s):
    d = zlib.decompressobj(-15)
    try:
        d.decompress(s)
    except zlib.error:
        return "bad"
    return "ok" if d.eof else "bad"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", default=None)
    a = ap.parse_args()
    tmp = a.write or tempfile.mkdtemp(prefix="edge")
    os.makedirs(tmp, exist_ok=True)
    paths, rows = [], []
    for i, (name, rfc, zl, f) in enumerate(VECS):
        w = W(); f(w)
        s = w.bytes()
        p = os.path.join(tmp, "%02d.deflate" % i)
        open(p, "wb").write(s)
        paths.append(p); rows.append((name, rfc, zl, s))
    res = subprocess.run([TOOL, "--batch"], input="\n".join(paths) + "\n", capture_output=True,
                         text=True, check=True).stdout.splitlines()
    bad = 0
    for (name, rfc, zl, s), line in zip(rows, res):
        f = line.split()
        ours = f[1]
        flag = ("ok" if f[2] == "1" else "bad") if ours == "ok" else "bad"
        zreal = zlib_verdict(s)
        okv = ours == rfc and flag == zl and zreal == zl
        bad += not okv
        print("%s  %-62s rfc %-3s ours %-3s | zlib expected %-3s flag %-3s real %-3s" %
              ("  " if okv else "!!", name, rfc, ours, zl, flag, zreal))
    print("mismatches:", bad)
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
