#!/usr/bin/env python3
"""Images of many kinds encoded by libwebp's cwebp (-lossless, every -z
preset, -q/-m pairs, -exact, -near_lossless), and 3 mutants of each
(bit flips, some in the first 40 bytes where the transforms and codes are;
truncations; extensions; overwritten bytes), decoded as bare VP8L
bitstreams by our decoder and libwebp's: verdicts and pixels compared.

  wdiff.py [-n N] [--seed S] [--tool batch-spec] [--limit PIXELS] [-j JOBS]
"""
import argparse
import multiprocessing
import os
import random
import struct
import subprocess
import sys
import tempfile

import wlib

CWEBP = os.path.join(wlib.HERE, "build", "cwebp")


def pam(w, h, px):
    """px: list of (r, g, b, a)."""
    hdr = "P7\nWIDTH %d\nHEIGHT %d\nDEPTH 4\nMAXVAL 255\nTUPLTYPE RGB_ALPHA\nENDHDR\n" % (w, h)
    return hdr.encode() + bytes(c for p in px for c in p)


def image(rng):
    """A random image of one of several kinds, small enough to decode fast."""
    kind = rng.choice(["noise", "gradient", "palette", "palette", "text", "tiles", "tiny", "flat",
                       "alpha", "photoish", "stripes"])
    if kind == "tiny":
        w, h = rng.randint(1, 5), rng.randint(1, 5)
    elif kind in ("stripes",):
        w, h = rng.choice([(1, rng.randint(1, 300)), (rng.randint(1, 300), 1), (rng.randint(1, 64), rng.randint(1, 64))])
    else:
        w, h = rng.randint(1, 160), rng.randint(1, 120)
    n = w * h
    if kind == "noise":
        bits = rng.choice([8, 4, 2, 1])
        m = 256 - (1 << (8 - bits))
        px = [tuple(rng.randrange(256) & m for _ in range(3)) + (255 if rng.random() < 0.7 else rng.randrange(256),)
              for _ in range(n)]
    elif kind == "gradient":
        a, b, c = rng.randint(-4, 4), rng.randint(-4, 4), rng.randint(0, 255)
        px = [(((x * a + y * b + c) & 255), ((x + y) * a) & 255, (x * y) & 255, 255) for y in range(h) for x in range(w)]
    elif kind in ("palette", "text", "stripes"):
        k = rng.choice([1, 2, 3, 4, 5, 8, 16, 17, 40, 200, 256])
        pal = [tuple(rng.randrange(256) for _ in range(4)) for _ in range(k)]
        if kind == "palette":
            px = [rng.choice(pal) for _ in range(n)]
        elif kind == "stripes":
            px = [pal[(x // rng.choice([1, 1, 3]) + y) % k] for y in range(h) for x in range(w)]
        else:  # runs, like text on a background
            px, cur = [], pal[0]
            for _ in range(n):
                if rng.random() < 0.15:
                    cur = rng.choice(pal)
                px.append(cur)
    elif kind == "tiles":
        t = rng.choice([2, 4, 8, 16])
        cols = {}
        px = []
        for y in range(h):
            for x in range(w):
                key = (x // t, y // t)
                if key not in cols:
                    cols[key] = tuple(rng.randrange(256) for _ in range(3)) + (255,)
                px.append(cols[key])
    elif kind == "flat":
        c = tuple(rng.randrange(256) for _ in range(4))
        px = [c] * n
    elif kind == "alpha":
        px = [(rng.randrange(256), rng.randrange(256), rng.randrange(256), rng.choice([0, 0, 255, rng.randrange(256)]))
              for _ in range(n)]
    elif kind == "photoish":  # smooth with noise: predictors and color transform
        px = []
        for y in range(h):
            for x in range(w):
                r = (128 + 60 * ((x * 7 + y * 3) % 50) // 50 + rng.randint(-3, 3)) & 255
                g = (r + 20 + rng.randint(-2, 2)) & 255
                b = (g // 2 + y + rng.randint(-2, 2)) & 255
                px.append((r, g, b, 255))
    else:
        px = [(0, 0, 0, 255)] * n
    return w, h, pam(w, h, px)


def cwebp_args(rng):
    a = ["-lossless", "-quiet"]
    r = rng.random()
    if r < 0.4:
        a += ["-z", str(rng.randint(0, 9))]
    else:
        a += ["-q", str(rng.choice([0, 1, 25, 50, 75, 90, 100])), "-m", str(rng.randint(0, 6))]
    if rng.random() < 0.3:
        a += ["-exact"]
    if rng.random() < 0.15:
        a += ["-near_lossless", str(rng.choice([0, 20, 40, 60, 80]))]
    return a


def vp8l(webp):
    """The VP8L chunk's payload of a simple lossless file."""
    assert webp[12:16] == b"VP8L", webp[12:16]
    n = struct.unpack_from("<I", webp, 16)[0]
    return webp[20:20 + n]


def mutate(rng, s):
    s = bytearray(s)
    k = rng.random()
    if k < 0.35:  # bit flips, often early (header, transforms, prefix codes)
        for _ in range(rng.randint(1, 3)):
            i = rng.randrange(min(len(s), 40)) if rng.random() < 0.6 else rng.randrange(len(s))
            s[i] ^= 1 << rng.randrange(8)
    elif k < 0.55:  # truncate
        s = s[:rng.randrange(len(s))]
    elif k < 0.7:  # extend
        s += bytes(rng.randrange(256) for _ in range(rng.randint(1, 20)))
    else:  # overwrite a few bytes
        for _ in range(rng.randint(1, 4)):
            s[rng.randrange(len(s))] = rng.randrange(256)
    if len(s) >= 1:
        s[0] = 0x2f  # keep the signature, so both read on
    return bytes(s)


def encode(job):
    seed, i = job
    rng = random.Random(seed * 1000003 + i)
    w, h, img = image(rng)
    args = cwebp_args(rng)
    with tempfile.TemporaryDirectory() as d:
        src, dst = os.path.join(d, "a.pam"), os.path.join(d, "a.webp")
        open(src, "wb").write(img)
        subprocess.run([CWEBP] + args + [src, "-o", dst], check=True)
        s = vp8l(open(dst, "rb").read())
    muts = [mutate(rng, s) for _ in range(3)]
    return [(s, "%s img %dx%d" % (" ".join(args), w, h))] + [(m, "mutant") for m in muts]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=500)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--tool", default="batch-spec")
    ap.add_argument("--limit", type=int, default=1 << 22)
    ap.add_argument("-j", type=int, default=min(32, os.cpu_count()))
    ap.add_argument("--save", help="directory for failing inputs")
    a = ap.parse_args()
    with multiprocessing.Pool(a.j) as pool:
        recs = [r for rs in pool.map(encode, [(a.seed, i) for i in range(a.n)]) for r in rs]
    recs = [(wlib.even(x), what) for x, what in recs]
    inputs = [r[0] for r in recs]
    ours = wlib.run_ours(inputs, a.tool, a.limit)
    ref = wlib.run_libwebp(inputs, a.limit)
    fails = ok_img = ok_err = lenient = 0
    for k, ((s, what), x, y) in enumerate(zip(recs, ours, ref)):
        if wlib.same(x, y):
            if x is None:
                ok_err += 1
            else:
                ok_img += 1
                lenient += not x[3]["strict"]
            if what != "mutant" and x is None:
                print("encoder output refused by both?", what)
                fails += 1
            continue
        fails += 1
        print("FAIL #%d (%s): ours %s, libwebp %s" % (k, what, wlib.describe(x), wlib.describe(y)))
        if x is not None and y is not None and x[:2] == y[:2]:
            print("     first differing pixel (index, ours, libwebp):", wlib.first_diff(x, y))
        if a.save:
            os.makedirs(a.save, exist_ok=True)
            open(os.path.join(a.save, "fail%d.vp8l" % k), "wb").write(s)
    print("seed %d: %d streams (%d encoded, %d mutants): %d images agree (%d lenient), %d both refuse, %d FAIL" %
          (a.seed, len(recs), a.n, 3 * a.n, ok_img, lenient, ok_err, fails))
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
