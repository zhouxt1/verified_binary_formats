#!/usr/bin/env python3
"""Images of many kinds encoded lossy by libwebp's cwebp (random -q, -m,
-segments, -sns, -f, -sharpness, -strong/-nostrong, -preset, -alpha), and
3 mutants of each frame (bit flips, often in the first partition;
truncations; extensions; overwritten bytes; the frame tag's first
partition size), decoded as bare VP8 frames by RFC 6386's reference
decoder and by ours, and wrapped in a simple lossy WebP file by libwebp.

Ours must agree with the reference decoder on every stream (verdict and
planes): a disagreement is a FAIL. Where ours sets its `lib` flag, libwebp
must give the same image too: a difference is a FAIL. The reference
decoder and libwebp are compared and their differences counted by kind,
and each explained by the notes the spec records (vp8spec::Notes).

  ldiff.py [-n N] [--seed S] [--tool batch-vp8-spec] [--limit PIXELS] [-j JOBS] [--save DIR]
"""
import argparse
import multiprocessing
import os
import random
import subprocess
import sys
import tempfile

import llib
import wdiff

CWEBP = os.path.join(llib.HERE, "build", "cwebp")


def cwebp_args(rng):
    a = ["-quiet"]
    if rng.random() < 0.2:
        a += ["-preset", rng.choice(["default", "photo", "picture", "drawing", "icon", "text"])]
    a += ["-q", str(rng.choice([0, 1, 5, 25, 50, 75, 90, 95, 100])), "-m", str(rng.randint(0, 6))]
    if rng.random() < 0.5:
        a += ["-segments", str(rng.randint(1, 4))]
    if rng.random() < 0.4:
        a += ["-sns", str(rng.choice([0, 25, 50, 100]))]
    if rng.random() < 0.5:
        a += ["-f", str(rng.choice([0, 10, 30, 60, 100]))]
    if rng.random() < 0.4:
        a += ["-sharpness", str(rng.randint(0, 7))]
    if rng.random() < 0.5:
        a += [rng.choice(["-strong", "-nostrong"])]
    if rng.random() < 0.15:
        a += ["-af"]
    if rng.random() < 0.1:
        a += ["-partition_limit", str(rng.choice([0, 50, 100]))]
    if rng.random() < 0.1:
        a += ["-sharp_yuv"]
    return a


def mutate(rng, s):
    s = bytearray(s)
    k = rng.random()
    if k < 0.35:  # bit flips, often in the header and first partition
        for _ in range(rng.randint(1, 3)):
            i = rng.randrange(min(len(s), 60)) if rng.random() < 0.6 else rng.randrange(len(s))
            s[i] ^= 1 << rng.randrange(8)
    elif k < 0.55:  # truncate
        s = s[:rng.randrange(len(s))]
    elif k < 0.65:  # extend
        s += bytes(rng.randrange(256) for _ in range(rng.randint(1, 20)))
    elif k < 0.75 and len(s) >= 3:  # another first partition size
        raw = s[0] | s[1] << 8 | s[2] << 16
        p0 = max(0, (raw >> 5) + rng.randint(-8, 8))
        raw = (raw & 31) | (p0 & 0x7ffff) << 5
        s[0:3] = bytes([raw & 255, raw >> 8 & 255, raw >> 16])
    else:  # overwrite a few bytes
        for _ in range(rng.randint(1, 4)):
            s[rng.randrange(len(s))] = rng.randrange(256)
    if len(s) >= 1:
        s[0] &= 0xfe  # keep it a key frame
    return bytes(s)


def encode(job):
    seed, i = job
    rng = random.Random(seed * 1000003 + i)
    w, h, img = wdiff.image(rng)
    args = cwebp_args(rng)
    with tempfile.TemporaryDirectory() as d:
        src, dst = os.path.join(d, "a.pam"), os.path.join(d, "a.webp")
        open(src, "wb").write(img)
        subprocess.run([CWEBP] + args + [src, "-o", dst], check=True)
        f = open(dst, "rb").read()
    s = llib.vp8_payload(f)
    muts = [mutate(rng, s) for _ in range(3)]
    return [(s, f, "%s img %dx%d" % (" ".join(args), w, h))] + [(m, None, "mutant") for m in muts]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=500)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--tool", default="batch-vp8-spec")
    ap.add_argument("--limit", type=int, default=1 << 22)
    ap.add_argument("-j", type=int, default=min(32, os.cpu_count()))
    ap.add_argument("--save", help="directory for failing inputs")
    ap.add_argument("-v", action="store_true", help="list reference/libwebp differences")
    a = ap.parse_args()
    with multiprocessing.Pool(a.j) as pool:
        recs = [r for rs in pool.map(encode, [(a.seed, i) for i in range(a.n)]) for r in rs]
    fails = llib.compare(recs, a.tool, a.limit, a.save, a.v, "seed %d: %d frames (%d encoded, %d mutants)" %
                         (a.seed, len(recs), a.n, 3 * a.n))
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
