#!/usr/bin/env python3
"""Whole lossy WebP files through the lossy executable spec (`vwebp-tool
batch-lossy-file`: container, ALPH alpha, VP8 frame) and libwebp (ydec:
Y'CbCr and alpha planes): libwebp-test-data's files, images with and
without alpha encoded lossy by cwebp under random alpha options
(-alpha_method, -alpha_filter, -alpha_q, -exact, -noalpha), and mutants of
those (the ALPH header byte's fields, truncated or resized chunks, a second
ALPH, chunks inserted or dropped, the VP8X size, canvas and flags).

Where ours sets `lib`, libwebp must give the same planes and alpha (an
image without an ALPH chunk has alpha 255): a difference is a FAIL. The
other differences are counted.

  lfile.py [-n N] [--seed S] [--limit PIXELS] [--save DIR] [--tool batch-lossy-file|batch-lossy-file-v]
"""
import argparse
import collections
import glob
import multiprocessing
import os
import random
import struct
import subprocess
import sys
import tempfile

import llib
import wdiff

CWEBP = os.path.join(llib.HERE, "build", "cwebp")


def run_ours(files, limit=None, tool="batch-lossy-file"):
    env = dict(os.environ, **({"VW_LIMIT": str(limit)} if limit else {}))
    out = llib._run([llib.TOOL, tool], files, env)
    res, i = [], 0
    for _ in files:
        st = out[i]
        i += 1
        if st == 0:
            res.append(None)
        elif st == 2:
            res.append("other")
        else:
            w, h, lib, has_a = struct.unpack_from("<IIBB", out, i)
            i += 10
            y, u, v, i = llib._planes(out, i, w, h)
            a = None
            if has_a:
                a = out[i:i + w * h]
                i += w * h
            res.append((w, h, y, u, v, {"lib": bool(lib), "alpha": a}))
    assert i == len(out)
    return res


def same(o, l):
    if o is None or l is None:
        return o is l
    if o[:5] != l[:5]:
        return False
    oa, la = o[5]["alpha"], l[5]["alpha"]
    n = o[0] * o[1]
    return (oa or b"\xff" * n) == (la or b"\xff" * n)


def chunks(f):
    """The chunks of a RIFF WebP file: (tag, payload)."""
    out, i = [], 12
    while i + 8 <= len(f):
        n = struct.unpack_from("<I", f, i + 4)[0]
        out.append((f[i:i + 4], f[i + 8:i + 8 + n]))
        i += 8 + n + (n & 1)
    return out


def assemble(cs):
    body = b"WEBP" + b"".join(t + struct.pack("<I", len(p)) + p + (b"\0" if len(p) & 1 else b"") for t, p in cs)
    return b"RIFF" + struct.pack("<I", len(body)) + body


def mutate(rng, f):
    cs = chunks(f)
    k = rng.random()
    ai = [i for i, (t, _) in enumerate(cs) if t == b"ALPH"]
    if ai and k < 0.3:  # the ALPH header byte
        i = ai[0]
        p = bytearray(cs[i][1])
        if p:
            p[0] ^= 1 << rng.randrange(8)
        cs[i] = (b"ALPH", bytes(p))
    elif ai and k < 0.4:  # truncate or extend the alpha
        i = ai[0]
        p = cs[i][1]
        cs[i] = (b"ALPH", p[:rng.randrange(len(p) + 1)] if rng.random() < 0.6 else p + bytes(rng.randrange(256) for _ in range(rng.randint(1, 9))))
    elif ai and k < 0.45:  # a second ALPH, before or after
        i = ai[0]
        p = bytes(rng.randrange(256) for _ in range(rng.randint(1, 40)))
        cs.insert(i + rng.randint(0, 1), (b"ALPH", p))
    elif k < 0.55:  # an unknown or metadata chunk somewhere after the first
        cs.insert(rng.randint(1, len(cs)), (rng.choice([b"EXIF", b"XMP ", b"ICCP", b"ZZZZ", b"ALPH"]),
                                            bytes(rng.randrange(256) for _ in range(rng.randint(0, 12)))))
    elif k < 0.6 and len(cs) > 1:  # drop a chunk
        del cs[rng.randrange(len(cs))]
    elif k < 0.7 and cs[0][0] == b"VP8X":  # VP8X flags, canvas or size
        p = bytearray(cs[0][1])
        r = rng.random()
        if r < 0.4:
            p[0] ^= 1 << rng.randrange(8)
        elif r < 0.8:
            j = rng.choice([4, 7])
            p[j] = (p[j] + rng.choice([-1, 1])) & 255
        else:
            p += bytes(rng.randint(1, 4))
        cs[0] = (b"VP8X", bytes(p))
    else:  # the frame: a flipped bit or a truncation
        i = next(i for i, (t, _) in enumerate(cs) if t in (b"VP8 ", b"VP8L")) if any(t in (b"VP8 ", b"VP8L") for t, _ in cs) else None
        if i is not None and cs[i][1]:
            p = bytearray(cs[i][1])
            if rng.random() < 0.5:
                j = rng.randrange(len(p))
                p[j] ^= 1 << rng.randrange(8)
            else:
                p = p[:rng.randrange(len(p) + 1)]
            cs[i] = (cs[i][0], bytes(p))
    return assemble(cs)


def cwebp_args(rng):
    a = ["-quiet", "-q", str(rng.choice([0, 30, 75, 100])), "-m", str(rng.randint(0, 6))]
    a += ["-alpha_method", str(rng.randint(0, 1)), "-alpha_filter", rng.choice(["none", "fast", "best"]),
          "-alpha_q", str(rng.choice([0, 10, 50, 100]))]
    if rng.random() < 0.3:
        a += ["-exact"]
    if rng.random() < 0.1:
        a += ["-noalpha"]
    return a


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
    return [(f, "%s img %dx%d" % (" ".join(args), w, h))] + [(mutate(rng, f), "mutant") for _ in range(3)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=300)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--limit", type=int, default=1 << 25)
    ap.add_argument("-j", type=int, default=min(32, os.cpu_count()))
    ap.add_argument("--save")
    ap.add_argument("--tool", default="batch-lossy-file", help="batch-lossy-file-v: the verified decoder")
    a = ap.parse_args()
    recs = [(open(p, "rb").read(), "corpus " + os.path.basename(p))
            for p in sorted(glob.glob(os.path.join(llib.HERE, "build", "test-data", "*.webp")))]
    with multiprocessing.Pool(a.j) as pool:
        recs += [r for rs in pool.map(encode, [(a.seed, i) for i in range(a.n)]) for r in rs]
    files = [f for f, _ in recs]
    ours = run_ours(files, a.limit, a.tool)
    lib = llib.run_libwebp(files, a.limit)
    fails = 0
    kinds = collections.Counter()
    for k, ((f, what), o, l) in enumerate(zip(recs, ours, lib)):
        if o == "other":
            kinds["not lossy"] += 1
            continue
        if what.startswith("corpus") or (what != "mutant" and o is None):
            if o is None or not same(o, l):
                fails += 1
                print("FAIL #%d (%s): ours %s, libwebp %s" % (k, what, llib.describe(o), llib.describe(l)))
        if o is not None and o[5]["lib"] and not same(o, l):
            fails += 1
            print("FAIL #%d (%s): lib flag set, but libwebp %s" % (k, what, llib.describe(l)))
            if a.save:
                os.makedirs(a.save, exist_ok=True)
                open(os.path.join(a.save, "file%d.webp" % k), "wb").write(f)
        if o is None:
            kinds["both refuse" if l is None else "ours refuses, libwebp image"] += 1
        elif same(o, l):
            kinds["same image" + (" with alpha" if o[5]["alpha"] else "") + ("" if o[5]["lib"] else " (lib cleared)")] += 1
        else:
            kinds["libwebp refuses (lib cleared)" if l is None else "libwebp differs (lib cleared)"] += 1
    print("lfile seed %d: %d files: %d FAIL; %s" % (a.seed, len(recs), fails,
                                                    ", ".join("%s %d" % kv for kv in sorted(kinds.items()))))
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
