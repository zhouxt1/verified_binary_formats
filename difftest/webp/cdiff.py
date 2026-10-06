#!/usr/bin/env python3
"""The WebP container: VP8L streams (from gen.py, and cwebp's) wrapped in
files of many shapes, and mutants of them, through the verified container
decoder (`vwebp-tool batch-file`, `vwebp::riff::webp_x`) and libwebp
(`wdec`, WebPDecode). Images compared pixel by pixel.

First every file of libwebp-test-data, and edge files built by hand
(`edge_files`). Then shapes: simple lossless files; extended ones (VP8X of 10 bytes or more,
reserved bits set, ICC/Alpha/Exif/XMP flags) with chunks before the image
(ICCP, ALPH, EXIF, XMP, unknown, odd-sized) and after it; canvases that
match the image or not; the Animation flag; lossy chunks (VP8 payloads from
libwebp-test-data); data after the RIFF; a missing padding byte. Mutants:
bytes flipped in the container's headers, sizes off by a little, truncations.

Where libwebp and the spec differ, each difference must be one of libwebp's
known ways (difftest/webp/README.md), checked, not assumed:

  overrun    libwebp decodes an image whose bits run past its chunk: its
             image is the spec's image of the bitstream extended by the file's
             bytes after the payload.
  raw        the first chunk is not VP8/VP8L/VP8X: libwebp's image is the
             spec's of the bytes from that chunk's header on, as a bitstream.
  lib        the spec's `lib` flag is false and libwebp refuses the file.
  lossy      the file is lossy, which this decoder does not decode (libwebp
             decodes it or refuses it).
  animated   the file is animated: libwebp refuses (UNSUPPORTED_FEATURE).

  cdiff.py [-n N] [--seed S] [--save DIR]
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

import gen
import wlib


def chunk(tag, body, pad=True):
    return tag + struct.pack("<I", len(body)) + body + (b"\0" if pad and len(body) & 1 else b"")


def riff(chunks, size_delta=0, trailing=b""):
    body = b"WEBP" + b"".join(chunks)
    return b"RIFF" + struct.pack("<I", len(body) + size_delta) + body + trailing


def vp8l_dims(s):
    v = int.from_bytes(s[1:5], "little")
    return (v & 0x3fff) + 1, ((v >> 14) & 0x3fff) + 1


LOSSY = []


def lossy_payloads():
    for f in sorted(glob.glob(os.path.join(wlib.HERE, "build", "test-data", "*.webp"))):
        d = open(f, "rb").read()
        if d[12:16] == b"VP8 ":
            n = struct.unpack_from("<I", d, 16)[0]
            LOSSY.append(d[20:20 + n])
            if len(LOSSY) >= 8:
                break


def rand_chunk(rng):
    tag = rng.choice([b"ICCP", b"ALPH", b"EXIF", b"XMP ", b"ABCD", b"anmf", b"ANIM", b"ANMF", b"XYZW"])
    return chunk(tag, bytes(rng.getrandbits(8) for _ in range(rng.choice([0, 1, 3, 10, 64]))))


def wrap(rng, s):
    """A file around the VP8L stream `s`, and what shape it is."""
    w, h = vp8l_dims(s)
    k = rng.random()
    if k < 0.25:
        return riff([chunk(b"VP8L", s)]), "simple"
    if k < 0.33:
        return riff([chunk(b"VP8L", s)], trailing=bytes(rng.getrandbits(8) for _ in range(rng.randint(1, 20)))), "simple+trailing"
    if k < 0.38 and LOSSY:
        body = rng.choice(LOSSY)
        if rng.random() < 0.5:
            return riff([chunk(b"VP8 ", body)]), "lossy"
        return riff([chunk(b"VP8X", bytes([0, 0, 0, 0]) + bytes(6)), chunk(b"VP8 ", body)]), "lossy-x"
    flags = rng.choice([0, 0, 0x10, 0x20, 0x08, 0x04, 0xc1, 0x02])
    cw, ch = w, h
    if rng.random() < 0.1:
        cw, ch = w + rng.choice([-1, 1]) or 1, h
    xsize = 10 if rng.random() < 0.85 else rng.choice([11, 12, 14, 9])
    vp8x = bytes([flags]) + bytes(rng.getrandbits(8) if rng.random() < 0.1 else 0 for _ in range(3))
    vp8x += (cw - 1).to_bytes(3, "little") + (ch - 1).to_bytes(3, "little")
    vp8x = (vp8x + bytes(rng.getrandbits(8) for _ in range(max(0, xsize - 10))))[:xsize]
    pre = [rand_chunk(rng) for _ in range(rng.choice([0, 0, 1, 2, 4]))]
    post = [rand_chunk(rng) for _ in range(rng.choice([0, 1, 2]))]
    img = chunk(b"VP8L", s, pad=not (rng.random() < 0.1 and not post))
    return riff([chunk(b"VP8X", vp8x)] + pre + [img] + post), "extended flags=%02x x=%d pre=%d" % (flags, xsize, len(pre))


def mutate(rng, f):
    f = bytearray(f)
    k = rng.random()
    if k < 0.4:  # a byte of the container's headers
        idx = [i for i in range(len(f)) if i < 40] or [0]
        i = rng.choice(idx)
        f[i] ^= 1 << rng.randrange(8)
    elif k < 0.7:  # a size off by a little: the RIFF's, or a chunk's
        offs = [4] + [i + 4 for i in range(12, len(f) - 8) if bytes(f[i:i + 4]) in
                      (b"VP8L", b"VP8X", b"ICCP", b"ALPH", b"EXIF", b"XMP ", b"ABCD", b"VP8 ")]
        o = rng.choice(offs)
        v = struct.unpack_from("<I", f, o)[0] + rng.choice([-2, -1, 1, 2, 7, -7])
        struct.pack_into("<I", f, o, v & 0xffffffff)
    else:
        f = f[:rng.randrange(1, len(f))]
    return bytes(f)


def build(job):
    seed, i = job
    rng = random.Random(seed * 7919 + i)
    s, what = gen.one((seed + 1000, i, 0.0))
    if what != "valid" or len(s) < 5:
        s = bytes([0x2f, 0, 0, 0, 0]) + b"\x00" * 4  # tiny; mostly invalid
    f, shape = wrap(rng, s)
    out = [(f, shape)]
    for _ in range(2):
        out.append((mutate(rng, f), "mutant of " + shape))
    return out


def run_files(files, limit):
    data = b"".join(struct.pack("<I", len(x)) + x for x in files)
    env = dict(os.environ, VW_LIMIT=str(limit))
    out = subprocess.run([wlib.TOOL, "batch-file"], input=data, stdout=subprocess.PIPE, check=True, env=env).stdout
    res, i = [], 0
    for _ in files:
        st, lib = out[i], out[i + 1]
        i += 2
        if st == 1:
            w, h, strict = struct.unpack_from("<IIB", out, i)
            i += 9
            n = 4 * w * h
            res.append(("img", (w, h, out[i:i + n]), bool(lib), bool(strict)))
            i += n
        else:
            res.append(({0: "bad", 3: "lossy", 4: "animated", 5: "toobig"}[st], None, bool(lib), None))
    assert i == len(out)
    return res


def bare(streams):
    """The spec's image of each bare stream (vwebp-tool batch)."""
    return wlib.run_ours(streams, "batch")


def chunk_list(f):
    """(tag, payload start, size) of the chunks after WEBP, as far as they parse."""
    out, i = [], 12
    while i + 8 <= len(f):
        size = struct.unpack_from("<I", f, i + 4)[0]
        out.append((bytes(f[i:i + 4]), i + 8, size))
        i += 8 + size + (size & 1)
    return out


def explain(f, ours, ref):
    """Which known difference explains ours != ref, or None."""
    kind = ours[0]
    if kind == "lossy":
        return "lossy"  # not decoded here, whatever libwebp makes of it
    if kind == "animated" and ref is None:
        return "animated"
    if kind == "img" and ref is None and not ours[2]:
        return "lib"
    if kind == "bad" and ref is not None:
        cl = chunk_list(f)
        img = next(((a, n) for tag, a, n in cl if tag == b"VP8L"), None)
        cands = []
        if img:
            a, n = img
            cands.append(("overrun", f[a:]))          # the payload and everything after it
        cands.append(("raw", f[12:]))
        imgs = bare([c for _, c in cands])
        for (name, _), r in zip(cands, imgs):
            if r is not None and r != "skip" and r[:3] == ref[:3]:
                return name
    return None


def edge_files():
    """Hand-built files at the container's corners, from a corpus bitstream."""
    s = open(os.path.join(wlib.HERE, "build", "test-data", "lossless_vec_2_3.webp"), "rb").read()
    v = s[20:20 + struct.unpack_from("<I", s, 16)[0]]
    w, h = vp8l_dims(v)
    dims = (w - 1).to_bytes(3, "little") + (h - 1).to_bytes(3, "little")
    vp8x = chunk(b"VP8X", bytes(4) + dims)
    odd = v + b"\0" if len(v) % 2 == 0 else v  # an odd-sized payload
    out = []
    # the image chunk runs past the RIFF data (libwebp refuses too)
    body = b"WEBP" + vp8x + b"VP8L" + struct.pack("<I", len(v)) + v
    out.append((b"RIFF" + struct.pack("<I", len(body) - (len(v) - 100)) + body, "edge: chunk past the RIFF"))
    # the bare bitstream right after WEBP (libwebp decodes it: "raw")
    out.append((b"RIFF" + struct.pack("<I", 4 + len(v)) + b"WEBP" + v, "edge: raw bitstream"))
    # VP8X of 12 bytes (the RFC: unknown fields are ignored; libwebp refuses: "lib")
    out.append((riff([chunk(b"VP8X", bytes(4) + dims + b"\0\0"), chunk(b"VP8L", v)]), "edge: VP8X of 12 bytes"))
    # an odd-sized image chunk without its padding byte, simple and extended
    out.append((riff([chunk(b"VP8L", odd, pad=False)]), "edge: simple, no padding byte"))
    out.append((riff([vp8x, chunk(b"VP8L", odd, pad=False)]), "edge: extended, no padding byte"))
    # ALPH before VP8L, and chunks of every kind after it
    out.append((riff([vp8x, chunk(b"ALPH", b"\1\2\3"), chunk(b"VP8L", v), chunk(b"EXIF", b"x" * 5)]), "edge: ALPH + VP8L"))
    return out


def corpus_files():
    fs = sorted(glob.glob(os.path.join(wlib.HERE, "build", "test-data", "*.webp")))
    return [(open(f, "rb").read(), "corpus " + os.path.basename(f)) for f in fs]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--limit", type=int, default=1 << 22)
    ap.add_argument("-j", type=int, default=min(32, os.cpu_count()))
    ap.add_argument("--save")
    a = ap.parse_args()
    lossy_payloads()
    with multiprocessing.Pool(a.j) as pool:
        recs = [r for rs in pool.map(build, [(a.seed, i) for i in range(a.n)]) for r in rs]
    recs = corpus_files() + edge_files() + recs
    files = [r[0] for r in recs]
    ours = run_files(files, a.limit)
    ref = wlib.run_libwebp(files, a.limit)
    tally = collections.Counter()
    fails = 0
    for k, ((f, what), x, y) in enumerate(zip(recs, ours, ref)):
        if x[0] == "img" and y is not None and x[1] == y[:3]:
            tally["same image"] += 1
            continue
        if x[0] == "bad" and y is None:
            tally["both refuse"] += 1
            continue
        if x[0] == "toobig":
            tally["too big"] += 1
            continue
        why = explain(f, x, y)
        if why:
            tally["known: " + why] += 1
            continue
        fails += 1
        print("FAIL #%d (%s): ours %s lib=%s, libwebp %s" % (k, what, x[0], x[2], wlib.describe(y)))
        if a.save:
            os.makedirs(a.save, exist_ok=True)
            open(os.path.join(a.save, "cfail%d_%d.webp" % (a.seed, k)), "wb").write(f)
    for (f, what), x, y in zip(recs, ours, ref):
        if what.startswith("edge"):
            print("  %-34s ours %-8s lib=%-5s libwebp %s" % (what, x[0], x[2], wlib.describe(y)))
    print("seed %d: %d files: %s, %d FAIL" % (a.seed, len(recs), ", ".join("%s %d" % kv for kv in sorted(tally.items())), fails))
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
