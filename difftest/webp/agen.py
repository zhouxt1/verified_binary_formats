#!/usr/bin/env python3
"""Animated WebP files, generated: frames from gen.py's valid streams
(small, with and without the alpha hint, pixels of every alpha), placed on
a canvas at even offsets, with every dispose and blend method, durations,
ANIM background and loop count, other chunks before, between and after the
frames (and unknown chunks at the end of a frame); and mutants (header
bytes flipped, sizes off by a little, flags changed, truncations). Each
through libwebp's WebPAnimDecoder (build/adec) and an animation decoder
under test: the model (animmodel.py, default) or the verified one
(`--tool batch-anim`). Canvases and timestamps compared frame by frame.

Differences must be libwebp's known ones, each checked: `lib` (the
decoder says libwebp refuses), libwebp's reading (`libwebp_view`: the ANMF
chunk's size ignored past its image chunks, a frame's VP8L padding byte
read as bitstream, a 5-byte ANIM's padding byte read as the loop count,
an ANMF without a bitstream chunk dropped;
the model on the rewritten file must give libwebp's frames), `lossy`.

  agen.py [-n N] [--seed S] [--tool model|batch-anim] [--save DIR]
"""
import argparse
import collections
import multiprocessing
import os
import random
import struct
import subprocess
import sys

import animmodel
import cdiff
import gen
import wlib

ADEC = os.path.join(wlib.HERE, "build", "adec")


def frame_streams(seed, n):
    out = []
    i = 0
    rng = random.Random(seed)
    while len(out) < n:
        s, what = gen.one((seed + 5000, i, 0.0))
        i += 1
        if what == "valid" and len(s) > 5:
            w, h = cdiff.vp8l_dims(s)
            if w * h <= 48 * 40:
                out.append(s)
    return out


def anmf(x, y, w, h, dur, bits, subchunks):
    body = (x // 2).to_bytes(3, "little") + (y // 2).to_bytes(3, "little")
    body += (w - 1).to_bytes(3, "little") + (h - 1).to_bytes(3, "little")
    body += dur.to_bytes(3, "little") + bytes([bits])
    return cdiff.chunk(b"ANMF", body + b"".join(subchunks))


def make(rng, pool):
    k = rng.choice([1, 2, 2, 3, 4, 6])
    frames = [rng.choice(pool) for _ in range(k)]
    dims = [cdiff.vp8l_dims(s) for s in frames]
    cw = max(d[0] for d in dims) + rng.choice([0, 0, 1, 2, 7])
    ch = max(d[1] for d in dims) + rng.choice([0, 0, 1, 2, 7])
    flags = 0x02 | rng.choice([0, 0x10, 0x10, 0x20, 0x08]) | (rng.choice([0x01, 0x40, 0x80]) if rng.random() < 0.05 else 0)
    vp8x = bytes([flags, 0, 0, 0]) + (cw - 1).to_bytes(3, "little") + (ch - 1).to_bytes(3, "little")
    cs = [cdiff.chunk(b"VP8X", vp8x)]
    if rng.random() < 0.2:
        cs.append(cdiff.chunk(b"ICCP", b"icc!"))
    cs.append(cdiff.chunk(b"ANIM", struct.pack("<IH", rng.getrandbits(32), rng.choice([0, 1, 3]))))
    for s, (w, h) in zip(frames, dims):
        x = rng.randrange(0, cw - w + 1) & ~1
        y = rng.randrange(0, ch - h + 1) & ~1
        bits = rng.randrange(4)
        fw, fh = (w, h) if rng.random() < 0.9 else (w + 1, h)  # ANMF size vs the bitstream's
        sub = [cdiff.chunk(b"VP8L", s)]
        if rng.random() < 0.1:
            sub.append(cdiff.chunk(b"XYZW", b"123"))
        cs.append(anmf(x, y, fw, fh, rng.choice([0, 1, 40, 100, 0xffffff]), bits, sub))
        if rng.random() < 0.1:
            cs.append(cdiff.chunk(b"ABCD", b"between"))
        if rng.random() < 0.03:  # a frame with no bitstream chunk
            cs.append(anmf(0, 0, 1, 1, 7, 0, [cdiff.chunk(b"XYZW", b"no image")]))
    if rng.random() < 0.2:
        cs.append(cdiff.chunk(b"EXIF", b"exif"))
    return cdiff.riff(cs)


def mutate(rng, f):
    f = bytearray(f)
    k = rng.random()
    if k < 0.3:
        i = rng.randrange(min(len(f), 60))
        f[i] ^= 1 << rng.randrange(8)
    elif k < 0.55:
        offs = [4] + [i + 4 for i in range(12, len(f) - 8) if bytes(f[i:i + 4]) in
                      (b"ANMF", b"ANIM", b"VP8L", b"VP8X", b"XYZW", b"ICCP")]
        o = rng.choice(offs)
        v = struct.unpack_from("<I", f, o)[0] + rng.choice([-2, -1, 1, 2, -16])
        struct.pack_into("<I", f, o, v & 0xffffffff)
    elif k < 0.8:  # an ANMF's flags byte or offsets
        offs = [i for i in range(12, len(f) - 24) if bytes(f[i:i + 4]) == b"ANMF"]
        if offs:
            o = rng.choice(offs) + 8
            f[o + rng.choice([0, 3, 6, 9, 15])] ^= 1 << rng.randrange(8)
    else:
        f = f[:rng.randrange(1, len(f))]
    return bytes(f)


def build(job):
    seed, i, pool = job
    rng = random.Random(seed * 104729 + i)
    f = make(rng, pool)
    return [(f, "anim"), (mutate(rng, f), "mutant")]


def run_adec(files, limit):
    data = b"".join(struct.pack("<I", len(x)) + x for x in files)
    out = subprocess.run([ADEC, "-n", str(limit)], input=data, stdout=subprocess.PIPE, check=True).stdout
    res, i = [], 0
    for _ in files:
        st = out[i]
        i += 1
        if not st:
            res.append(None)
            continue
        cw, ch, loops, bg, n = struct.unpack_from("<5I", out, i)
        i += 20
        frames = []
        for _ in range(n):
            ts = struct.unpack_from("<I", out, i)[0]
            px = list(struct.unpack_from("<%dI" % (cw * ch), out, i + 4))
            i += 4 + 4 * cw * ch
            frames.append((ts, px))
        res.append((cw, ch, loops, bg, frames))
    assert i == len(out)
    return res


def run_model(files):
    streams = []
    idx = {}

    def collect(bs):
        idx.setdefault(bytes(bs), len(streams))
        if len(streams) < len(idx):
            streams.append(bytes(bs))
        return (1, 1, [0], 0)  # a placeholder, so that parsing goes on to every frame
    for f in files:
        animmodel.anim(f, collect)
    decoded = wlib.run_ours([wlib.even(s) for s in streams], "batch") if streams else []
    table = {}
    for s, d in zip(streams, decoded):
        if d is None or d == "skip":
            table[s] = None
        else:
            w, h, px, _ = d
            table[s] = (w, h, list(struct.unpack("<%dI" % (w * h), px)), (s[4] >> 4) & 1 if len(s) > 4 else 0)
    # an odd-length stream was given a zero byte for the batch; the model's
    # frames are decoded from their chunk's payload exactly
    table2 = {}
    for s in streams:
        table2[s] = table[s] if len(s) % 2 == 0 else None
    odd = [s for s in streams if len(s) % 2 == 1]
    if odd:
        dec = wlib.run_ours(odd, "batch")
        for s, d in zip(odd, dec):
            if d is not None and d != "skip":
                w, h, px, _ = d
                table2[s] = (w, h, list(struct.unpack("<%dI" % (w * h), px)), (s[4] >> 4) & 1)
    return [animmodel.anim(f, lambda bs: table2.get(bytes(bs))) for f in files]


def libwebp_view(f):
    """The file as libwebp's demuxer reads it (a rewrite, so the model can
    recompute libwebp's frames): an ANMF chunk ends where its image chunks
    do (libwebp resumes top-level parsing there, whatever the ANMF's size
    says); an odd-sized VP8L chunk in a frame includes its padding byte
    (libwebp's fragment is the padded chunk and the bit reader reads it
    all); an ANIM chunk of 5 bytes has 6 (libwebp reads its padding byte);
    an ANMF with no image chunk is gone (libwebp drops the frame).
    None if nothing changes."""
    body = bytearray(f[12:])
    end = min(len(body), animmodel.le(f, 4, 4) - 4)
    out = bytearray()
    i = 0
    changed = False
    while i + 8 <= end:
        tag = bytes(body[i:i + 4])
        size = animmodel.le(body, i + 4, 4)
        if tag == b"ANIM" and size == 5 and i + 14 <= end:
            out += b"ANIM" + struct.pack("<I", 6) + body[i + 8:i + 14]
            i += 14
            changed = True
            continue
        if tag == b"ANMF" and i + 24 <= end:
            hdr = body[i + 8:i + 24]
            q = i + 24
            subs = bytearray()
            for want in (b"ALPH", b"IMG"):
                if q + 8 > end:
                    break
                t2 = bytes(body[q:q + 4])
                s2 = animmodel.le(body, q + 4, 4)
                if (want == b"ALPH" and t2 == b"ALPH") or (want == b"IMG" and t2 in (b"VP8L", b"VP8 ")):
                    ps = s2 + (s2 & 1)
                    if t2 == b"VP8L" and s2 & 1 and q + 8 + ps <= end:
                        subs += t2 + struct.pack("<I", ps) + body[q + 8:q + 8 + ps]
                        changed = True
                    else:
                        subs += body[q:q + 8 + ps]
                    q += 8 + ps
            if q - i - 8 != size + (size & 1):
                changed = True
            if not subs:
                changed = True  # no image chunk: libwebp drops the frame
                i = q
                continue
            out += b"ANMF" + struct.pack("<I", 16 + len(subs)) + hdr + subs
            i = q
            continue
        ps = size + (size & 1)
        out += body[i:i + 8 + ps]
        i += 8 + ps
    if not changed:
        return None
    b2 = b"WEBP" + bytes(out)
    return b"RIFF" + struct.pack("<I", len(b2)) + b2


def explain(f, ours, ref, limit):
    if ours == "lossy":
        return "lossy"
    if ours == "toobig" and ref is None:
        return "too big for both"  # the decoder's limit and the oracle's (-n) are the same
    if isinstance(ours, tuple) and ours[0] * ours[1] * len(ours[4]) > limit:
        return "too big for the oracle"
    if isinstance(ours, tuple) and not ours[5] and ref is None:
        return "lib"
    if ref is not None:
        g = libwebp_view(f)
        if g is not None:
            r = run_model([g])[0]
            if isinstance(r, tuple) and (r[0], r[1], r[2], r[3]) == ref[:4] and r[4] == ref[4]:
                return "libwebp's reading (ANMF size, padding bytes)"
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=500)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--tool", default="model")
    ap.add_argument("--limit", type=int, default=1 << 22)
    ap.add_argument("--save")
    a = ap.parse_args()
    pool = frame_streams(a.seed, 60)
    with multiprocessing.Pool(min(32, os.cpu_count())) as p:
        recs = [r for rs in p.map(build, [(a.seed, i, pool) for i in range(a.n)]) for r in rs]
    files = [f for f, _ in recs]
    ref = run_adec(files, a.limit)
    if a.tool == "model":
        ours = run_model(files)
    else:
        import anim_tool
        ours = anim_tool.run(files, a.limit)
    tally = collections.Counter()
    fails = 0
    for k, ((f, what), x, y) in enumerate(zip(recs, ours, ref)):
        if x is None and y is None:
            tally["both refuse"] += 1
            continue
        if isinstance(x, tuple) and y is not None and x[:5] == y[:5] if False else (
                isinstance(x, tuple) and y is not None and (x[0], x[1], x[2], x[3]) == y[:4] and x[4] == y[4]):
            tally["same frames"] += 1
            continue
        why = explain(f, x, y, a.limit)
        if why:
            tally["known: " + why] += 1
            continue
        fails += 1
        desc = "refuses" if x is None else (x if isinstance(x, str) else "%d frames" % len(x[4]))
        rdesc = "refuses" if y is None else "%d frames" % len(y[4])
        detail = ""
        if isinstance(x, tuple) and y is not None and len(x[4]) == len(y[4]):
            for fi, ((t1, p1), (t2, p2)) in enumerate(zip(x[4], y[4])):
                if t1 != t2 or p1 != p2:
                    j = next((j for j in range(len(p1)) if p1[j] != p2[j]), None)
                    detail = " first difference: frame %d ts %d/%d pixel %s %s/%s" % (
                        fi, t1, t2, j, "%08x" % p1[j] if j is not None else "", "%08x" % p2[j] if j is not None else "")
                    break
        print("FAIL #%d (%s): ours %s, libwebp %s%s" % (k, what, desc, rdesc, detail))
        if a.save:
            os.makedirs(a.save, exist_ok=True)
            open(os.path.join(a.save, "afail%d_%d.webp" % (a.seed, k)), "wb").write(f)
    print("seed %d: %d files: %s, %d FAIL" % (a.seed, len(recs), ", ".join("%s %d" % kv for kv in sorted(tally.items())), fails))
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
