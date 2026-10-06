#!/usr/bin/env python3
"""Random VP8 key frames, built with a boolean encoder (RFC 6386 7.3): the
frame header and the first partition's header fields are chosen at random
over their whole ranges (segmentation with absolute or delta values and
extreme quantizer and filter adjustments, both filter types, filter
deltas, 1 to 8 token partitions, quantizer deltas, coefficient
probability updates to any value, 0 included, the skip probability),
and the per-macroblock data after them (modes, then tokens in each
partition) is random bits, sometimes biased towards 0 or 1 (1s give
long runs of the largest coefficients). Occasionally the frame is
hidden, has reserved bits set, a short partition, an oversized partition
size, a 1-byte or empty partition, or a partition starting with 0xff.

Decoded as ldiff.py does (reference decoder, ours, libwebp): ours must
agree with the reference decoder on every frame, and with libwebp where it
sets `lib`.

  gen8.py [-n N] [--seed S] [--tool batch-vp8-spec] [--limit PIXELS] [--save DIR] [-v]
"""
import argparse
import random
import struct
import sys

import llib


class BoolEncoder:
    """RFC 6386 7.3's encoder (write_bool, flush_bool_encoder)."""

    def __init__(self):
        self.out = bytearray()
        self.range = 255
        self.bottom = 0
        self.bit_count = 24

    def _add_one(self):
        i = len(self.out) - 1
        while i >= 0 and self.out[i] == 255:
            self.out[i] = 0
            i -= 1
        if i >= 0:
            self.out[i] += 1

    def put(self, prob, bit):
        split = 1 + (((self.range - 1) * prob) >> 8)
        if bit:
            self.bottom += split
            self.range -= split
        else:
            self.range = split
        while self.range < 128:
            self.range <<= 1
            if self.bottom & (1 << 31):
                self._add_one()
            self.bottom = (self.bottom << 1) & 0xffffffff
            self.bit_count -= 1
            if not self.bit_count:
                self.out.append((self.bottom >> 24) & 0xff)
                self.bottom &= (1 << 24) - 1
                self.bit_count = 8

    def flag(self, b):
        self.put(128, b)

    def uint(self, v, n):
        for i in reversed(range(n)):
            self.flag((v >> i) & 1)

    def int(self, v, n):
        self.uint(abs(v), n)
        self.flag(v < 0)

    def maybe_int(self, v, n):
        self.flag(v != 0)
        if v != 0:
            self.int(v, n)

    def flush(self):
        c = self.bit_count
        v = self.bottom
        if v & (1 << (32 - c)):
            self._add_one()
        v = (v << (c & 7)) & 0xffffffff
        c >>= 3
        while c > 0:
            c -= 1
            v = (v << 8) & 0xffffffff
        for _ in range(4):
            self.out.append((v >> 24) & 0xff)
            v = (v << 8) & 0xffffffff
        return bytes(self.out)


def signed(rng, n, special=()):
    """A value for maybe_int(n): often 0, often extreme."""
    m = (1 << n) - 1
    r = rng.random()
    if r < 0.4:
        return 0
    if r < 0.6 and special:
        return rng.choice(special)
    if r < 0.75:
        return rng.choice([m, -m, 1, -1])
    return rng.randint(-m, m)


def random_bits(rng, enc, n, bias):
    for _ in range(n):
        enc.flag(1 if rng.random() < bias else 0)


def frame(rng):
    what = []
    if rng.random() < 0.85:
        w, h = rng.randint(1, 72), rng.randint(1, 72)
    else:
        w, h = rng.randint(1, 300), rng.randint(1, 40)
        if rng.random() < 0.5:
            w, h = h, w
    mbw, mbh = (w + 15) // 16, (h + 15) // 16
    e = BoolEncoder()
    # Color space and clamping type.
    cs = 0 if rng.random() < 0.95 else rng.randint(1, 3)
    if cs:
        what.append("reserved")
    e.uint(cs, 2)
    # Segmentation.
    seg = rng.random() < 0.5
    e.flag(seg)
    if seg:
        um, ud = rng.random() < 0.6, rng.random() < 0.6
        e.flag(um)
        e.flag(ud)
        if ud:
            e.flag(rng.random() < 0.5)  # abs
            for _ in range(4):
                e.maybe_int(signed(rng, 7, (-1, 127, -127, 64, -64)), 7)
            for _ in range(4):
                e.maybe_int(signed(rng, 6, (-63, 63, 30, -30)), 6)
        if um:
            for _ in range(3):
                if rng.random() < 0.7:
                    e.flag(1)
                    e.uint(rng.choice([0, 1, 128, 255, rng.randrange(256)]), 8)
                else:
                    e.flag(0)
        what.append("seg%s%s" % ("M" if um else "", "D" if ud else ""))
    # Loop filter.
    simple = rng.random() < 0.3
    e.flag(simple)
    level = rng.choice([0, 1, 14, 15, 39, 40, 63, rng.randint(0, 63), rng.randint(0, 63)])
    e.uint(level, 6)
    e.uint(rng.randint(0, 7), 3)
    delta = rng.random() < 0.4
    e.flag(delta)
    if delta:
        upd = rng.random() < 0.8
        e.flag(upd)
        if upd:
            for _ in range(8):
                e.maybe_int(signed(rng, 6, (-63, 63)), 6)
    # Partitions.
    lp = rng.choice([0, 0, 1, 2, 3])
    e.uint(lp, 2)
    nparts = 1 << lp
    # Quantizer.
    e.uint(rng.choice([0, 0, 1, 127, rng.randint(0, 127), rng.randint(0, 127)]), 7)
    for _ in range(5):
        e.maybe_int(signed(rng, 4, (-15, 15)), 4)
    e.flag(rng.random() < 0.5)  # refresh_entropy_probs
    # Coefficient probability updates.
    rate = rng.choice([0, 0, 0.01, 0.05, 0.3])
    for p in llib.COEFF_UPDATE_PROBS:
        u = rng.random() < rate
        e.put(p, u)
        if u:
            e.uint(rng.choice([0, 1, 128, 254, 255, rng.randrange(256)]), 8)
    skip = rng.random() < 0.5
    e.flag(skip)
    if skip:
        e.uint(rng.choice([0, 1, 128, 255, rng.randrange(256)]), 8)
    # Per-macroblock modes: random bits.
    bias = rng.choice([0.5, 0.5, 0.2, 0.8, 0.05, 0.95])
    nbits = mbw * mbh * rng.choice([20, 40, 80, 80, 80])
    if rng.random() < 0.1:
        nbits //= 8
        what.append("short-p0")
    random_bits(rng, e, nbits, bias)
    p0 = e.flush()
    # Token partitions: random bits, biased.
    parts = []
    for k in range(nparts):
        rows = len(range(k, mbh, nparts))
        t = BoolEncoder()
        b = rng.choice([0.5, 0.5, 0.3, 0.7, 0.05, 0.97])
        per = rng.choice([30, 100, 300, 600])
        random_bits(rng, t, rows * mbw * per, b)
        data = t.flush()
        r = rng.random()
        if r < 0.05:
            data = data[:rng.randrange(len(data) + 1)]
            what.append("short")
        elif r < 0.07:
            data = data[:1]
            what.append("1-byte")
        elif r < 0.09:
            data = b""
            what.append("empty")
        elif r < 0.11 and data:
            data = b"\xff" + data[1:]
            what.append("ff")
        parts.append(data)
    sizes = b"".join(struct.pack("<I", len(p))[:3] for p in parts[:-1])
    if rng.random() < 0.03 and nparts > 1:
        sizes = struct.pack("<I", len(parts[0]) + rng.randint(1, 50))[:3] + sizes[3:]
        what.append("oversize")
    version = rng.choice([0, 0, 0, 1, 2, 3]) if rng.random() < 0.97 else rng.randint(4, 7)
    show = 1 if rng.random() < 0.97 else 0
    if not show:
        what.append("hidden")
    tag = 0 | version << 1 | show << 4 | len(p0) << 5
    hdr = bytes([tag & 255, tag >> 8 & 255, tag >> 16 & 255, 0x9d, 0x01, 0x2a])
    hdr += struct.pack("<HH", w | rng.choice([0, 0, 0, 1, 2, 3]) << 14, h | rng.choice([0, 0, 0, 1, 2, 3]) << 14)
    return hdr + p0 + sizes + b"".join(parts), "gen %dx%d parts %d %s" % (w, h, nparts, " ".join(what))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--tool", default="batch-vp8-spec")
    ap.add_argument("--limit", type=int, default=1 << 22)
    ap.add_argument("--save", help="directory for failing inputs")
    ap.add_argument("-v", action="store_true")
    a = ap.parse_args()
    rng = random.Random(a.seed)
    recs = []
    for _ in range(a.n):
        f, what = frame(rng)
        recs.append((f, None, what))
    fails = llib.compare(recs, a.tool, a.limit, a.save, a.v, "gen8 seed %d: %d frames" % (a.seed, a.n))
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
