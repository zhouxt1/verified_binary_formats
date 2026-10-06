#!/usr/bin/env python3
"""Print a VP8 key frame's headers (RFC 6386 9.2-9.11): the frame tag and
the first partition's fields up to the skip probability, read with the
RFC's boolean decoder (7.3), which shifts in zeros past the end.

  vp8hdr.py FRAME...
"""
import struct
import sys

import llib


class Bool:
    def __init__(self, b):
        self.b, self.i = b, 0
        self.value = 0
        for _ in range(2):
            self.value = (self.value << 8) | self._byte()
        self.range, self.bit_count = 255, 0

    def _byte(self):
        self.i += 1
        return self.b[self.i - 1] if self.i <= len(self.b) else 0

    def bool(self, prob):
        split = 1 + (((self.range - 1) * prob) >> 8)
        big = split << 8
        if self.value >= big:
            r, self.range, self.value = 1, self.range - split, self.value - big
        else:
            r, self.range = 0, split
        while self.range < 128:
            self.value <<= 1
            self.range <<= 1
            self.bit_count += 1
            if self.bit_count == 8:
                self.bit_count = 0
                self.value |= self._byte()
        return r

    def lit(self, n):
        v = 0
        for _ in range(n):
            v = (v << 1) | self.bool(128)
        return v

    def signed(self, n):
        v = self.lit(n)
        return -v if self.bool(128) else v

    def opt(self, n):
        return self.signed(n) if self.bool(128) else 0


def header(f):
    """The fields as a dict."""
    tag = f[0] | f[1] << 8 | f[2] << 16
    h = {"version": tag >> 1 & 7, "show": tag >> 4 & 1, "p0": tag >> 5,
         "w": struct.unpack_from("<H", f, 6)[0] & 0x3fff, "h": struct.unpack_from("<H", f, 8)[0] & 0x3fff,
         "scale": (f[7] >> 6, f[9] >> 6), "len": len(f)}
    d = Bool(f[10:10 + h["p0"]])
    h["cs"], h["clamp"] = d.lit(1), d.lit(1)
    seg = d.lit(1)
    if seg:
        um, ud = d.lit(1), d.lit(1)
        s = {"update_map": um, "update_data": ud}
        if ud:
            s["abs"] = d.lit(1)
            s["q"] = [d.opt(7) for _ in range(4)]
            s["lf"] = [d.opt(6) for _ in range(4)]
        if um:
            s["probs"] = [d.lit(8) if d.lit(1) else 255 for _ in range(3)]
        h["seg"] = s
    h["simple"], h["level"], h["sharp"] = d.lit(1), d.lit(6), d.lit(3)
    if d.lit(1):
        h["lf_delta"] = True
        if d.lit(1):
            h["ref_d"] = [d.opt(6) for _ in range(4)]
            h["mode_d"] = [d.opt(6) for _ in range(4)]
    h["parts"] = 1 << d.lit(2)
    h["q"] = d.lit(7)
    h["dq"] = [d.opt(4) for _ in range(5)]
    h["refresh"] = d.lit(1)
    ups = []
    for k, p in enumerate(llib.COEFF_UPDATE_PROBS):
        if d.bool(p):
            ups.append((k, d.lit(8)))
    h["prob_updates"] = len(ups)
    h["zero_probs"] = sum(1 for _, v in ups if v == 0)
    h["skip_prob"] = d.lit(8) if d.lit(1) else None
    h["p0_pos"] = d.i
    return h


if __name__ == "__main__":
    for p in sys.argv[1:]:
        print(p, header(open(p, "rb").read()))
