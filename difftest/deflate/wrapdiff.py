#!/usr/bin/env python3
"""zlib (RFC 1950) and gzip (RFC 1952) wrappers against Python's zlib.

Streams: zlib.compress at every level and window, gzip members with and
without FEXTRA, FNAME, FCOMMENT and FHCRC (built by hand, since Python's
gzip module writes only FNAME), and their bit-flipped, truncated and
extended mutants. vdeflate's verdict must be zlib's (a single member, with
windowBits 15 or 31), with the same data and the same end.

    difftest/deflate/wrapdiff.py [-n N] [--seed S]
"""
import argparse, os, random, struct, subprocess, sys, tempfile, zlib

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TOOL = os.path.join(ROOT, "target/release/vdeflate-tool")

def fnv(b):
    h = 0xcbf29ce484222325
    for x in b:
        h = ((h ^ x) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return h

def ref(fmt, s):
    d = zlib.decompressobj(15 if fmt == "zlib" else 31)
    try:
        out = d.decompress(s, 1 << 28)
    except zlib.error:
        return None
    if not d.eof:
        return None
    return out, len(s) - len(d.unused_data)

def gzip_member(rng, data):
    flg = 0
    hdr = bytearray(b"\x1f\x8b\x08\x00") + struct.pack("<I", rng.randrange(1 << 32)) + bytes([rng.choice([0, 2, 4]), rng.randrange(256)])
    extra = b""
    if rng.random() < 0.4:
        flg |= 4
        x = os.urandom(rng.randrange(0, 300))
        extra += struct.pack("<H", len(x)) + x
    if rng.random() < 0.5:
        flg |= 8
        extra += bytes(rng.randrange(1, 256) for _ in range(rng.randrange(0, 40))) + b"\x00"
    if rng.random() < 0.4:
        flg |= 16
        extra += bytes(rng.randrange(1, 256) for _ in range(rng.randrange(0, 40))) + b"\x00"
    hdr[3] = flg
    h = bytes(hdr) + extra
    if rng.random() < 0.4:
        h = bytes([h[0], h[1], h[2], h[3] | 2]) + h[4:]
        h += struct.pack("<H", zlib.crc32(h) & 0xFFFF)
    c = zlib.compressobj(rng.choice([0, 1, 6, 9]), zlib.DEFLATED, -15)
    body = c.compress(data) + c.flush()
    return h + body + struct.pack("<II", zlib.crc32(data), len(data) & 0xFFFFFFFF)

def mutate(rng, s):
    s = bytearray(s)
    k = rng.randrange(4)
    if k <= 1 and s:
        i = rng.randrange(len(s) * 8)
        s[i // 8] ^= 1 << (i % 8)
    elif k == 2 and s:
        del s[rng.randrange(len(s)):]
    else:
        s += os.urandom(rng.randrange(1, 10))
    return bytes(s)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=1000)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    srcs = [open(os.path.join(ROOT, "vdeflate/src", f), "rb").read() for f in sorted(os.listdir(os.path.join(ROOT, "vdeflate/src")))]
    tmp = tempfile.mkdtemp(prefix="wrapdiff")
    cases = []
    for i in range(a.n):
        src = rng.choice(srcs)
        data = src[: rng.randrange(0, len(src) + 1)] if rng.random() < 0.8 else os.urandom(rng.randrange(0, 3000))
        if rng.random() < 0.5:
            s = zlib.compress(data, rng.choice([0, 1, 6, 9]))
            fmt = "zlib"
        else:
            s = gzip_member(rng, data)
            fmt = "gzip"
        cases.append((fmt, s))
        for j in range(2):
            cases.append((fmt, mutate(rng, s)))
    lines = []
    for i, (fmt, s) in enumerate(cases):
        p = os.path.join(tmp, "%06d" % i)
        open(p, "wb").write(s)
        lines.append("%s %s" % (fmt, p))
    res = subprocess.run([TOOL, "--batch-wrap"], input="\n".join(lines) + "\n", capture_output=True, text=True, check=True).stdout.splitlines()
    stats, fails = {}, 0
    for (fmt, s), line in zip(cases, res):
        f = line.split()
        r = ref(fmt, s)
        if f[1] == "ok":
            st, n, used, h = int(f[2]), int(f[3]), int(f[4]), int(f[5], 16)
            if r is None:
                key = "ours ok, zlib refuses, flag off" if not st else "FAIL ours ok, zlib refuses"
            elif not st:
                key = "FAIL flag off, zlib accepts"
            elif fnv(r[0]) != h or len(r[0]) != n or r[1] != used:
                key = "FAIL different data or end"
            else:
                key = "both ok, same"
        else:
            key = "both refuse" if r is None else "FAIL ours refuses, zlib accepts"
        stats[(fmt, key)] = stats.get((fmt, key), 0) + 1
        fails += key.startswith("FAIL")
    for (fmt, key), n in sorted(stats.items()):
        print("%-4s %-36s %d" % (fmt, key, n))
    print("failures:", fails)
    sys.exit(1 if fails else 0)

if __name__ == "__main__":
    main()
