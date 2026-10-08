#!/usr/bin/env python3
"""Differential test of vdeflate against zlib (Python's, 1.3).

Streams come from zlib itself (every level, strategy, window and memory
level, over text, binary and random data, with flushes that make stored and
empty blocks), and from bit-flipping, truncating and extending them. For
each stream, both decoders must agree:

  * zlib decodes it (to the end of a final block)  <=>  vdeflate decodes it
    and says zlib accepts it;
  * when both decode, the outputs are equal and vdeflate stops where zlib
    does (zlib's unused_data is what follows vdeflate's bit count, rounded
    up to a byte).

A stream vdeflate decodes with the flag off must be one zlib refuses.

    difftest/deflate/zdiff.py [-n N] [--seed S]
"""
import argparse, os, random, subprocess, sys, tempfile, zlib

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TOOL = os.path.join(ROOT, "target/release/vdeflate-tool")
LSPEC = os.path.join(ROOT, "lspec/.lake/build/bin/lspec")

def lspec_wrap(lines):
    """The Lean spec (lspec/Lspec/Deflate/Wrap.lean) on `vdeflate-tool --batch-wrap`
    input lines; its output lines, in the same format."""
    return subprocess.run([LSPEC, "wrap", "--batch"], input="".join(l + "\n" for l in lines),
                          capture_output=True, text=True, check=True).stdout.splitlines()

def lean_vs_vdeflate(lines, vd):
    """Compare the Lean spec with vdeflate on the same input: (agreeing, failures)."""
    same, fails = 0, 0
    for line, v, l in zip(lines, vd, lspec_wrap(lines)):
        if l == v:
            same += 1
        else:
            fails += 1
            print("FAIL lean != vdeflate:", line, "| vdeflate:", v, "| lean:", l)
    return same, fails

def fnv(b):
    h = 0xcbf29ce484222325
    for x in b:
        h ^= x
        h = (h * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return h

def zlib_ref(s):
    d = zlib.decompressobj(-15)
    try:
        out = d.decompress(s, 1 << 28)
    except zlib.error as e:
        return None
    if not d.eof or d.unconsumed_tail:
        return None
    return out, len(s) - len(d.unused_data)

def corpus_sources(rng):
    srcs = []
    for dirpath, _, files in os.walk(os.path.join(ROOT, "docs")):
        for f in files:
            p = os.path.join(dirpath, f)
            try:
                if os.path.getsize(p) < 4 << 20:
                    srcs.append(open(p, "rb").read())
            except OSError:
                pass
    for d in ("vdeflate/src", "vbrotli/src", "vwebp/src", "vh26x/src"):
        for f in sorted(os.listdir(os.path.join(ROOT, d))):
            p = os.path.join(ROOT, d, f)
            if os.path.isfile(p):
                srcs.append(open(p, "rb").read())
    return srcs

def gen_data(rng, srcs):
    k = rng.randrange(8)
    if k == 0:
        return os.urandom(rng.randrange(0, 5000))
    if k == 1:
        return bytes([rng.randrange(4)]) * rng.randrange(0, 70000)
    if k == 2:
        n = rng.randrange(1, 300)
        return bytes(rng.choice(b"ab") for _ in range(n)) * rng.randrange(1, 50)
    if k == 3:
        return b""
    s = rng.choice(srcs)
    a = rng.randrange(0, max(1, len(s)))
    return s[a:a + rng.randrange(0, 200000)]

def compress(rng, data):
    level = rng.choice([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, -1])
    strategy = rng.choice([zlib.Z_DEFAULT_STRATEGY, zlib.Z_FILTERED, zlib.Z_HUFFMAN_ONLY,
                           zlib.Z_RLE, zlib.Z_FIXED])
    wbits = -rng.randrange(9, 16)
    mem = rng.randrange(1, 10)
    c = zlib.compressobj(level, zlib.DEFLATED, wbits, mem, strategy)
    out = b""
    pos = 0
    while pos < len(data):
        n = rng.randrange(1, 70000)
        out += c.compress(data[pos:pos + n])
        pos += n
        r = rng.randrange(6)
        if r == 0:
            out += c.flush(zlib.Z_SYNC_FLUSH)
        elif r == 1:
            out += c.flush(zlib.Z_FULL_FLUSH)
    out += c.flush(zlib.Z_FINISH)
    return out

def mutate(rng, s):
    s = bytearray(s)
    k = rng.randrange(5)
    if k <= 1 and s:
        for _ in range(rng.randrange(1, 4)):
            i = rng.randrange(len(s) * 8)
            s[i // 8] ^= 1 << (i % 8)
    elif k == 2 and s:
        del s[rng.randrange(len(s)):]
    elif k == 3:
        s += os.urandom(rng.randrange(1, 10))
    elif s:
        i = rng.randrange(len(s))
        s[i] = rng.randrange(256)
    return bytes(s)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--keep", default=None, help="directory to keep failing streams in")
    ap.add_argument("--stream", action="store_true", help="also decode each stream in random pieces")
    a = ap.parse_args()
    rng = random.Random(a.seed)
    srcs = corpus_sources(rng)
    tmp = tempfile.mkdtemp(prefix="zdiff")
    cases = []
    for i in range(a.n):
        data = gen_data(rng, srcs)
        s = compress(rng, data)
        cases.append(("gen", s, data))
        for j in range(3):
            cases.append(("mut", mutate(rng, s), None))
    paths = []
    for i, (kind, s, _) in enumerate(cases):
        p = os.path.join(tmp, "%06d.bin" % i)
        open(p, "wb").write(s)
        paths.append(p)
    res = subprocess.run([TOOL, "--batch"], input="\n".join(paths) + "\n", capture_output=True,
                         text=True, check=True).stdout.splitlines()
    assert len(res) == len(paths)
    stats = {}
    fails = 0
    for (kind, s, data), line in zip(cases, res):
        f = line.split()
        ours = f[1]
        ref = zlib_ref(s)
        key = None
        if ours == "ok":
            st, olen, bits, h = int(f[2]), int(f[3]), int(f[4]), int(f[5], 16)
            if ref is None:
                key = "ours ok, zlib refuses, flag off" if not st else "FAIL ours ok+flag, zlib refuses"
            else:
                out, used = ref
                if not st:
                    key = "FAIL flag off but zlib accepts"
                elif fnv(out) != h or len(out) != olen:
                    key = "FAIL outputs differ"
                elif (bits + 7) // 8 != used:
                    key = "FAIL stop position differs"
                else:
                    key = "both ok, same"
            if kind == "gen" and ours == "ok" and data is not None and (fnv(data) != h):
                key = "FAIL round trip"
        elif ours == "bad":
            key = "both refuse" if ref is None else "FAIL ours refuses, zlib accepts"
        else:
            key = "FAIL toobig"
        k2 = (kind, key)
        stats[k2] = stats.get(k2, 0) + 1
        if key.startswith("FAIL"):
            fails += 1
            if a.keep:
                os.makedirs(a.keep, exist_ok=True)
                open(os.path.join(a.keep, "%s-%d.bin" % (kind, fails)), "wb").write(s)
    if a.stream:
        out = subprocess.run([TOOL, "--batch-stream"], input="\n".join(paths) + "\n", capture_output=True,
                             text=True, check=True).stdout.splitlines()
        for l in out:
            if l.startswith("MISMATCH"):
                print(l)
                fails += 1
        print(out[-1])
    for (kind, key), n in sorted(stats.items()):
        print("%-4s %-40s %d" % (kind, key, n))
    print("failures:", fails)
    sys.exit(1 if fails else 0)

if __name__ == "__main__":
    main()
