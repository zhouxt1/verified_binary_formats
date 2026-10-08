#!/usr/bin/env python3
"""gzip files of several members (as pigz, or `cat a.gz b.gz`, make them),
and their mutants, against zlib reading member after member (as gzip -d
does): vdeflate's `inflate_gzip_file` must give the same data, or refuse
exactly when zlib does. (Not against Python's gzip.decompress: it accepts
reserved FLG bits, which RFC 1952 2.3.1.2 says a decoder must refuse, and
zlib and gzip -d do.)

    difftest/deflate/gzmulti.py [-n N] [--seed S]
"""
import argparse, gzip, os, random, subprocess, sys, tempfile, zlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zdiff

def fnv(b):
    h = 0xcbf29ce484222325
    for x in b:
        h = ((h ^ x) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return h

def members(s):
    """zlib's reading of a gzip file: members to the end, or None."""
    if not s:
        return None
    out = b""
    while s:
        d = zlib.decompressobj(31)
        try:
            out += d.decompress(s)
        except zlib.error:
            return None
        if not d.eof:
            return None
        s = d.unused_data
    return out

def member(rng, d):
    lv = rng.choice([0, 1, 6, 9])
    return gzip.compress(d, compresslevel=lv, mtime=0)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=1000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--lspec", action="store_true", help="also the Lean spec, which must print what vdeflate prints")
    a = ap.parse_args()
    rng = random.Random(a.seed)
    srcs = zdiff.corpus_sources(rng)
    d = tempfile.mkdtemp(prefix="gzmulti")
    cases = []
    for i in range(a.n):
        k = rng.choice([1, 1, 2, 3, 5])
        s = b"".join(member(rng, zdiff.gen_data(rng, srcs)[:20000]) for _ in range(k))
        r = rng.random()
        if r < 0.15:
            s = s[:rng.randrange(len(s) + 1)]
        elif r < 0.3 and s:
            j = rng.randrange(len(s))
            s = s[:j] + bytes([s[j] ^ (1 << rng.randrange(8))]) + s[j + 1:]
        elif r < 0.35:
            s = s + bytes(rng.randrange(256) for _ in range(rng.randrange(1, 20)))
        p = os.path.join(d, "%05d.gz" % i)
        open(p, "wb").write(s)
        cases.append((p, s))
    out = subprocess.run([zdiff.TOOL, "--batch-wrap"], input="".join("gzipfile %s\n" % p for p, _ in cases),
                         capture_output=True, text=True, check=True).stdout.splitlines()
    fails = 0
    agree = {"ok": 0, "bad": 0}
    for (p, s), line in zip(cases, out):
        ref = members(s)
        f = line.split()
        if ref is None:
            ok = f[1] == "bad"
            agree["bad"] += ok
        else:
            ok = f[1] == "ok" and int(f[2]) == len(ref) and f[3] == "%016x" % fnv(ref)
            agree["ok"] += ok
        if not ok:
            fails += 1
            print("FAIL", p, line, "python:", None if ref is None else len(ref))
    print("files %d: both decode %d, both refuse %d" % (len(cases), agree["ok"], agree["bad"]))
    if a.lspec:
        lines = ["gzipfile %s" % p for p, _ in cases]
        same, lf = zdiff.lean_vs_vdeflate(lines, out)
        print("lean == vdeflate %d of %d" % (same, len(lines)))
        fails += lf
    print("failures:", fails)
    sys.exit(1 if fails else 0)

if __name__ == "__main__":
    main()
