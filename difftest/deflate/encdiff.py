#!/usr/bin/env python3
"""vdeflate's compressor: its output must decode, by zlib, to the input.

The inputs are zdiff.py's data: text, binary, random, runs, empty. The
round trip through vdeflate's own decoder is a theorem; this checks the
spec's agreement with zlib on what the compressor writes, and reports the
size against zlib -1 and -6. With --wrap zlib or gzip, the compressor's
zlib or gzip output, decoded by zlib's zlib or gzip decoder (which checks
the trailer).

    difftest/deflate/encdiff.py [-n N] [--seed S] [--wrap raw|zlib|gzip]
"""
import argparse, os, random, subprocess, sys, tempfile, zlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zdiff

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=500)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--wrap", choices=["raw", "zlib", "gzip"], default="raw")
    a = ap.parse_args()
    rng = random.Random(a.seed)
    srcs = zdiff.corpus_sources(rng)
    tmp = tempfile.mkdtemp(prefix="encdiff")
    paths, datas = [], []
    for i in range(a.n):
        d = zdiff.gen_data(rng, srcs)
        p = os.path.join(tmp, "%06d" % i)
        open(p, "wb").write(d)
        paths.append(p); datas.append(d)
    env = dict(os.environ, VD_WRAP=a.wrap)
    wbits = {"raw": -15, "zlib": 15, "gzip": 31}[a.wrap]
    out = subprocess.run([zdiff.TOOL, "--compress"], env=env, input="\n".join(paths) + "\n", capture_output=True, text=True, check=True).stdout.splitlines()
    fails = 0
    tot = [0, 0, 0, 0]
    for p, d, line in zip(paths, datas, out):
        c = open(p + ".vz", "rb").read()
        try:
            dec = zlib.decompressobj(wbits)
            o = dec.decompress(c)
            ok = dec.eof and o == d and dec.unused_data == b""
        except zlib.error:
            ok = False
        if not ok:
            fails += 1
            print("FAIL", p)
        tot[0] += len(d); tot[1] += len(c)
        z1 = zlib.compressobj(1, zlib.DEFLATED, -15); tot[2] += len(z1.compress(d) + z1.flush())
        z6 = zlib.compressobj(6, zlib.DEFLATED, -15); tot[3] += len(z6.compress(d) + z6.flush())
    print("inputs %d, %d bytes: vdeflate %d, zlib -1 %d, zlib -6 %d" % (a.n, tot[0], tot[1], tot[2], tot[3]))
    print("failures:", fails)
    sys.exit(1 if fails else 0)

if __name__ == "__main__":
    main()
