#!/usr/bin/env python3
"""vdeflate's verdicts against zlib, miniz_oxide and libdeflate together.

Inputs: edge.py's vectors and zlib-made streams with their mutants (as in
zdiff.py). Each decoder either decodes (to an output hash) or refuses; the
table counts each pattern of verdicts, with vdeflate's split by its zlib
flag (z: zlib would accept, r: only the RFC reading does). A decoder that
decodes to different bytes from vdeflate is reported as such.

    difftest/deflate/odiff.py [-n N] [--seed S]
"""
import argparse, collections, os, random, subprocess, sys, tempfile, zlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zdiff

ROOT = zdiff.ROOT
BENCH = os.path.join(ROOT, "bench/deflate/target/release/deflate-bench")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=500)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    srcs = zdiff.corpus_sources(rng)
    tmp = tempfile.mkdtemp(prefix="odiff")
    paths = []
    subprocess.run([sys.executable, os.path.join(ROOT, "difftest/deflate/edge.py"), "--write", os.path.join(tmp, "edge")],
                   check=False, capture_output=True)
    edge = sorted(os.path.join(tmp, "edge", f) for f in os.listdir(os.path.join(tmp, "edge")))
    paths += edge
    for i in range(a.n):
        s = zdiff.compress(rng, zdiff.gen_data(rng, srcs))
        for j in range(4):
            m = zdiff.mutate(rng, s) if j else s
            p = os.path.join(tmp, "%06d-%d" % (i, j))
            open(p, "wb").write(m)
            paths.append(p)
    out = subprocess.run([BENCH, "--verdicts"], input="\n".join(paths) + "\n", capture_output=True, text=True, check=True).stdout
    pat = collections.Counter()
    ex = {}
    for line in out.splitlines():
        p, v, zl, mz, ld = line.split()
        vo = v.rsplit(":", 1)[0] if v.startswith("ok") else v
        flag = v.rsplit(":", 1)[1] if v.startswith("ok") else "-"
        def cmp(x):
            if x == "bad" or x == "big":
                return x
            return "same" if vo == x else "DIFFERENT"
        key = ("vdeflate " + ("ok/" + flag if v.startswith("ok") else "bad"), "zlib " + cmp(zl), "miniz_oxide " + cmp(mz), "libdeflate " + cmp(ld))
        pat[key] += 1
        ex.setdefault(key, p)
    for k, c in sorted(pat.items(), key=lambda x: -x[1]):
        e = ex[k]
        print("%6d  %-14s %-11s %-18s %-16s e.g. %s" % (c, k[0], k[1], k[2], k[3], os.path.basename(e) if "/edge/" not in e else "edge/" + os.path.basename(e)))

if __name__ == "__main__":
    main()
