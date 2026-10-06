#!/usr/bin/env python3
"""vdeflate's compressor output, decoded by vdeflate, zlib, miniz_oxide and
libdeflate (bench/deflate's --verdicts): all four must give back the input.

Inputs are zdiff.py's kinds of data, compressed at level 6, at level 1, and
by the streaming compressor in pieces of up to 300 bytes.

    difftest/deflate/encall.py [-n N] [--seed S]
"""
import argparse, os, random, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zdiff

BENCH = os.path.join(zdiff.ROOT, "bench/deflate/target/release/deflate-bench")

def fnv(b):
    h = 0xcbf29ce484222325
    for x in b:
        h = ((h ^ x) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return h

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=1500)
    ap.add_argument("--seed", type=int, default=21)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    srcs = zdiff.corpus_sources(rng)
    d = tempfile.mkdtemp(prefix="encall")
    orig, paths = {}, []
    for i in range(a.n):
        x = zdiff.gen_data(rng, srcs)
        p = os.path.join(d, "%05d" % i)
        open(p, "wb").write(x)
        paths.append(p)
        orig[p] = fnv(x)
    files = []
    for tag, env in [("l6", {}), ("l1", {"VD_LEVEL": "1"}), ("st", {"VD_STREAM": "300"})]:
        subprocess.run([zdiff.TOOL, "--compress"], input="\n".join(paths) + "\n", text=True,
                       capture_output=True, check=True, env=dict(os.environ, **env))
        for p in paths:
            os.rename(p + ".vz", p + "." + tag)
            files.append((p + "." + tag, p))
    res = subprocess.run([BENCH, "--verdicts"], input="\n".join(q for q, _ in files) + "\n",
                         capture_output=True, text=True, check=True).stdout.splitlines()
    bad = 0
    for (q, p), line in zip(files, res):
        f = line.split()
        want = "ok:%x" % orig[p]
        ours = f[1].rsplit(":", 1)[0]
        if not (ours == want and f[2] == want and f[3] == want and f[4] == want):
            bad += 1
            print("MISMATCH", line, want)
    print("files %d, decoded to the input by all four: %d" % (len(files), len(files) - bad))
    print("failures:", bad)
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
