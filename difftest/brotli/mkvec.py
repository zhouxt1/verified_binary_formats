#!/usr/bin/env python3
"""Freeze a small differential test into vbrotli/tests/data/vectors.txt, for
`cargo test -p vbrotli` on a fresh clone (no Google decoder to build).

The streams are Google's test vectors (the small ones), edge.py's hand-built
streams and bdiff.py's (Google's encoder on small data, and mutants). Each
is decoded by Google's decoder (build/gdec, from build.sh) and by the
verified decoder (vbrotli-tool batch), and kept only if the two agree as
bdiff.py requires: the same data and end where Google decodes; where it
refuses, vbrotli refuses or decodes with its Google flag off. The expected
result written is Google's wherever Google decodes.

    difftest/brotli/mkvec.py [-n N] [--seed S]

One line per stream: `NAME HEX bad` or `NAME HEX ok LEN FNV64 END FLAG`, HEX
`-` for an empty stream, END in bytes, FLAG 1 when Google decodes it.
"""
import argparse, glob, os, random, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bdiff, edge

OUT = os.path.join(bdiff.ROOT, "vbrotli/tests/data/vectors.txt")
TESTDATA = os.path.join(bdiff.HERE, "build/brotli/tests/testdata")

def fnv(b):
    h = 0xcbf29ce484222325
    for x in b:
        h = ((h ^ x) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return h

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=80)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    r = random.Random(a.seed)
    cases = []
    for f in sorted(glob.glob(os.path.join(TESTDATA, "*.compressed*"))):
        if os.path.getsize(f) <= 12000:
            cases.append(("google:" + os.path.basename(f), open(f, "rb").read()))
    for i, (name, data, valid, out) in enumerate(edge.cases()):
        cases.append(("edge:%d" % i, data))
    files = bdiff.corpus_files()
    for i in range(a.n):
        data = bdiff.gen_data(r, files)[: r.choice([0, 10, 300, 3000, 20000])]
        s, kw = bdiff.compress(r, data)
        cases.append(("enc:q%d,w%d" % (kw["quality"], kw["lgwin"]), s))
        for j in range(2):
            cases.append(("mut", bdiff.mutate(r, s)))
    g = bdiff.Proc([bdiff.GDEC], "g")
    t = bdiff.Proc([bdiff.TOOL, "batch"], "t")
    out, stats = [], {}
    for name, s in cases:
        status, code, used, gout = g.run(s)
        tr = t.run(s)
        hx = s.hex() or "-"
        if status == 1:
            if tr is None or not tr[1] or tr[0] != 8 * used or tr[2] != gout:
                sys.exit("disagreement with Google on %s %s" % (name, hx))
            line = "%s %s ok %d %016x %d 1" % (name, hx, len(gout), fnv(gout), used)
        elif tr is not None:
            bits, google, data = tr
            if google:
                sys.exit("Google flag on, Google refuses: %s %s" % (name, hx))
            line = "%s %s ok %d %016x %d 0" % (name, hx, len(data), fnv(data), bits // 8)
        else:
            line = "%s %s bad" % (name, hx)
        f = line.split()
        k = (name.split(":")[0], f[2], f[-1] if f[2] == "ok" else "")
        stats[k] = stats.get(k, 0) + 1
        out.append(line)
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        fh.write("# difftest/brotli/mkvec.py -n %d --seed %d: NAME HEX bad | ok LEN FNV64 END GOOGLE_FLAG\n" % (a.n, a.seed))
        fh.write("\n".join(out) + "\n")
    for k, v in sorted(stats.items()):
        print(" ".join(k), v)
    print("%d vectors, %d bytes -> %s" % (len(out), os.path.getsize(OUT), OUT))

if __name__ == "__main__":
    main()
