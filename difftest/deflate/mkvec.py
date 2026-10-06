#!/usr/bin/env python3
"""Freeze a small differential test into vdeflate/tests/data/vectors.txt, for
`cargo test -p vdeflate` on a fresh clone (no zlib build needed).

The streams are zdiff's (zlib's raw streams and mutants), wrapdiff's (zlib
and gzip) and edge.py's hand-built ones. Each is decoded by zlib (Python's)
and by vdeflate-tool, and kept only if the two agree as the suites require:
the same data and end where zlib decodes; where zlib refuses, vdeflate
refuses or decodes with its zlib flag off (edge.py's vectors: the RFC's
verdict). The expected result written is zlib's wherever zlib decodes.

    difftest/deflate/mkvec.py [-n N] [--seed S]

One line per stream: `FORMAT HEX bad` or `FORMAT HEX ok LEN FNV64 END FLAG`,
HEX `-` for an empty stream, END in bytes (a raw stream's bits rounded up), FLAG 1 when zlib decodes it.
"""
import argparse, os, random, subprocess, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zdiff, wrapdiff, edge

ROOT = zdiff.ROOT
TOOL = zdiff.TOOL
OUT = os.path.join(ROOT, "vdeflate/tests/data/vectors.txt")

def small_data(rng, srcs):
    d = zdiff.gen_data(rng, srcs)
    return d[: rng.randrange(0, 1500)] if len(d) > 1500 and rng.random() < 0.9 else d[:20000]

def run_tool(flag, lines):
    return subprocess.run([TOOL, flag], input="\n".join(lines) + "\n", capture_output=True,
                          text=True, check=True).stdout.splitlines()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=60)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    zdiff.os.urandom = wrapdiff.os.urandom = lambda n: bytes(rng.randrange(256) for _ in range(n))
    srcs = zdiff.corpus_sources(rng)
    cases = []  # (fmt, stream, rfc verdict or None)
    for name, rfc, zl, f in edge.VECS:
        w = edge.W(); f(w)
        cases.append(("raw", w.bytes(), rfc))
    for i in range(a.n):
        s = zdiff.compress(rng, small_data(rng, srcs))
        cases.append(("raw", s, None))
        for j in range(2):
            cases.append(("raw", zdiff.mutate(rng, s), None))
    for i in range(a.n):
        data = small_data(rng, srcs)
        if i % 2:
            fmt, s = "zlib", zdiff.zlib.compress(data, rng.choice([0, 1, 6, 9]))
        else:
            fmt, s = "gzip", wrapdiff.gzip_member(rng, data)
        cases.append((fmt, s, None))
        for j in range(2):
            cases.append((fmt, wrapdiff.mutate(rng, s), None))
    tmp = tempfile.mkdtemp(prefix="mkvec")
    raw, wrap = [], []
    for i, (fmt, s, _) in enumerate(cases):
        p = os.path.join(tmp, "%05d" % i)
        open(p, "wb").write(s)
        (raw if fmt == "raw" else wrap).append(p if fmt == "raw" else "%s %s" % (fmt, p))
    res = iter(run_tool("--batch", raw)), iter(run_tool("--batch-wrap", wrap))
    out, stats = [], {}
    for fmt, s, rfc in cases:
        hx = s.hex() or "-"
        f = next(res[0] if fmt == "raw" else res[1]).split()
        if fmt == "raw":
            r = zdiff.zlib_ref(s)
            ok = f[1] == "ok"
            if ok:
                st, n, end, h = int(f[2]), int(f[3]), (int(f[4]) + 7) // 8, int(f[5], 16)
        else:
            r = wrapdiff.ref(fmt, s)
            ok = f[1] == "ok"
            if ok:
                st, n, end, h = int(f[2]), int(f[3]), int(f[4]), int(f[5], 16)
        if r is not None:
            data, used = r
            if not ok or not st or n != len(data) or h != zdiff.fnv(data) or end != used:
                sys.exit("disagreement with zlib on %s %s: %s" % (fmt, s.hex(), " ".join(f)))
            line = "%s %s ok %d %016x %d 1" % (fmt, hx, len(data), zdiff.fnv(data), used)
        elif ok:
            if st:
                sys.exit("zlib flag on, zlib refuses: %s %s" % (fmt, s.hex()))
            line = "%s %s ok %d %016x %d 0" % (fmt, hx, n, h, end)
        else:
            line = "%s %s bad" % (fmt, hx)
        if rfc is not None and rfc != ("ok" if ok else "bad"):
            sys.exit("edge vector against the RFC: %s" % s.hex())
        k = (fmt, line.split()[2], line.split()[-1] if ok else "")
        stats[k] = stats.get(k, 0) + 1
        out.append(line)
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        fh.write("# difftest/deflate/mkvec.py -n %d --seed %d: FORMAT HEX bad | ok LEN FNV64 END ZLIB_FLAG\n" % (a.n, a.seed))
        fh.write("\n".join(out) + "\n")
    for k, v in sorted(stats.items()):
        print(" ".join(k), v)
    print("%d vectors, %d bytes -> %s" % (len(out), os.path.getsize(OUT), OUT))

if __name__ == "__main__":
    main()
