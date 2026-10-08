#!/usr/bin/env python3
"""The Lean spec of RFC 1951 (lspec/Lspec/Deflate/Spec.lean), run, against
vdeflate's verified decoder and zlib.

vdeflate's decoder is proved to compute its Verus spec (vdeflate/src/spec.rs),
so where the two agree here, the Lean spec and the Verus spec agree. The
checks:

  * Lean spec == vdeflate, on every stream: the same verdict, zlib flag,
    output length, bit count and output digest;
  * Lean spec against zlib, by zdiff.py's rules (zlib decodes the stream
    <=> the spec decodes it with the flag on; equal outputs; zlib stops at
    the spec's bit count rounded up to a byte);
  * edge.py's hand-built vectors: the spec gives each its RFC verdict, and
    its flag is zlib's verdict.

Streams are zdiff.py's (zlib's own output at every setting, and bit-flipped,
truncated and extended mutants) and edge.py's.

    difftest/deflate/lspecdiff.py [-n N] [--seed S] [--leanzip TOOL]

With --leanzip, also lean-zip's spec decoder (`Deflate.Spec.decode`, by
kim-em/lean-zip, written independently from the RFC; TOOL is a driver that
prints `PATH ok LEN BITS FNV` or `PATH bad`, see lspec/README.md), with the
fix for kim-em/lean-zip#2586. Every stream lean-zip decodes the Lean spec must
decode the same, and every stream the Lean spec decodes with the zlib flag on
must decode the same there (`LeanZipEq.inflate_of_decodesTo`,
`decodesTo_of_inflate`). lean-zip may refuse a stream the Lean spec decodes with
the flag off: it rejects HDIST 30 and 31, as zlib does.

Needs target/release/vdeflate-tool and lspec/.lake/build/bin/lspec (`lake
build` in lspec/).
"""
import argparse, os, random, subprocess, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import edge, zdiff

ROOT = zdiff.ROOT
VD = [os.path.join(ROOT, "target/release/vdeflate-tool"), "--batch"]
LS = [os.path.join(ROOT, "lspec/.lake/build/bin/lspec"), "deflate", "--batch"]

def batch(cmd, paths):
    out = subprocess.run(cmd, input="\n".join(paths) + "\n", capture_output=True, text=True,
                         check=True).stdout.splitlines()
    assert len(out) == len(paths)
    return [l.split(None, 1)[1] for l in out]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=500)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--keep", default=None, help="directory to keep failing streams in")
    ap.add_argument("--leanzip", default=None, help="lean-zip spec decoder driver")
    ap.add_argument("--leanzip-max", type=int, default=20000,
                    help="only give lean-zip streams vdeflate decodes to at most this many bytes, "
                         "or refuses (its List-based spec is quadratic)")
    a = ap.parse_args()
    rng = random.Random(a.seed)
    srcs = zdiff.corpus_sources(rng)
    cases = []
    for name, rfc, zl, f in edge.VECS:
        w = edge.W(); f(w)
        cases.append(("edge", w.bytes(), (name, rfc, zl)))
    for i in range(a.n):
        s = zdiff.compress(rng, zdiff.gen_data(rng, srcs))
        cases.append(("gen", s, None))
        for j in range(3):
            cases.append(("mut", zdiff.mutate(rng, s), None))
    tmp = tempfile.mkdtemp(prefix="lspecdiff")
    paths = []
    for i, (_, s, _) in enumerate(cases):
        p = os.path.join(tmp, "%06d.bin" % i)
        open(p, "wb").write(s)
        paths.append(p)
    vd = batch(VD, paths)
    ls = batch(LS, paths)
    lz = [None] * len(paths)
    if a.leanzip:
        small = [i for i, v in enumerate(vd)
                 if not v.startswith("ok") or int(v.split()[2]) <= a.leanzip_max]
        for i, z in zip(small, batch([a.leanzip], [paths[i] for i in small])):
            lz[i] = z
    stats, fails = {}, 0
    for (kind, s, info), v, l, z in zip(cases, vd, ls, lz):
        keys = []
        if z is not None:
            lf = l.split()
            ours = " ".join(lf[:1] + lf[2:]) if lf[0] == "ok" else "bad"
            if z == ours:
                keys.append("lean-zip == lean")
            elif lf[0] == "ok" and lf[1] == "0" and z == "bad":
                keys.append("lean-zip refuses, lean decodes with the flag off")
                print("lean-zip refuses: %s %s" % (kind, info[0] if info else ""))
            else:
                keys.append("FAIL lean-zip differs: " + z)
        keys.append("lean == vdeflate" if l == v else "FAIL lean != vdeflate")
        f = l.split()
        ref = zdiff.zlib_ref(s)
        if f[0] == "ok":
            st, olen, bits, h = int(f[1]), int(f[2]), int(f[3]), int(f[4], 16)
            if ref is None:
                keys.append("lean ok, zlib refuses, flag off" if not st
                            else "FAIL lean ok+flag, zlib refuses")
            else:
                out, used = ref
                if not st:
                    keys.append("FAIL flag off but zlib accepts")
                elif zdiff.fnv(out) != h or len(out) != olen:
                    keys.append("FAIL outputs differ from zlib")
                elif (bits + 7) // 8 != used:
                    keys.append("FAIL stop position differs from zlib")
                else:
                    keys.append("both ok, same")
        else:
            keys.append("both refuse" if ref is None else "FAIL lean refuses, zlib accepts")
        if kind == "edge":
            name, rfc, zl = info
            flag = ("ok" if f[1] == "1" else "bad") if f[0] == "ok" else "bad"
            if f[0] != rfc or flag != zl:
                keys.append("FAIL edge vector: " + name)
                print("edge %r: rfc %s zlib %s, lean %s" % (name, rfc, zl, l))
        for k in keys:
            stats[(kind, k)] = stats.get((kind, k), 0) + 1
        if any(k.startswith("FAIL") for k in keys):
            fails += 1
            print("FAIL %s: lean %r vdeflate %r" % (kind, l, v))
            if a.keep:
                os.makedirs(a.keep, exist_ok=True)
                open(os.path.join(a.keep, "%s-%d.bin" % (kind, fails)), "wb").write(s)
    for (kind, key), n in sorted(stats.items()):
        print("%-4s %-40s %d" % (kind, key, n))
    print("failures:", fails)
    sys.exit(1 if fails else 0)

if __name__ == "__main__":
    main()
