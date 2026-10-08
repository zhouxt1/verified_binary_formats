#!/usr/bin/env python3
"""vdeflate's compressors against the Lean spec's `Bridge.CompressesTo`.

`Bridge.verus_deflate_ok_eq` (lspec/Lspec/Bridge/VerusDeep.lean) says the compressors'
Verus contract `deflate_ok(data, o)` means `CompressesTo data o`: the bits of `o`, followed
by anything, decode by the Lean spec to `data`, with the zlib flag on, ending at a bit `q`
with (q + 7) / 8 = len(o). This runs the compressors and checks that with the Lean spec
itself (`lspec deflate --batch`), on `o` and on `o` followed by random bytes:

  * the verdict is `ok`, the flag is 1, the output is `data` (length and digest);
  * (bits + 7) // 8 == len(o);
  * `o` + junk gives exactly the same verdict line.

Levels 1, 6 and 9, the fixed-code compressor (VD_FIXED), the streaming one (VD_STREAM) and
near-optimal parsing (VD_OPT, `opt::deflate_opt`).
Inputs are zdiff.py's data.

    difftest/deflate/lspecenc.py [-n N] [--seed S]

Needs target/release/vdeflate-tool and lspec/.lake/build/bin/lspec.
"""
import argparse, os, random, subprocess, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zdiff

LS = [os.path.join(zdiff.ROOT, "lspec/.lake/build/bin/lspec"), "deflate", "--batch"]
MODES = [("L1", {"VD_LEVEL": "1"}), ("L6", {"VD_LEVEL": "6"}), ("L9", {"VD_LEVEL": "9"}),
         ("fixed", {"VD_FIXED": "1"}), ("stream", {"VD_STREAM": "300"}), ("opt", {"VD_OPT": "1"})]

def fnv(b):
    h = 0xcbf29ce484222325
    for x in b:
        h = ((h ^ x) * 0x100000001b3) & 0xffffffffffffffff
    return "%016x" % h

def lspec(paths):
    out = subprocess.run(LS, input="\n".join(paths) + "\n", capture_output=True, text=True,
                         check=True).stdout.splitlines()
    assert len(out) == len(paths)
    return [l.split(None, 1)[1] for l in out]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=200)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    srcs = zdiff.corpus_sources(rng)
    datas = [zdiff.gen_data(rng, srcs) for _ in range(a.n)]
    fails = total = 0
    for mode, env in MODES:
        tmp = tempfile.mkdtemp(prefix="lspecenc-" + mode)
        paths = []
        for i, d in enumerate(datas):
            p = os.path.join(tmp, "%06d" % i)
            open(p, "wb").write(d)
            paths.append(p)
        subprocess.run([zdiff.TOOL, "--compress"], env=dict(os.environ, **env),
                       input="\n".join(paths) + "\n", capture_output=True, text=True, check=True)
        outs, junk = [], []
        for p in paths:
            o = open(p + ".vz", "rb").read()
            outs.append(p + ".vz")
            j = p + ".junk"
            open(j, "wb").write(o + bytes(rng.randrange(256) for _ in range(rng.randrange(1, 17))))
            junk.append(j)
        v1, v2 = lspec(outs), lspec(junk)
        for d, o, r1, r2 in zip(datas, outs, v1, v2):
            total += 1
            olen = os.path.getsize(o)
            f = r1.split()
            ok = (len(f) == 5 and f[0] == "ok" and f[1] == "1" and int(f[2]) == len(d)
                  and f[4] == fnv(d) and (int(f[3]) + 7) // 8 == olen and r2 == r1)
            if not ok:
                fails += 1
                if fails <= 5:
                    print("FAIL %s %s: %r / with junk %r (input %d bytes, output %d)"
                          % (mode, o, r1, r2, len(d), olen))
        print("%-6s %d outputs checked" % (mode, len(datas)))
    print("outputs: %d, failures: %d" % (total, fails))
    return 1 if fails else 0

if __name__ == "__main__":
    sys.exit(main())
