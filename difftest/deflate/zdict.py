#!/usr/bin/env python3
"""zlib streams with a preset dictionary (FDICT), made by zlib with zdict=,
and their mutants, against zlib's decompressobj(zdict=): vdeflate's
`inflate_zlib_dict` must give the same data and end, or refuse exactly when
zlib does. Some are decoded with the wrong dictionary (DICTID must refuse
them), some are ordinary streams (the dictionary is not used).

    difftest/deflate/zdict.py [-n N] [--seed S]
"""
import argparse, os, random, subprocess, sys, tempfile, zlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zdiff

def fnv(b):
    h = 0xcbf29ce484222325
    for x in b:
        h = ((h ^ x) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return h

def ref(s, dct):
    try:
        d = zlib.decompressobj(15, zdict=dct) if dct else zlib.decompressobj(15)
        o = d.decompress(s)
    except (zlib.error, ValueError):
        return None
    if not d.eof:
        return None
    return o, len(s) - len(d.unused_data)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    srcs = zdiff.corpus_sources(rng)
    d = tempfile.mkdtemp(prefix="zdict")
    cases = []
    for i in range(a.n):
        data = zdiff.gen_data(rng, srcs)[:50000]
        dct = zdiff.gen_data(rng, srcs)[:rng.choice([1, 100, 5000, 40000])] or b"x"
        if rng.random() < 0.3 and len(data) > 10:
            dct = data[rng.randrange(len(data) // 2):][:rng.randrange(1, 40000)] or b"x"  # a dictionary that helps
        use = rng.random() < 0.85
        c = zlib.compressobj(rng.choice([1, 6, 9]), zlib.DEFLATED, 15, zdict=dct) if use else zlib.compressobj(6)
        s = c.compress(data) + c.flush()
        r = rng.random()
        if r < 0.1:
            s = s[:rng.randrange(len(s) + 1)]
        elif r < 0.25 and s:
            j = rng.randrange(len(s))
            s = s[:j] + bytes([s[j] ^ (1 << rng.randrange(8))]) + s[j + 1:]
        elif r < 0.3:
            s = s + os.urandom(rng.randrange(1, 10))
        given = dct if rng.random() < 0.9 else dct[:-1] + bytes([dct[-1] ^ 1])
        p = os.path.join(d, "%05d" % i)
        open(p, "wb").write(s)
        open(p + ".dict", "wb").write(given)
        cases.append((p, s, given))
    out = subprocess.run([zdiff.TOOL, "--batch-wrap"], input="".join("zlibdict %s %s.dict\n" % (p, p) for p, _, _ in cases),
                         capture_output=True, text=True, check=True).stdout.splitlines()
    fails = 0
    both_ok = both_bad = 0
    for (p, s, dct), line in zip(cases, out):
        rr = ref(s, dct)
        f = line.split()
        if rr is None:
            ok = f[1] == "bad"
            both_bad += ok
        else:
            o, n = rr
            ok = f[1] == "ok" and int(f[3]) == len(o) and int(f[4]) == n and f[5] == "%016x" % fnv(o)
            both_ok += ok
        if not ok:
            fails += 1
            print("FAIL", p, line, None if rr is None else (len(rr[0]), rr[1]))
    print("streams %d: both decode %d, both refuse %d" % (len(cases), both_ok, both_bad))
    print("failures:", fails)
    sys.exit(1 if fails else 0)

if __name__ == "__main__":
    main()
