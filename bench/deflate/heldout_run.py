#!/usr/bin/env python3
"""Run the held-out evaluation (HELDOUT.md): every compressor on every file of
SETS_DIR, raw DEFLATE sizes, decoding checks, a summary per set.

    heldout_run.py SETS_DIR WORK_DIR ZOPFLI OUT.json
"""
import concurrent.futures as cf, json, os, shutil, statistics, subprocess, sys, time, zlib

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TOOL = os.path.join(ROOT, "target/release/vdeflate-tool")
BENCH = os.path.join(ROOT, "bench/deflate/target/release/deflate-bench")
LSPEC = os.path.join(ROOT, "lspec/.lake/build/bin/lspec")

def fnv(b):
    h = 0xcbf29ce484222325
    for x in b:
        h = ((h ^ x) * 0x100000001b3) & 0xffffffffffffffff
    return "%016x" % h

def vd(paths, env):
    t = time.time()
    subprocess.run([TOOL, "--compress"], env=dict(os.environ, **env), input="\n".join(paths) + "\n",
                   capture_output=True, text=True, check=True)
    return time.time() - t

def main():
    sets_dir, work, zop, out = sys.argv[1:5]
    res = {}
    for s in sorted(os.listdir(sets_dir)):
        files = sorted(os.listdir(os.path.join(sets_dir, s)))
        src = {f: os.path.join(sets_dir, s, f) for f in files}
        r = {f: {"bytes": os.path.getsize(src[f])} for f in files}
        secs = {}
        for tag, env in (("opt", {"VD_OPT": "1"}), ("vd9", {"VD_LEVEL": "9"})):
            d = os.path.join(work, s, tag); os.makedirs(d, exist_ok=True)
            paths = []
            for f in files:
                p = os.path.join(d, f)
                if not os.path.exists(p): shutil.copyfile(src[f], p)
                paths.append(p)
            secs[tag] = vd(paths, env)
            for f, p in zip(files, paths):
                r[f][tag] = os.path.getsize(p + ".vz")
        o = subprocess.run([BENCH, "--ld-compress", "12"] + [src[f] for f in files], capture_output=True,
                           text=True, check=True).stdout.split("\n")
        for line in o:
            if line.strip():
                p, n, _ = line.split(); r[os.path.basename(p)]["ld12"] = int(n)
        for f in files:
            c = zlib.compressobj(9, zlib.DEFLATED, -15, 9)
            r[f]["zl9"] = len(c.compress(open(src[f], "rb").read()) + c.flush())
        def zrun(f):
            return f, len(subprocess.run([zop, "--deflate", "-c", src[f]], capture_output=True, check=True).stdout)
        t = time.time()
        with cf.ThreadPoolExecutor(64) as ex:
            for f, n in ex.map(zrun, files):
                r[f]["zopfli"] = n
        secs["zopfli_parallel"] = time.time() - t
        # checks: zlib decodes every deflate_opt output; the Lean spec checks CompressesTo
        bad = []
        for f in files:
            d = open(src[f], "rb").read()
            c = open(os.path.join(work, s, "opt", f + ".vz"), "rb").read()
            if zlib.decompress(c, -15) != d: bad.append(f)
        lean_bad = None
        if s != "enwik8":
            outs = [os.path.join(work, s, "opt", f + ".vz") for f in files]
            v = subprocess.run([LSPEC, "deflate", "--batch"], input="\n".join(outs) + "\n", capture_output=True,
                               text=True, check=True).stdout.splitlines()
            lean_bad = []
            for f, line in zip(files, v):
                x = line.split()[1:]
                d = open(src[f], "rb").read(); n = r[f]["opt"]
                ok = (len(x) == 5 and x[0] == "ok" and x[1] == "1" and int(x[2]) == len(d) and x[4] == fnv(d)
                      and (int(x[3]) + 7) // 8 == n)
                if not ok: lean_bad.append(f)
        res[s] = {"files": r, "secs": secs, "zlib_bad": bad, "lean_bad": lean_bad}
        json.dump(res, open(out, "w"), indent=1)
        summary(s, res[s])

def summary(s, x):
    r = x["files"]; fs = list(r)
    tot = {k: sum(r[f][k] for f in fs) for k in ("bytes", "opt", "vd9", "ld12", "zl9", "zopfli")}
    print("== %s: %d files, %d bytes; opt %.1f s, zopfli %.1f s (parallel); zlib-decode failures %d, Lean-spec failures %s"
          % (s, len(fs), tot["bytes"], x["secs"]["opt"], x["secs"]["zopfli_parallel"], len(x["zlib_bad"]),
             "n/a" if x["lean_bad"] is None else len(x["lean_bad"])))
    for k in ("vd9", "zl9", "ld12", "zopfli"):
        w = sum(r[f]["opt"] < r[f][k] for f in fs); l = sum(r[f]["opt"] > r[f][k] for f in fs)
        med = statistics.median(r[f]["opt"] / r[f][k] for f in fs)
        print("   opt vs %-6s total %+.3f%%   files won %d / tied %d / lost %d   median ratio %.4f"
              % (k, 100 * (tot["opt"] / tot[k] - 1), w, len(fs) - w - l, l, med))

if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--summary":
        for s, x in json.load(open(sys.argv[2])).items(): summary(s, x)
    else:
        main()
