"""Single-threaded lossy WebP decode speed: each decoder behind its batch
protocol, the same frame K and 2K times; time per frame is the difference
over K (process start-up and file reading cancel), best of R. Output is
checked against libwebp's planes first."""
import os, struct, subprocess, sys, time, glob
HERE = os.path.dirname(os.path.abspath(__file__))
W = os.path.join(HERE, "..", "..", "difftest", "webp", "build")
B = os.environ.get("IMAGES", os.path.join(HERE, "images"))
DECS = [  # name, command, input (file or bare frame), output format
    ("vwebp verified, SSE2 (this work)", [os.environ.get("VW_BIN", os.path.join(HERE, "vbatch", "target", "release", "vbatch"))], "bare", "ours"),
        ("libwebp 1.6.0, SSE2", [W + "/ydec"], "file", "ydec"),
    ("libwebp 1.6.0, C only", [W + "/ydec-c"], "file", "ydec"),
    ("FFmpeg n9.0.2 vp8, x86 asm", [os.path.join(HERE, "ffydec-asm")], "bare", "ff"),
    ("FFmpeg n9.0.2 vp8, no asm", [W + "/ffydec"], "bare", "ff"),
    ("Wuffs std/vp8 f31d952", [W + "/wufydec"], "bare", "ff"),
    ("image-webp f4d80bd (Rust)", [W + "/iwh-target/release/iwhdec", "vp8"], "bare", "ff"),
    ("Go x/image v0.46.0", [W + "/godec", "vp8"], "bare", "ff"),
]
DECS = [d for d in DECS if os.path.exists(d[1][0])]  # the harnesses built here


def frame(path):
    d = open(path, "rb").read(); assert d[12:16] == b"VP8 "
    n = struct.unpack("<I", d[16:20])[0]; return d, d[20:20 + n]
def planes(out, fmt):
    i = 0
    st = out[0]; i = 1
    if fmt in ("ff", "ydec"): i += 4
    assert st == 1, (fmt, st)
    w, h = struct.unpack_from("<II", out, i); i += 8
    if fmt == "ydec": i += 1
    cw, ch = (w + 1) // 2, (h + 1) // 2
    return w * h, out[i:i + w * h + 2 * cw * ch]
import resource
def run(cmd, rec, k):
    # child CPU time (user + sys): steadier than wall time on a shared machine
    data = (struct.pack("<I", len(rec)) + rec) * k
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    subprocess.run(cmd, input=data, stdout=subprocess.DEVNULL, check=True)
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    return (r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime)
sets = {"kodak": sorted(glob.glob(B + "/kodak/*.webp")), "photos": sorted(glob.glob(B + "/photos/*.webp"))}
R = 5
ONLY = os.environ.get("ONLY")
if ONLY:
    DECS = [d for d in DECS if any(o in d[0] for o in ONLY.split(","))]
res = {}
for sname, files in sets.items():
    for f in files:
        whole, bare = frame(f)
        ref = None
        for name, cmd, kind, fmt in DECS:
            rec = whole if kind == "file" else bare
            out = subprocess.run(cmd, input=struct.pack("<I", len(rec)) + rec, stdout=subprocess.PIPE, check=True).stdout
            px, pl = planes(out, fmt)
            if ref is None: ref = pl
            same = pl == ref
            t1 = run(cmd, rec, 1)
            k = max(1, min(200, int(0.4 / max(t1, 1e-3))))
            best = min((run(cmd, rec, 2 * k) - run(cmd, rec, k)) / k for _ in range(R))
            res.setdefault((sname, name), []).append((px, best, same))
            print("%-10s %-24s %-34s %8.2f ms %s" % (sname, os.path.basename(f), name, best * 1e3, "" if same else "PLANES DIFFER"), flush=True)
print()
for sname in sets:
    base = None
    print("== %s" % sname)
    for name, *_ in DECS:
        r = res[(sname, name)]
        px = sum(p for p, _, _ in r); t = sum(x for _, x, _ in r)
        mps = px / t / 1e6
        if base is None: base = t
        print("%-36s %8.1f MP/s  %6.2fx vwebp-SSE2 time  %s" % (name, mps, t / base, "all identical" if all(s for *_, s in r) else "DIFFERENCES"))
