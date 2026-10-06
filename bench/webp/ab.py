"""A/B of two decoders (name=path), robust to machine load: per image,
(a decoder whose file name starts with "ydec" is given the whole WebP
file, as libwebp's harness wants; the others the bare VP8 frame)
repeated paired runs in alternating order, child CPU time (user+sys) of K
frames, the per-image median ratio B/A; reported: the geometric mean of
those ratios (B faster if > 1) and each one's best MP/s."""
import glob, math, os, resource, statistics, struct, subprocess, sys, time
B = os.environ.get("IMAGES", os.path.join(os.path.dirname(os.path.abspath(__file__)), "images"))
(na, ca), (nb, cb) = [a.split("=", 1) for a in sys.argv[1:3]]
files = sorted(glob.glob(B + "/photos/*.webp")) + sorted(glob.glob(B + "/kodak/*.webp"))[:6]
def rec(f, cmd):
    d = open(f, "rb").read(); n = struct.unpack("<I", d[16:20])[0]; x = d[20:20 + n]
    if os.path.basename(cmd).startswith("ydec"): x = d
    return struct.pack("<I", len(x)) + x
def cpu(cmd, data):
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    subprocess.run([cmd], input=data, stdout=subprocess.DEVNULL, check=True)
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    return (r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime)
logs = []; best = {na: 0.0, nb: 0.0}; px = 0
for f in files:
    ra, rb = rec(f, ca), rec(f, cb); b = rec(f, "")[4:]
    p = (struct.unpack("<H", b[6:8])[0] & 0x3fff) * (struct.unpack("<H", b[8:10])[0] & 0x3fff); px += p
    t1 = cpu(ca, ra); k = max(2, min(200, int(0.4 / max(t1, 1e-3))))
    data = {ca: ra * k, cb: rb * k}
    ratios = []; bt = {na: 1e9, nb: 1e9}
    for rep in range(8):
        order = [(na, ca), (nb, cb)] if rep % 2 == 0 else [(nb, cb), (na, ca)]
        t = {n: cpu(c, data[c]) / k for n, c in order}
        ratios.append(t[na] / t[nb]); bt[na] = min(bt[na], t[na]); bt[nb] = min(bt[nb], t[nb])
    logs.append(math.log(statistics.median(ratios)))
    best[na] += bt[na]; best[nb] += bt[nb]
print("%s vs %s: %s is %.3fx as fast (geomean of per-image medians); best %s %.1f MP/s, %s %.1f MP/s"
      % (nb, na, nb, math.exp(sum(logs) / len(logs)), na, px / best[na] / 1e6, nb, px / best[nb] / 1e6))
