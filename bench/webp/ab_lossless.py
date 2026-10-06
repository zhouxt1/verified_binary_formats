"""A/B of two lossless decoders (name=path), each behind the batch protocol
of difftest/webp (lbatch/ for vwebp, difftest/webp/build/wdec for libwebp),
on the images of get_lossless.sh (whole .webp files): photos, Kodak and
synthetic graphics. First every image's
pixels are compared between the two (a difference stops the run). Then, as
ab.py: per image, repeated paired runs in alternating order, child CPU time
(user+sys) of K decodes, the per-image median ratio A/B; reported: the
geometric mean of those ratios (B faster if > 1), per set, and each one's
best MP/s. KODAK=n takes the first n Kodak images (default 8; 24 for all),
REPS the paired runs per image (default 8)."""
import glob, math, os, resource, statistics, struct, subprocess, sys
B = os.environ.get("IMAGES", os.path.join(os.path.dirname(os.path.abspath(__file__)), "images"))
(na, ca), (nb, cb) = [a.split("=", 1) for a in sys.argv[1:3]]
nk = int(os.environ.get("KODAK", "8")); reps = int(os.environ.get("REPS", "8"))
sets = [("photos", sorted(glob.glob(B + "/lossless/photos/*.webp"))),
        ("kodak", sorted(glob.glob(B + "/lossless/kodak/*.webp"))[:nk]),
        ("graphics", sorted(glob.glob(B + "/lossless/graphics/*.webp")))]
def rec(f):
    d = open(f, "rb").read()
    return struct.pack("<I", len(d)) + d
def pixels(cmd, r):
    o = subprocess.run([cmd], input=r, stdout=subprocess.PIPE, check=True).stdout
    # wdec: status, code (i32), w, h, pixels; lbatch: status, w, h, pixels
    return o[13:] if os.path.basename(cmd).startswith("wdec") else o[9:]
def cpu(cmd, data):
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    subprocess.run([cmd], input=data, stdout=subprocess.DEVNULL, check=True)
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    return (r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime)
def size(f):
    d = open(f, "rb").read(); i = d.find(b"VP8L") + 9
    v = struct.unpack("<I", d[i:i + 4])[0]
    return ((v & 0x3fff) + 1) * (((v >> 14) & 0x3fff) + 1)
for name, files in sets:
    for f in files:
        r = rec(f)
        if pixels(ca, r) != pixels(cb, r):
            sys.exit("pixels differ on " + f)
allogs = []
sets = [(n, f) for n, f in sets if f]
for name, files in sets:
    logs = []; best = {na: 0.0, nb: 0.0}; px = 0
    for f in files:
        r = rec(f); px += size(f)
        t1 = cpu(ca, r); k = max(2, min(200, int(0.4 / max(t1, 1e-3))))
        data = r * k
        ratios = []; bt = {na: 1e9, nb: 1e9}
        for rep in range(reps):
            order = [(na, ca), (nb, cb)] if rep % 2 == 0 else [(nb, cb), (na, ca)]
            t = {n: cpu(c, data) / k for n, c in order}
            ratios.append(t[na] / t[nb]); bt[na] = min(bt[na], t[na]); bt[nb] = min(bt[nb], t[nb])
        logs.append(math.log(statistics.median(ratios)))
        best[na] += bt[na]; best[nb] += bt[nb]
    allogs += logs
    print("%-8s %2d images: %s is %.3fx as fast as %s; best %s %.1f MP/s, %s %.1f MP/s"
          % (name, len(files), nb, math.exp(sum(logs) / len(logs)), na, na, px / best[na] / 1e6, nb, px / best[nb] / 1e6))
print("all      %2d images: %s is %.3fx as fast as %s (geomean of per-image medians)"
      % (len(allogs), nb, math.exp(sum(allogs) / len(allogs)), na))
