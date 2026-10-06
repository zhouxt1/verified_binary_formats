"""Synthetic graphics for the lossless benchmark (PPM, deterministic):
ui (flat panels, borders, glyph-like text), chart (axes, lines, bars),
icons (small tiles of few colors and short gradients), gradient (smooth
two-axis ramps with flat shapes). Usage: gen_graphics.py OUTDIR"""
import os, random, sys
W, H = 1024, 768
def img(bg): return [[bg] * W for _ in range(H)]
def rect(im, x0, y0, x1, y1, c):
    for y in range(max(0, y0), min(H, y1)):
        row = im[y]
        for x in range(max(0, x0), min(W, x1)): row[x] = c
def line(im, x0, y0, x1, y1, c):
    n = max(abs(x1 - x0), abs(y1 - y0), 1)
    for i in range(n + 1):
        x = x0 + (x1 - x0) * i // n; y = y0 + (y1 - y0) * i // n
        if 0 <= x < W and 0 <= y < H: im[y][x] = c
def save(im, path):
    with open(path, "wb") as f:
        f.write(b"P6\n%d %d\n255\n" % (W, H))
        f.write(bytes(v for row in im for c in row for v in c))
def ui(r):
    im = img((236, 236, 240))
    for _ in range(40):
        x, y = r.randrange(W), r.randrange(H); w, h = r.randrange(40, 400), r.randrange(20, 200)
        c = r.choice([(255, 255, 255), (250, 250, 252), (52, 120, 246), (230, 230, 235), (40, 44, 52)])
        rect(im, x, y, x + w, y + h, c)
        for xx in (x, x + w - 1): line(im, xx, y, xx, y + h - 1, (200, 200, 205))
        for yy in (y, y + h - 1): line(im, x, yy, x + w - 1, yy, (200, 200, 205))
        ink = (20, 20, 20) if c[0] > 128 else (240, 240, 240)
        for ty in range(y + 6, y + h - 10, 14):
            for tx in range(x + 6, x + w - 8, 7):
                if r.random() < 0.15: continue
                g = r.getrandbits(35)
                for k in range(35):
                    if g >> k & 1 and 0 <= ty + k // 5 < H and 0 <= tx + k % 5 < W: im[ty + k // 5][tx + k % 5] = ink
    return im
def chart(r):
    im = img((255, 255, 255))
    line(im, 60, 20, 60, H - 40, (0, 0, 0)); line(im, 60, H - 40, W - 20, H - 40, (0, 0, 0))
    for gy in range(40, H - 40, 50): line(im, 61, gy, W - 20, gy, (225, 225, 225))
    for i in range(24):
        h = r.randrange(50, 500); c = [(66, 133, 244), (219, 68, 55), (244, 180, 0)][i % 3]
        rect(im, 80 + i * 38, H - 40 - h, 80 + i * 38 + 28, H - 40, c)
    for c in [(15, 157, 88), (171, 71, 188), (0, 172, 193)]:
        y = r.randrange(100, 600)
        for x in range(60, W - 20, 8):
            y2 = max(20, min(H - 41, y + r.randrange(-30, 31)))
            for d in range(3): line(im, x, y + d, x + 8, y2 + d, c)
            y = y2
    return im
def icons(r):
    im = img((255, 255, 255))
    for ty in range(0, H - 47, 48):
        for tx in range(0, W - 47, 48):
            pal = [tuple(r.randrange(256) for _ in range(3)) for _ in range(4)]
            for y in range(ty + 8, ty + 40):
                for x in range(tx + 8, tx + 40):
                    k = ((x - tx) // 8 + (y - ty) // 8 + r.randrange(2)) % 4
                    c = pal[k]
                    if k == 3: c = tuple(min(255, v + (x - tx)) for v in c)
                    im[y][x] = c
    return im
def gradient(r):
    im = [[((x * 255) // W, (y * 255) // H, ((x + y) * 255) // (W + H)) for x in range(W)] for y in range(H)]
    for _ in range(12):
        x, y = r.randrange(W), r.randrange(H)
        rect(im, x, y, x + r.randrange(30, 200), y + r.randrange(30, 200), tuple(r.randrange(256) for _ in range(3)))
    return im
out = sys.argv[1]; os.makedirs(out, exist_ok=True)
for name, f in [("ui", ui), ("chart", chart), ("icons", icons), ("gradient", gradient)]:
    save(f(random.Random(name)), os.path.join(out, name + ".ppm"))
