# Minimal PNG (8-bit RGB/RGBA, non-interlaced) to PPM, stdlib only.
import sys, zlib, struct
def conv(src, dst):
    d = open(src, 'rb').read(); assert d[:8] == b'\x89PNG\r\n\x1a\n'
    i, idat = 8, b''
    while i < len(d):
        n, t = struct.unpack('>I4s', d[i:i+8]); c = d[i+8:i+8+n]; i += 12 + n
        if t == b'IHDR': w, h, bd, ct, _, _, il = struct.unpack('>IIBBBBB', c); assert bd == 8 and il == 0 and ct in (2, 6)
        elif t == b'IDAT': idat += c
    bpp = 3 if ct == 2 else 4; raw = zlib.decompress(idat); stride = w * bpp
    out, prev, p = bytearray(), bytearray(stride), 0
    for _ in range(h):
        f = raw[p]; line = bytearray(raw[p+1:p+1+stride]); p += 1 + stride
        for x in range(stride):
            a = line[x-bpp] if x >= bpp else 0; b = prev[x]; cc = prev[x-bpp] if x >= bpp else 0
            if f == 1: line[x] = (line[x] + a) & 255
            elif f == 2: line[x] = (line[x] + b) & 255
            elif f == 3: line[x] = (line[x] + (a + b) // 2) & 255
            elif f == 4:
                pa, pb, pc = abs(b - cc), abs(a - cc), abs(a + b - 2 * cc)
                line[x] = (line[x] + (a if pa <= pb and pa <= pc else b if pb <= pc else cc)) & 255
        prev = line
        out += line if bpp == 3 else bytes(v for k, v in enumerate(line) if k % 4 != 3)
    open(dst, 'wb').write(b'P6\n%d %d\n255\n' % (w, h) + bytes(out))
for s in sys.argv[1:]: conv(s, s[:-4] + '.ppm')
