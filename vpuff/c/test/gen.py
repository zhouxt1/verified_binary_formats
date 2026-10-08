"""Streams for the puff differential test: zlib raw deflate at every level and
strategy, then truncated, bit-flipped and random mutants. Writes length-prefixed
records to stdout."""
import os, random, struct, sys, zlib
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
N = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
out = sys.stdout.buffer
def emit(b): out.write(struct.pack('<I', len(b)) + b)
def data():
    k = random.random()
    n = random.choice([0, 1, 2, 10, 100, 1000, 5000, 40000])
    if k < 0.3: return bytes(random.randrange(256) for _ in range(n))
    if k < 0.6: return bytes(random.choice(b'abcab ') for _ in range(n))
    if k < 0.8: return os.urandom(8) * (n // 8 + 1)
    return bytes(random.randrange(4) for _ in range(n))
for i in range(N):
    d = data()
    lvl = random.choice([0, 1, 6, 9])
    strat = random.choice([zlib.Z_DEFAULT_STRATEGY, zlib.Z_FIXED, zlib.Z_HUFFMAN_ONLY, zlib.Z_RLE])
    c = zlib.compressobj(lvl, zlib.DEFLATED, -15, 9, strat)
    s = c.compress(d) + c.flush()
    emit(s)
    m = bytearray(s)
    k = random.random()
    if k < 0.35 and m:
        for _ in range(random.randint(1, 3)):
            j = random.randrange(len(m)); m[j] ^= 1 << random.randrange(8)
    elif k < 0.6 and m:
        m = m[:random.randrange(len(m))]
    elif k < 0.75:
        m = bytearray(os.urandom(random.randint(0, 64)))
    else:
        m = m + os.urandom(random.randint(1, 8))
    emit(bytes(m))
