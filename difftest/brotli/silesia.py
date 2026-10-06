#!/usr/bin/env python3
"""Silesia, compressed by Google's encoder at several qualities and windows
(cached in /tmp/silesia-br), decoded by vbrotli's verified decoder and by
Google's C decoder: the data must be the file. Also times both (one run
each, through the batch protocol: a rough figure; bench/brotli is for
speed). Usage: silesia.py [--q 1,5,9,11] [--files a,b]"""
import argparse, os, struct, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
import brotli

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from bdiff import Proc, GDEC, TOOL

SIL = '/tmp/silesia'
CACHE = '/tmp/silesia-br'
FILES = ['dickens', 'mozilla', 'mr', 'nci', 'ooffice', 'osdb', 'reymont', 'samba', 'sao', 'webster', 'x-ray', 'xml']


def stream(f, q, w):
    p = os.path.join(CACHE, f'{f}.q{q}.w{w}.br')
    if not os.path.exists(p):
        data = open(os.path.join(SIL, f), 'rb').read()
        tmp = p + '.tmp'
        open(tmp, 'wb').write(brotli.compress(data, quality=q, lgwin=w))
        os.rename(tmp, p)
    return p


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--q', default='1,5,9,11')
    ap.add_argument('--files', default=','.join(FILES))
    ap.add_argument('--tool', default='batch')
    a = ap.parse_args()
    os.makedirs(CACHE, exist_ok=True)
    jobs = [(f, int(q), 22) for q in a.q.split(',') for f in a.files.split(',')]
    jobs += [(f, 5, w) for w in (16, 24) for f in a.files.split(',')]
    with ThreadPoolExecutor(os.cpu_count()) as ex:
        paths = list(ex.map(lambda j: stream(*j), jobs))
    g = Proc([GDEC], 'g')
    t = Proc([TOOL, a.tool], 't')
    fails = 0
    print(f'{"file":10} {"q":>3} {"w":>3} {"size":>10} {"ratio":>6} {"vbrotli MB/s":>12} {"google MB/s":>12}')
    for (f, q, w), p in zip(jobs, paths):
        data = open(os.path.join(SIL, f), 'rb').read()
        s = open(p, 'rb').read()
        t0 = time.perf_counter(); gr = g.run(s); t1 = time.perf_counter(); tr = t.run(s); t2 = time.perf_counter()
        ok = gr[0] == 1 and gr[3] == data and tr is not None and tr[2] == data and tr[1] and tr[0] == 8 * len(s)
        fails += not ok
        mb = len(data) / 1e6
        print(f'{f:10} {q:3} {w:3} {len(s):10} {len(data) / len(s):6.2f} {mb / (t2 - t1):12.1f} {mb / (t1 - t0):12.1f}'
              + ('' if ok else '  FAIL'))
    print(f'{len(jobs)} streams, {fails} failures')
    sys.exit(1 if fails else 0)


if __name__ == '__main__':
    main()
