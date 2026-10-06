#!/usr/bin/env python3
"""Differential test of vbrotli's spec against Google's brotli decoder.

Streams: data of several kinds (text sampled from the repository's files,
UTF-8 text, binary, random bytes, runs, short and empty inputs) compressed by
Google's encoder (the `brotli` Python module) at every quality, window
(lgwin 10..24), block size and mode, and their mutants (flipped bits,
truncations, extensions, overwritten bytes). Each stream is decoded by
Google's C decoder (`build/gdec`, v1.2.0) and by the decoder under test
(`vbrotli-tool batch-spec` by default: the executable transcription of the
spec). The verdicts must agree:

* the spec decodes with the Google flag on  <=>  Google succeeds;
  and then the data and the bytes consumed are the same;
* the spec decodes with the flag off  =>  Google fails;
* the spec has no result  =>  Google fails or wants more input.

After build.sh and `cargo build --release -p
vbrotli-tool`. Usage: bdiff.py [-n N] [--seed S] [--tool batch-spec|batch]
"""
import argparse, os, random, struct, subprocess, sys, glob

import brotli

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
GDEC = os.path.join(HERE, 'build', 'gdec')
TOOL = os.path.join(ROOT, 'target', 'release', 'vbrotli-tool')


class Proc:
    """A batch decoder: send a stream, read its record back."""

    def __init__(self, argv, kind):
        self.p = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        self.kind = kind

    def rd(self, n):
        b = self.p.stdout.read(n)
        assert len(b) == n, 'decoder died'
        return b

    def run(self, data):
        self.p.stdin.write(struct.pack('<I', len(data)) + data)
        self.p.stdin.flush()
        if self.kind == 'g':
            status, code, used, n = struct.unpack('<BiQI', self.rd(17))
            return status, code, used, self.rd(n)
        status = self.rd(1)[0]
        if status == 0:
            return None
        google, bits, n = struct.unpack('<BQI', self.rd(13))
        return bits, bool(google), self.rd(n)


def corpus_files():
    """The repository's text files (no symlinks, no build outputs)."""
    fs = []
    for d, dirs, names in os.walk(ROOT, followlinks=False):
        dirs[:] = [x for x in dirs if x not in ('target', 'build', '.git') and not os.path.islink(os.path.join(d, x))]
        for x in names:
            f = os.path.join(d, x)
            if x.endswith(('.rs', '.md', '.py', '.txt', '.json')) and not os.path.islink(f) and os.path.getsize(f) > 0:
                fs.append(f)
    return sorted(fs)


def gen_data(r, files):
    k = r.randrange(9)
    n = r.choice([0, 1, 2, 3, 5, 17, 100, 1000, 5000, 20000, 70000, 200000])
    if k == 0:  # text from the repository
        s = open(r.choice(files), 'rb').read()
        i = r.randrange(len(s))
        return s[i:i + n]
    if k == 1:  # several files' text
        return b''.join(open(r.choice(files), 'rb').read()[:n // 3 + 1] for _ in range(3))[:n]
    if k == 2:  # UTF-8 text with non-ASCII letters
        words = ['naïve', 'café', 'Straße', 'Москва', 'город', '東京', 'データ', 'the', 'of', 'and',
                 'élan', 'ζωή', 'हिन्दी', 'data', 'html', '<div class="x">', '</div>']
        return ' '.join(r.choice(words) for _ in range(n // 5 + 1)).encode()[:n]
    if k == 3:
        return bytes(r.randrange(256) for _ in range(min(n, 30000)))
    if k == 4:  # runs
        out = bytearray()
        while len(out) < n:
            out += bytes([r.randrange(256)]) * r.randrange(1, 300)
        return bytes(out[:n])
    if k == 5:  # small alphabet
        a = bytes(r.randrange(256) for _ in range(r.randrange(1, 6)))
        return bytes(r.choice(a) for _ in range(min(n, 50000)))
    if k == 6:  # repeats at long distances
        base = bytes(r.randrange(256) for _ in range(r.randrange(1, 3000)))
        return (base * (n // max(1, len(base)) + 1))[:n]
    if k == 7:  # binary: the repository's build of the tool, if any
        s = open(TOOL, 'rb').read()
        i = r.randrange(len(s))
        return s[i:i + n]
    # words for the static dictionary, with punctuation
    ws = [b'the', b'of', b'and', b'time', b'down', b'life', b'left', b'back', b'code', b'data',
          b'show', b'only', b'site', b'city', b'open', b'just', b'like', b'free', b'work', b'text']
    seps = [b' ', b', ', b'. ', b'\n', b'="', b'">', b'(', b'ing ', b'ed ', b"'"]
    out = bytearray()
    while len(out) < n:
        w = r.choice(ws)
        if r.random() < 0.3:
            w = w.capitalize()
        if r.random() < 0.1:
            w = w.upper()
        out += w + r.choice(seps)
    return bytes(out[:n])


def compress(r, data):
    q = r.randrange(12)
    w = r.randrange(10, 25)
    kw = dict(quality=q, lgwin=w, mode=r.choice([brotli.MODE_GENERIC, brotli.MODE_TEXT, brotli.MODE_FONT]))
    if r.random() < 0.3:
        kw['lgblock'] = r.choice([0] + list(range(16, 25)))
    return brotli.compress(data, **kw), kw


def mutate(r, s):
    s = bytearray(s)
    k = r.randrange(5)
    if k == 0 and s:
        for _ in range(r.randrange(1, 4)):
            i = r.randrange(len(s) * 8)
            s[i // 8] ^= 1 << (i % 8)
    elif k == 1 and s:
        s = s[:r.randrange(len(s))]
    elif k == 2:
        s += bytes(r.randrange(256) for _ in range(r.randrange(1, 5)))
    elif k == 3 and s:
        i = r.randrange(len(s))
        for j in range(i, min(len(s), i + r.randrange(1, 4))):
            s[j] = r.randrange(256)
    elif s:  # flip a bit near the start, where the headers are
        i = r.randrange(min(len(s) * 8, 200))
        s[i // 8] ^= 1 << (i % 8)
    return bytes(s)


def check(g, t, s, what, fails):
    status, code, used, gout = g
    if t is None:
        ok = status != 1
    else:
        bits, google, out = t
        if google:
            ok = status == 1 and used * 8 == bits and gout == out
        else:
            ok = status != 1
    if not ok:
        fails.append((what, s, g[:3], None if t is None else (t[0], t[1], len(t[2]))))
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('-n', type=int, default=500)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--tool', default='batch-spec')
    ap.add_argument('--mutants', type=int, default=3)
    a = ap.parse_args()
    r = random.Random(a.seed)
    files = corpus_files()
    g = Proc([GDEC], 'g')
    t = Proc([TOOL, a.tool], 't')
    fails, n, flagged, rejected = [], 0, 0, 0
    for i in range(a.n):
        data = gen_data(r, files)
        s, kw = compress(r, data)
        streams = [(s, ('orig', kw))] + [(mutate(r, s), ('mutant', kw)) for _ in range(a.mutants)]
        for st, what in streams:
            gr, tr = g.run(st), t.run(st)
            n += 1
            if tr is None:
                rejected += 1
            elif not tr[1]:
                flagged += 1
            if what[0] == 'orig' and (gr[0] != 1 or gr[3] != data):
                fails.append(('google does not round-trip', st, gr[:3], None))
            check(gr, tr, st, what, fails)
    print(f'{n} streams ({a.n} compressed, {n - a.n} mutants): {rejected} without a result, '
          f'{flagged} with the Google flag off, {len(fails)} failures')
    os.makedirs(os.path.join(HERE, 'build', 'fails'), exist_ok=True)
    for j, (what, st, gr, tr) in enumerate(fails[:20]):
        p = os.path.join(HERE, 'build', 'fails', f'{a.seed}-{j}.br')
        open(p, 'wb').write(st)
        print(' FAIL', what, 'google', gr, 'tool', tr, p)
    sys.exit(1 if fails else 0)


if __name__ == '__main__':
    main()
