#!/usr/bin/env python3
"""Structure-aware VP8L streams: our own writer (not libwebp's encoder), so
the streams reach what cwebp never writes. Random transforms in random
order (sometimes repeated); predictor images with every green value;
color tables of every size, with indexes past the table; color caches of
every size (and invalid ones); entropy images with unused groups and
over 1000 groups; prefix codes as random complete trees, written as simple
or normal codes (random runs of 16/17/18, max_symbol, single-symbol code
length codes), and on purpose incomplete, over-subscribed, empty,
single-symbol with a length other than 1, simple symbols outside the
alphabet; LZ77 copies with every distance code, overlapping, past the start
or the end. Streams are then sometimes truncated or extended.

The decoder is simulated as the stream is written, so most streams are
valid; `mistake()` injects the invalid ones. Each stream is decoded by our
decoder and libwebp's, as in wdiff.py.

  gen.py [-n N] [--seed S] [--tool batch-spec] [--save DIR] [--p-bad P]
"""
import argparse
import multiprocessing
import os
import random
import sys

import wlib

CL_ORDER = [17, 18, 0, 1, 2, 3, 4, 5, 16, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
DIST_MAP = [
    (0, 1), (1, 0), (1, 1), (-1, 1), (0, 2), (2, 0), (1, 2), (-1, 2), (2, 1), (-2, 1), (2, 2), (-2, 2),
    (0, 3), (3, 0), (1, 3), (-1, 3), (3, 1), (-3, 1), (2, 3), (-2, 3), (3, 2), (-3, 2), (0, 4), (4, 0),
    (1, 4), (-1, 4), (4, 1), (-4, 1), (3, 3), (-3, 3), (2, 4), (-2, 4), (4, 2), (-4, 2), (0, 5), (3, 4),
    (-3, 4), (4, 3), (-4, 3), (5, 0), (1, 5), (-1, 5), (5, 1), (-5, 1), (2, 5), (-2, 5), (5, 2), (-5, 2),
    (4, 4), (-4, 4), (3, 5), (-3, 5), (5, 3), (-5, 3), (0, 6), (6, 0), (1, 6), (-1, 6), (6, 1), (-6, 1),
    (2, 6), (-2, 6), (6, 2), (-6, 2), (4, 5), (-4, 5), (5, 4), (-5, 4), (3, 6), (-3, 6), (6, 3), (-6, 3),
    (0, 7), (7, 0), (1, 7), (-1, 7), (5, 5), (-5, 5), (7, 1), (-7, 1), (4, 6), (-4, 6), (6, 4), (-6, 4),
    (2, 7), (-2, 7), (7, 2), (-7, 2), (3, 7), (-3, 7), (7, 3), (-7, 3), (5, 6), (-5, 6), (6, 5), (-6, 5),
    (8, 0), (4, 7), (-4, 7), (7, 4), (-7, 4), (8, 1), (8, 2), (6, 6), (-6, 6), (8, 3), (5, 7), (-5, 7),
    (7, 5), (-7, 5), (8, 4), (6, 7), (-6, 7), (7, 6), (-7, 6), (8, 5), (7, 7), (-7, 7), (8, 6), (8, 7),
]


class W:
    """LSB-first bit writer (RFC 9649 3.2)."""

    def __init__(self):
        self.bits = []

    def w(self, v, n):
        for j in range(n):
            self.bits.append((v >> j) & 1)

    def code(self, c, l):
        """A prefix code's bits, most significant first."""
        for j in range(l - 1, -1, -1):
            self.bits.append((c >> j) & 1)

    def bytes(self):
        out = bytearray((len(self.bits) + 7) // 8)
        for i, b in enumerate(self.bits):
            out[i // 8] |= b << (i % 8)
        return bytes(out)


def canon(lens):
    """sym -> (code, len), DEFLATE's canonical assignment."""
    count = [0] * 16
    for l in lens:
        count[l] += 1
    count[0] = 0
    nxt, code = [0] * 16, 0
    for l in range(1, 16):
        code = (code + count[l - 1]) << 1
        nxt[l] = code
    out = {}
    for s, l in enumerate(lens):
        if l:
            out[s] = (nxt[l], l)
            nxt[l] += 1
    return out


def tree_lengths(rng, k, maxlen):
    """Leaf depths of a random complete binary tree with k >= 2 leaves."""
    leaves = [0]
    while len(leaves) < k:
        cand = [i for i, d in enumerate(leaves) if d < maxlen]
        # bias: sometimes split the deepest, for long codes and second-level tables
        i = max(cand, key=lambda j: leaves[j]) if rng.random() < 0.3 else rng.choice(cand)
        d = leaves.pop(i)
        leaves += [d + 1, d + 1]
    rng.shuffle(leaves)
    return leaves


class G:
    """One stream's generator: an rng, a writer, a 'badness' budget."""

    def __init__(self, rng, p_bad):
        self.rng = rng
        self.p_bad = p_bad
        self.bw = W()
        self.bad = []  # what was injected
        self.notes = set()  # valid features worth knowing (no randomness used)

    def mistake(self, what, p=1.0):
        """Inject `what`, with probability p_bad * p (at most 2 per stream)."""
        if len(self.bad) < 2 and self.rng.random() < self.p_bad * p:
            self.bad.append(what)
            return True
        return False

    # ------------------------------------------------------------ codes

    def make_lens(self, asize, used):
        """Lengths for a code over `used` (and some extra symbols)."""
        rng = self.rng
        syms = set(used)
        if not syms:
            syms = {rng.choice([0, 0, rng.randrange(asize)])}
        extra = rng.choice([0, 0, 0, 1, 3, 20, asize])
        for _ in range(extra):
            syms.add(rng.randrange(asize))
        syms = sorted(syms)
        lens = [0] * asize
        if len(syms) == 1:
            l = 1
            if self.mistake("single-symbol code of length != 1", 0.5):
                l = rng.randint(2, 15)
            lens[syms[0]] = l
            return lens
        ds = tree_lengths(rng, len(syms), 15)
        for s, d in zip(syms, ds):
            lens[s] = d
        if self.mistake("incomplete code", 0.3):
            nz = [s for s in syms if lens[s] < 15]
            if nz:
                lens[rng.choice(nz)] += 1
        elif self.mistake("over-subscribed code", 0.3):
            nz = [s for s in syms if lens[s] > 1]
            if nz:
                lens[rng.choice(nz)] -= 1
        elif self.mistake("empty code", 0.1):
            lens = [0] * asize
        return lens

    def write_code(self, asize, lens):
        rng, bw = self.rng, self.bw
        nz = [s for s, l in enumerate(lens) if l]
        simple_ok = 1 <= len(nz) <= 2 and all(s < 256 and lens[s] == 1 for s in nz)
        if simple_ok and rng.random() < 0.8:
            bw.w(1, 1)
            syms = list(nz)
            if len(syms) == 2 and rng.random() < 0.5:
                syms.reverse()
                self.notes.add("simple descending")
            if len(syms) == 1 and rng.random() < 0.1:
                syms = syms * 2  # a duplicate: allowed
                self.notes.add("simple duplicate")
            if asize < 256 and len(syms) == 1 and self.mistake("simple symbol outside the alphabet", 0.5):
                syms = syms + [rng.randrange(asize, 256)]
            bw.w(len(syms) - 1, 1)
            first8 = 0 if syms[0] < 2 and rng.random() < 0.7 else 1
            bw.w(first8, 1)
            bw.w(syms[0], 8 if first8 else 1)
            if len(syms) == 2:
                bw.w(syms[1], 8)
            return
        bw.w(0, 1)
        # tokens: run-length the lengths (up to the last nonzero if max_symbol is used)
        use_max = rng.random() < 0.4
        end = (max(nz) + 1 if nz else 1) if use_max else asize
        toks = []
        i, prev = 0, 8
        while i < end:
            l = lens[i]
            run = 1
            while i + run < end and lens[i + run] == l:
                run += 1
            if l == 0 and run >= 3 and rng.random() < 0.9:
                n = min(run, 138)
                if n >= 11 and rng.random() < 0.8:
                    toks.append((18, n - 11, 7))
                else:
                    n = min(n, 10)
                    toks.append((17, n - 3, 3))
                i += n
            elif l != 0 and l == prev and run >= 3 and rng.random() < 0.8:
                n = min(run, 6)
                toks.append((16, n - 3, 2))
                i += n
            else:
                toks.append((l, 0, 0))
                if l:
                    prev = l
                i += 1
        if self.mistake("repeat past the alphabet", 0.2) and not use_max:
            toks.append((17, 7, 3))
        # the code length code over the token symbols
        tsyms = sorted({t[0] for t in toks})
        cll = [0] * 19
        if len(tsyms) == 1:
            cll[tsyms[0]] = 1 if rng.random() < 0.7 else rng.randint(1, 7)
        else:
            for s, d in zip(tsyms, tree_lengths(rng, len(tsyms), 7)):
                cll[s] = d
            if self.mistake("incomplete code length code", 0.2):
                s = rng.choice([s for s in tsyms if cll[s] < 7] or tsyms)
                cll[s] = min(7, cll[s] + 1)
        last = max(k for k in range(19) if cll[CL_ORDER[k]]) + 1
        n = max(4, last, rng.choice([last, last, 19]))
        bw.w(n - 4, 4)
        for k in range(n):
            bw.w(cll[CL_ORDER[k]], 3)
        cc = canon(cll)
        if use_max:
            m = len(toks)
            if self.mistake("max_symbol > alphabet", 0.3):
                m = asize + 1
            if m < 2:
                toks.append((0, 0, 0))  # max_symbol is at least 2
                m = 2
                if 0 not in cc:
                    raise Retry()  # max_symbol is at least 2 tokens; no token 0 to pad with
            v = m - 2
            k = 0
            while v >= 1 << (2 + 2 * k):
                k += 1
            bw.w(1, 1)
            bw.w(k, 3)
            bw.w(v, 2 + 2 * k)
        else:
            bw.w(0, 1)
        for s, e, eb in toks:
            if s not in cc:
                continue  # cannot happen: every token symbol has a length
            c, l = cc[s]
            if len(cc) > 1:
                bw.code(c, l)
            bw.w(e, eb)

    def code_for(self, asize, used):
        lens = self.make_lens(asize, used)
        self.write_code(asize, lens)
        return canon(lens), lens

    # ------------------------------------------------------------ image data

    def plan_pixels(self, w, h, cache_bits, group_of, want):
        """Choose tokens for a w x h image, simulating the decoder: literals
        (from `want(i)` or random), cache hits, copies. Returns the tokens
        and, per group, the symbols each of its five codes must have."""
        rng = self.rng
        total = w * h
        px, cache, toks = [], [0] * (1 << cache_bits) if cache_bits else [], []
        used = {}

        def put(c):
            px.append(c)
            if cache_bits:
                cache[((c * 0x1e35a7bd) & 0xffffffff) >> (32 - cache_bits)] = c

        p_copy = rng.choice([0, 0.05, 0.2, 0.5])
        p_cache = rng.choice([0, 0.1, 0.4]) if cache_bits else 0
        while len(px) < total:
            i = len(px)
            g = group_of(i % w, i // w)
            u = used.setdefault(g, [set() for _ in range(5)])
            r = rng.random()
            if r < p_copy and i > 0:
                if rng.random() < 0.5:
                    k = rng.randrange(120)
                    xi, yi = DIST_MAP[k]
                    dcode = k + 1
                    d = max(1, xi + yi * w)
                else:
                    d = rng.randint(1, min(i, rng.choice([4, 40, 4000, 1 << 20])))
                    dcode = d + 120
                length = rng.randint(1, min(total - i, rng.choice([3, 10, 300, 4096])))
                if self.mistake("copy past the end", 0.05):
                    length = min(4096, total - i + rng.randint(1, 3))
                elif d > i and not self.mistake("copy before the start", 0.3):
                    d, dcode = i, i + 120
                if d > i or length > total - i:
                    toks.append(("copy", g, length, dcode))
                    ls, _, _ = prefix(length)
                    ds, _, _ = prefix(dcode)
                    u[0].add(256 + ls)
                    u[4].add(ds)
                    return toks, used, px  # decoding stops here
                ls, _, _ = prefix(length)
                ds, _, _ = prefix(dcode)
                u[0].add(256 + ls)
                u[4].add(ds)
                toks.append(("copy", g, length, dcode))
                for _ in range(length):
                    put(px[len(px) - d])
            elif cache_bits and r < p_copy + p_cache:
                key = rng.randrange(len(cache))
                u[0].add(280 + key)
                toks.append(("cache", g, key))
                put(cache[key])
            else:
                c = want(i) if want else None
                if c is None:
                    c = rng.choice([rng.getrandbits(32), 0xff000000 | rng.getrandbits(24),
                                    px[-1] if px else 0, rng.choice([0, 0xffffffff, 0xff000000])])
                a, rr, gg, b = c >> 24, (c >> 16) & 255, (c >> 8) & 255, c & 255
                u[0].add(gg)
                u[1].add(rr)
                u[2].add(b)
                u[3].add(a)
                toks.append(("lit", g, c))
                put(c)
        return toks, used, px

    def write_groups(self, ngroups, cache_bits, used):
        asizes = [256 + 24 + ((1 << cache_bits) if cache_bits else 0), 256, 256, 256, 40]
        codes = []
        for g in range(ngroups):
            u = used.get(g, [set() for _ in range(5)])
            codes.append([self.code_for(asizes[j], u[j])[0] for j in range(5)])
        return codes

    def write_tokens(self, toks, codes):
        bw = self.bw

        def sym(g, j, s):
            cc = codes[g][j]
            if len(cc) > 1:
                c, l = cc[s]
                bw.code(c, l)

        for t in toks:
            if t[0] == "lit":
                _, g, c = t
                sym(g, 0, (c >> 8) & 255)
                sym(g, 1, (c >> 16) & 255)
                sym(g, 2, c & 255)
                sym(g, 3, c >> 24)
            elif t[0] == "cache":
                _, g, key = t
                sym(g, 0, 280 + key)
            else:
                _, g, length, dcode = t
                ls, le, leb = prefix(length)
                sym(g, 0, 256 + ls)
                bw.w(le, leb)
                ds, de, deb = prefix(dcode)
                sym(g, 4, ds)
                bw.w(de, deb)

    def cache_info(self):
        rng = self.rng
        if rng.random() < 0.5:
            self.bw.w(0, 1)
            return 0
        cb = rng.randint(1, 11)
        if self.mistake("color cache bits out of range", 0.2):
            cb = rng.choice([0, 12, 13, 14, 15])
        self.bw.w(1, 1)
        self.bw.w(cb, 4)
        return cb if 1 <= cb <= 11 else None

    def entropy_coded_image(self, w, h, want):
        cb = self.cache_info()
        if cb is None:
            raise Stop()
        toks, used, px = self.plan_pixels(w, h, cb, lambda x, y: 0, want)
        codes = self.write_groups(1, cb, used)
        self.write_tokens(toks, codes)
        if len(px) < w * h:
            raise Stop()
        return px

    def spatially_coded_image(self, w, h):
        rng, bw = self.rng, self.bw
        cb = self.cache_info()
        if cb is None:
            raise Stop()
        if rng.random() < 0.4:
            bw.w(1, 1)
            bits = rng.randint(0, 7)
            bw.w(bits, 3)
            bits += 2
            ew, eh = -(-w // (1 << bits)), -(-h // (1 << bits))
            k = rng.choice([1, 2, 3, 6, 20])
            big = rng.random() < 0.05
            idx = [rng.randrange(k) for _ in range(ew * eh)]
            if big:
                idx[rng.randrange(len(idx))] = rng.randint(1000, 1300)  # libwebp's remapping path
            if rng.random() < 0.3:
                idx[rng.randrange(len(idx))] += rng.randint(1, 5)  # leave some groups unused
            ent = self.entropy_coded_image(
                ew, eh, lambda i: (rng.getrandbits(8) << 24) | (idx[i] << 8) | rng.getrandbits(8))
            groups = [(v >> 8) & 0xffff for v in ent]
            ngroups = max(groups) + 1

            def group_of(x, y):
                return groups[(y >> bits) * ew + (x >> bits)]
        else:
            bw.w(0, 1)
            ngroups = 1

            def group_of(x, y):
                return 0
        want = self.main_want
        toks, used, px = self.plan_pixels(w, h, cb, group_of, want)
        codes = self.write_groups(ngroups, cb, used)
        self.write_tokens(toks, codes)

    def stream(self):
        rng, bw = self.rng, self.bw
        shape = rng.random()
        if shape < 0.2:
            w, h = rng.randint(1, 3), rng.randint(1, 3)
        elif shape < 0.3:
            w, h = rng.choice([(1, rng.randint(1, 200)), (rng.randint(1, 200), 1)])
        else:
            w, h = rng.randint(1, 48), rng.randint(1, 40)
        bw.w(0x2f, 8)
        bw.w(w - 1, 14)
        bw.w(h - 1, 14)
        bw.w(rng.randrange(2), 1)
        ver = 0 if not self.mistake("version != 0", 0.1) else rng.randint(1, 7)
        bw.w(ver, 3)
        order = [t for t in range(4) if rng.random() < 0.45]
        rng.shuffle(order)
        if order and self.mistake("a transform twice", 0.2):
            order.insert(rng.randrange(len(order) + 1), rng.choice(order))
        self.main_want = None
        xs = w
        for t in order:
            bw.w(1, 1)
            bw.w(t, 2)
            if t in (0, 1):
                bits = rng.randint(0, 7)
                bw.w(bits, 3)
                bits += 2
                tw, th = -(-xs // (1 << bits)), -(-h // (1 << bits))
                if t == 0:
                    lim = rng.choice([14, 16, 256])
                    self.entropy_coded_image(tw, th, lambda i: (rng.getrandbits(8) << 24) | (rng.randrange(lim) << 8))
                else:
                    self.entropy_coded_image(tw, th, lambda i: 0xff000000 | rng.getrandbits(24))
            elif t == 3:
                n = rng.choice([1, 2, 3, 4, 5, 16, 17, rng.randint(1, 256)])
                bw.w(n - 1, 8)
                self.entropy_coded_image(n, 1, None)
                wb = 0 if n > 16 else 1 if n > 4 else 2 if n > 2 else 3
                xs = -(-xs // (1 << wb))
                top = 1 << (8 >> wb) if wb else 256
                over = rng.random() < 0.2  # indexes past the table
                m = top if over else n

                def want(i, wb=wb, m=m):
                    if wb == 0:
                        return (rng.getrandbits(8) << 24) | (rng.randrange(m) << 8)
                    nb = 8 >> wb
                    g = 0
                    for k in range(1 << wb):
                        g |= rng.randrange(min(m, 1 << nb)) << (k * nb)
                    return 0xff000000 | (g << 8)
                if rng.random() < 0.8:
                    self.main_want = want
        bw.w(0, 1)
        self.spatially_coded_image(xs, h)


class Stop(Exception):
    """The stream is already invalid: stop writing it."""


class Retry(Exception):
    """This choice of encoding does not work: draw another stream."""


def prefix(v):
    """LZ77 prefix coding (3.6.2.2): (symbol, extra value, extra bits) for v >= 1."""
    if v <= 4:
        return v - 1, 0, 0
    x = v - 1
    hb = x.bit_length() - 1
    second = (x >> (hb - 1)) & 1
    eb = hb - 1
    return 2 * hb + second, x & ((1 << eb) - 1), eb


def one(job, notes=None):
    """A stream and what was injected. `notes`, a set, gets G.notes."""
    seed, i, p_bad = job
    for attempt in range(20):
        rng = random.Random((seed * 1000003 + i) * 31 + attempt)
        g = G(rng, p_bad if rng.random() < 0.5 else 0.0)  # half the streams meant valid
        try:
            g.stream()
        except Stop:
            pass
        except Retry:
            continue
        s = g.bw.bytes()
        if notes is not None:
            notes |= g.notes
        r = rng.random()
        what = ",".join(g.bad) or "valid"
        if r < 0.1 and len(s) > 1:
            s = s[:rng.randrange(1, len(s))]
            what += "+truncated"
        elif r < 0.15:
            s += bytes(rng.getrandbits(8) for _ in range(rng.randint(1, 8)))
            what += "+extended"
        return s, what
    return b"\x2f", "gave up"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--tool", default="batch-spec")
    ap.add_argument("--limit", type=int, default=1 << 22)
    ap.add_argument("--p-bad", type=float, default=0.1)
    ap.add_argument("-j", type=int, default=min(32, os.cpu_count()))
    ap.add_argument("--save", help="directory for failing inputs")
    ap.add_argument("--dump", help="write every stream into this directory")
    a = ap.parse_args()
    with multiprocessing.Pool(a.j) as pool:
        recs = pool.map(one, [(a.seed, i, a.p_bad) for i in range(a.n)])
    recs = [(wlib.even(s), what) for s, what in recs]
    if a.dump:
        os.makedirs(a.dump, exist_ok=True)
        for k, (s, what) in enumerate(recs):
            open(os.path.join(a.dump, "g%d_%d.vp8l" % (a.seed, k)), "wb").write(s)
    inputs = [r[0] for r in recs]
    ours = wlib.run_ours(inputs, a.tool, a.limit)
    ref = wlib.run_libwebp(inputs, a.limit)
    fails = ok_img = ok_err = lenient = valid_refused = 0
    for k, ((s, what), x, y) in enumerate(zip(recs, ours, ref)):
        if wlib.same(x, y):
            if x is None:
                ok_err += 1
                valid_refused += what == "valid"
            else:
                ok_img += 1
                lenient += not x[3]["strict"]
            continue
        fails += 1
        print("FAIL #%d (%s): ours %s, libwebp %s" % (k, what, wlib.describe(x), wlib.describe(y)))
        if x is not None and y is not None and x[:2] == y[:2]:
            print("     first differing pixel (index, ours, libwebp):", wlib.first_diff(x, y))
        if a.save:
            os.makedirs(a.save, exist_ok=True)
            open(os.path.join(a.save, "gfail%d_%d.vp8l" % (a.seed, k)), "wb").write(s)
    print("seed %d: %d streams: %d images agree (%d lenient), %d both refuse (%d meant valid), %d FAIL" %
          (a.seed, len(recs), ok_img, lenient, ok_err, valid_refused, fails))
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
