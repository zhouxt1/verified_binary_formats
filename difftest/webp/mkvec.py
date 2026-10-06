#!/usr/bin/env python3
"""Freeze a small differential test into vwebp/tests/data/vectors.txt, for
`cargo test -p vwebp` on a fresh clone (no libwebp or RFC 6386 decoder to
build). Needs build.sh's outputs and `cargo build --release -p vwebp-tool`.

Four kinds of input, each from the suites' own generators and checked by
their rules before it is kept:

* `vp8l`: bare lossless streams (wdiff.py's cwebp streams and
  mutants, gen.py's), decoded by the verified decoder (`batch`) and libwebp:
  kept where both refuse or both give the same image.
* `vp8`: bare lossy frames (ldiff.py's and mutants,
  gen8.py's), decoded by the verified decoder (`batch-vp8`) and RFC 6386's
  reference decoder: kept where the two agree (all, if the suites pass).
* `file`: lossless files (cdiff.py's shapes and mutants), through the verified container decoder (`batch-file`): kept
  where libwebp gives the same image, both refuse, or the difference is
  one of the kinds cdiff.py recognises (README: "Findings").
* `lossy`: lossy files with alpha (lfile.py's and mutants),
  through the verified decoder (`batch-lossy-file-v`): kept where libwebp
  gives the same image and alpha, or both refuse.

    difftest/webp/mkvec.py [-n N] [--seed S]

One line per input: `KIND NAME HEX RESULT`, HEX `-` if empty, and RESULT:
  vp8l   bad | W H STRICT BITS FNV(px as little-endian u32s)
  vp8    bad | W H FNV(Y, U, V)
  file   bad | toobig | lossy LIB | animated LIB | W H STRICT LIB FNV(px)
  lossy  bad | other | W H FNV(Y, U, V) FNV(alpha) or -
"""
import argparse, os, random, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wlib, llib, wdiff, gen, gen8, ldiff, cdiff, lfile

OUT = os.path.join(wlib.ROOT, "vwebp/tests/data/vectors.txt")
SMALL = 2500  # bytes: inputs kept are at most this long
L_LIMIT = 1 << 22  # pixels, as the suites (lossy files: 1 << 25)


def fnv(b):
    h = 0xcbf29ce484222325
    for x in b:
        h = ((h ^ x) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return "%016x" % h


def corpus():
    """libwebp-test-data's files are not ours to redistribute (it has no
    license), so the frozen vectors come from our generators only."""
    return []


def vp8l_cases(a, rng):
    recs = []
    for f, what in corpus():
        if f[12:16] == b"VP8L" and len(f) <= SMALL:
            recs.append((wlib.even(wdiff.vp8l(f)), what))
    for i in range(a.n):
        recs += [(wlib.even(s), w) for s, w in wdiff.encode((a.seed, i))]
        recs.append((wlib.even(gen.one((a.seed, i, 0.1))[0]), "gen"))
    recs = [r for r in recs if len(r[0]) <= SMALL]
    ours = wlib.run_ours([r[0] for r in recs], "batch", L_LIMIT)
    ref = wlib.run_libwebp([r[0] for r in recs], L_LIMIT)
    out = []
    for (s, what), x, y in zip(recs, ours, ref):
        if x == "skip" or not wlib.same(x, y):
            continue
        if x is None:
            out.append(("vp8l", what, s, "bad"))
        else:
            w, h, px, e = x
            out.append(("vp8l", what, s, "%d %d %d %d %s" % (w, h, e["strict"], e["bits"], fnv(px))))
    return out


def vp8_cases(a, rng):
    recs = []
    for f, what in corpus():
        fr = llib.vp8_payload(f)
        if fr is not None and len(fr) <= SMALL:
            recs.append((fr, what))
    for i in range(a.n):
        recs += [(s, w) for s, _, w in ldiff.encode((a.seed, i))]
        recs.append((gen8.frame(rng)[0], "gen8"))
    recs = [(llib.even(s), w) for s, w in recs if len(s) <= SMALL]
    frames = [r[0] for r in recs]
    rfc = [None if llib.too_big(s, L_LIMIT) else r for s, r in zip(frames, llib.run_rfc(frames))]
    ours = llib.run_ours(frames, "batch-vp8", L_LIMIT)
    out, fails = [], 0
    for (s, what), r, o in zip(recs, rfc, ours):
        if not llib.same(o, r):
            fails += 1
            continue
        if o is None:
            out.append(("vp8", what, s, "bad"))
        else:
            w, h, y, u, v, _ = o
            out.append(("vp8", what, s, "%d %d %s" % (w, h, fnv(y + u + v))))
    if fails:
        sys.exit("%d frames where the verified decoder and RFC 6386's differ: run ldiff.py" % fails)
    return out


def file_cases(a, rng):
    recs = []
    # not cdiff.lossy_payloads(): its lossy bodies come from libwebp-test-data
    for i in range(a.n):
        recs += [r for r in cdiff.build((a.seed, i)) if len(r[0]) <= SMALL]
    files = [r[0] for r in recs]
    ours = cdiff.run_files(files, L_LIMIT)
    ref = wlib.run_libwebp(files, L_LIMIT)
    out = []
    for (f, what), x, y in zip(recs, ours, ref):
        kind, img, lib, strict = x
        agree = (kind == "img" and y is not None and img == y[:3]) or (kind == "bad" and y is None) \
            or kind == "toobig" or cdiff.explain(f, x, y)
        if not agree:
            continue
        if kind == "img":
            w, h, px = img
            res = "%d %d %d %d %s" % (w, h, strict, lib, fnv(px))
        elif kind in ("lossy", "animated"):
            res = "%s %d" % (kind, lib)
        else:
            res = kind
        out.append(("file", what, f, res))
    return out


def lossy_cases(a, rng):
    recs = [(f, w) for f, w in corpus() if len(f) <= SMALL]
    for i in range(a.n):
        recs += [r for r in lfile.encode((a.seed, i)) if len(r[0]) <= SMALL]
    files = [r[0] for r in recs]
    ours = lfile.run_ours(files, 1 << 25, "batch-lossy-file-v")
    lib = llib.run_libwebp(files, 1 << 25)
    out = []
    for (f, what), o, l in zip(recs, ours, lib):
        if o == "other":
            out.append(("lossy", what, f, "other"))
        elif o is None and l is None:
            out.append(("lossy", what, f, "bad"))
        elif o is not None and lfile.same(o, l):
            w, h, y, u, v, e = o
            out.append(("lossy", what, f, "%d %d %s %s" % (w, h, fnv(y + u + v), fnv(e["alpha"]) if e["alpha"] else "-")))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=50)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    rows = vp8l_cases(a, rng) + vp8_cases(a, rng) + file_cases(a, rng) + lossy_cases(a, rng)
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        fh.write("# difftest/webp/mkvec.py -n %d --seed %d: KIND NAME HEX RESULT (see mkvec.py)\n" % (a.n, a.seed))
        for kind, what, s, res in rows:
            name = "".join(c if c.isalnum() or c in "._-" else "_" for c in what.split(" img")[0])[:40] or "_"
            fh.write("%s %s %s %s\n" % (kind, name, s.hex() or "-", res))
    stats = {}
    for kind, _, _, res in rows:
        k = (kind, res.split()[0] if res.split()[0] in ("bad", "toobig", "lossy", "animated", "other") else "image")
        stats[k] = stats.get(k, 0) + 1
    for k, v in sorted(stats.items()):
        print(" ".join(k), v)
    print("%d vectors, %d bytes -> %s" % (len(rows), os.path.getsize(OUT), OUT))


if __name__ == "__main__":
    main()
