"""Shared by the lossy (VP8) differential tests: find the VP8 frame in a
WebP file, run records through the decoders' batch protocols, and compare
the decoded planes.

Decoders: `build/rfc/rdec` (RFC 6386's reference decoder; one bare VP8
frame per record), `build/ydec` (libwebp; a WebP file per record) and
`vwebp-tool batch-vp8*` (ours; a bare VP8 frame per record). `run_*`
return one result per input:
  None                        no image (an error)
  'skip'                      (rdec) not a key frame
  'crash'                     (rdec) the reference decoder crashed
  (w, h, y, u, v, extra)      the planes as bytes, row by row
"""
import collections
import os
import struct
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
TOOL = os.path.join(ROOT, "target", "release", "vwebp-tool")

def _table(name, n):
    """A table from vwebp-tool/src/vp8tab.rs (generated from RFC 6386)."""
    import re
    src = open(os.path.join(ROOT, "vwebp-tool", "src", "vp8tab.rs")).read()
    body = re.search(name + r": \[u8; %d\] = \[(.*?)\];" % n, src, re.S).group(1)
    return [int(x) for x in body.replace("\n", " ").split(",") if x.strip()]


COEFF_UPDATE_PROBS = _table("COEFF_UPDATE_PROBS", 1056)
RDEC = os.path.join(HERE, "build", "rfc", "rdec")
YDEC = os.path.join(HERE, "build", "ydec")
FFYDEC = os.path.join(HERE, "build", "ffydec")


def vp8_payload(f):
    """The payload of the first "VP8 " chunk of a WebP file (walking
    chunks by their sizes), or None."""
    if len(f) < 12 or f[:4] != b"RIFF" or f[8:12] != b"WEBP":
        return None
    i = 12
    while i + 8 <= len(f):
        tag = f[i:i + 4]
        n = struct.unpack_from("<I", f, i + 4)[0]
        if tag == b"VP8 ":
            return f[i + 8:i + 8 + n]
        i += 8 + n + (n & 1)
    return None


def riff(vp8):
    """A bare VP8 frame in a simple lossy WebP file (RFC 9649 2.5)."""
    pad = b"\0" if len(vp8) & 1 else b""
    return (b"RIFF" + struct.pack("<I", 4 + 8 + len(vp8) + len(pad)) + b"WEBP" +
            b"VP8 " + struct.pack("<I", len(vp8)) + vp8 + pad)


def too_big(frame, limit):
    """The frame header says more than `limit` pixels (as VW_LIMIT, wdec -n)."""
    if len(frame) < 10:
        return False
    raw = struct.unpack_from("<I", frame, 6)[0]
    return (raw & 0x3fff) * ((raw >> 16) & 0x3fff) > limit


def _run(cmd, inputs, env=None):
    data = b"".join(struct.pack("<I", len(x)) + x for x in inputs)
    return subprocess.run(cmd, input=data, stdout=subprocess.PIPE, check=True, env=env).stdout


def _planes(out, i, w, h):
    cw, ch = (w + 1) // 2, (h + 1) // 2
    y = out[i:i + w * h]; i += w * h
    u = out[i:i + cw * ch]; i += cw * ch
    v = out[i:i + cw * ch]; i += cw * ch
    return y, u, v, i


def run_rfc(frames):
    out = _run([RDEC], frames)
    res, i = [], 0
    for _ in frames:
        st, code = struct.unpack_from("<Bi", out, i)
        i += 5
        if st == 2:
            res.append("skip")
        elif st == 3:
            res.append("crash")
        elif st == 0:
            res.append(None)
        else:
            w, h = struct.unpack_from("<II", out, i)
            i += 8
            y, u, v, i = _planes(out, i, w, h)
            res.append((w, h, y, u, v, {"code": code}))
    assert i == len(out)
    return res


def run_ffmpeg(frames):
    """FFmpeg's VP8 decoder (its harness is not in this release) on bare frames, as run_rfc."""
    out = _run([FFYDEC], frames)
    res, i = [], 0
    for _ in frames:
        st, code = struct.unpack_from("<Bi", out, i)
        i += 5
        if not st:
            res.append(None)
            continue
        w, h = struct.unpack_from("<II", out, i)
        i += 8
        y, u, v, i = _planes(out, i, w, h)
        res.append((w, h, y, u, v, {"code": code}))
    assert i == len(out)
    return res


def run_libwebp(files, limit=None):
    out = _run([YDEC] + (["-n", str(limit)] if limit else []), files)
    res, i = [], 0
    for _ in files:
        st, code = struct.unpack_from("<Bi", out, i)
        i += 5
        if st == 0:
            res.append(None)
            continue
        w, h, alpha = struct.unpack_from("<IIB", out, i)
        i += 9
        y, u, v, i = _planes(out, i, w, h)
        a = None
        if alpha:
            a = out[i:i + w * h]
            i += w * h
        res.append((w, h, y, u, v, {"code": code, "alpha": a}))
    assert i == len(out)
    return res


def run_ours(frames, tool="batch-vp8-spec", limit=None):
    env = dict(os.environ, **({"VW_LIMIT": str(limit)} if limit else {}))
    out = _run([TOOL, tool], frames, env)
    res, i = [], 0
    for _ in frames:
        st = out[i]
        i += 1
        if st == 0:
            res.append(None)
            continue
        w, h, lib = struct.unpack_from("<IIB", out, i)
        i += 9
        y, u, v, i = _planes(out, i, w, h)
        res.append((w, h, y, u, v, {"lib": bool(lib)}))
    assert i == len(out)
    return res


def notes(frames):
    """The spec's notes (vp8spec::Notes) for each frame, one line each."""
    out = _run([TOOL, "vp8-notes"], frames).decode().splitlines()
    assert len(out) == len(frames)
    return out


def same(a, b):
    """Two results agree: both None, or the same size and planes."""
    if a is None or b is None or isinstance(a, str) or isinstance(b, str):
        return a == b
    return a[:5] == b[:5]


def describe(r):
    if r is None or isinstance(r, str):
        return str(r)
    return "%dx%d" % (r[0], r[1])


def first_diff(a, b):
    """Where two same-size results first differ: (plane, x, y)."""
    w = a[0]
    for name, k, pw in (("Y", 2, w), ("U", 3, (w + 1) // 2), ("V", 4, (w + 1) // 2)):
        if a[k] != b[k]:
            j = next(j for j in range(len(a[k])) if a[k][j] != b[k][j])
            return name, j % pw, j // pw
    return None


def even(frame):
    """A frame of even length: a zero byte appended to an odd one.

    libwebp's VP8 decoder, like its VP8L decoder, takes the rest of the
    input as the frame (io.data_size in DecodeInto), not the chunk size:
    its last token partition runs on into the RIFF padding byte of an
    odd-sized chunk and any chunks after it. So the bitstream tests give
    all decoders the same even-length frame, which needs no padding. The
    container behaviour is its own finding (see README)."""
    return frame + b"\0" if len(frame) & 1 else frame


def compare(recs, tool, limit, save, verbose, title):
    """Decode records (frame, file, what) by the reference decoder, ours
    (bare frames) and libwebp (files), print the failures and a summary,
    and return the number of failures: ours must agree with the reference
    decoder on every frame, and with libwebp where it sets `lib`. A record
    whose file is None gets the frame, made even (`even`), on its own in a
    simple lossy file, and the frame is made even for all three."""
    recs = [(even(s), riff(even(s)), what) if f is None else (s, f, what) for s, f, what in recs]
    frames = [r[0] for r in recs]
    # The reference decoder has no pixel limit: over the limit, count it as
    # refusing, as ours and libwebp do.
    rfc = [None if too_big(s, limit) else r for s, r in zip(frames, run_rfc(frames))]
    ours = run_ours(frames, tool, limit)
    lib = run_libwebp([r[1] for r in recs], limit)
    # FFmpeg, for information: how often it agrees with the reference
    # decoder, on the frames the reference decoder decodes.
    ff = run_ffmpeg(frames) if os.path.exists(FFYDEC) else None
    fails = 0
    kinds = collections.Counter()
    flagged = []  # (index, kind) where ours clears `lib`
    for k, ((s, f, what), r, o, l) in enumerate(zip(recs, rfc, ours, lib)):
        if not same(o, r):
            fails += 1
            d = first_diff(o, r) if o and r and o[:2] == r[:2] else None
            print("FAIL #%d (%s): ours %s, rfc %s%s" % (k, what, describe(o), describe(r),
                                                        " first diff %s" % (d,) if d else ""))
            if save:
                os.makedirs(save, exist_ok=True)
                open(os.path.join(save, "fail%d.vp8" % k), "wb").write(s)
        if what != "mutant" and not what.startswith("gen") and r is None:
            print("encoder output refused by the reference decoder?", what)
            fails += 1
        if o not in (None, "crash") and not isinstance(o, str):
            if o[5]["lib"] and not same(o, l):
                fails += 1
                print("FAIL #%d (%s): lib flag set, but libwebp %s" % (k, what, describe(l)))
                if save:
                    os.makedirs(save, exist_ok=True)
                    open(os.path.join(save, "lib%d.vp8" % k), "wb").write(s)
            if not o[5]["lib"]:
                flagged.append((k, "libwebp agrees" if same(o, l) else "libwebp differs"))
        if same(r, l):
            kinds["both refuse" if r is None else "same image"] += 1
        else:
            kind = ("rfc image, libwebp refuses" if l is None else "rfc refuses, libwebp image" if r is None
                    else "different sizes" if r[:2] != l[:2] else "different pixels")
            if kind == "rfc refuses, libwebp image":
                kind += " (%s)" % why_refused(s)
            kinds[kind] += 1
            if verbose:
                print("#%d %s (%s)" % (k, kind, what))
    why = collections.Counter()
    if flagged:
        out = notes([frames[k] for k, _ in flagged])
        for (k, agree), line in zip(flagged, out):
            fields = [f.strip() for f in line.split("{")[1].strip().rstrip("}").split(",")]
            names = [f.split(":")[0] for f in fields if f.endswith("true")]
            why["%s (%s)" % ("+".join(names), agree)] += 1
    for kv in sorted(why.items(), key=lambda kv: -kv[1]):
        print("  lib cleared: %-50s %d" % kv)
    if ff is not None:
        dec = [k for k, r in enumerate(rfc) if r is not None and not isinstance(r, str)]
        enc = [k for k in dec if recs[k][2] not in ("mutant",) and not recs[k][2].startswith("gen")]
        print("  ffmpeg agrees with rfc on %d of %d frames rfc decodes (%d of %d encoder outputs)" %
              (sum(same(ff[k], rfc[k]) for k in dec), len(dec), sum(same(ff[k], rfc[k]) for k in enc), len(enc)))
    print("%s: ours/rfc/lib %d FAIL; rfc/libwebp: %s" %
          (title, fails, ", ".join("%s %d" % kv for kv in sorted(kinds.items()))))
    return fails


def why_refused(frame):
    """Why RFC 6386's reference decoder refuses a frame libwebp decodes:
    'reserved' (the color space or clamping type bit is set: dixie supports
    neither, libwebp ignores both), 'partition sizes' (a token partition's
    size is past the frame's end: dixie refuses, libwebp cuts it to what is
    left), or 'other'."""
    if len(frame) < 11:
        return "other"
    p0 = (frame[0] | frame[1] << 8 | frame[2] << 16) >> 5
    b = frame[10:10 + p0]
    if len(b) >= 2:
        # The first two bools of the first partition, at probability 128.
        value, rng, bits = b[0] << 8 | b[1], 255, []
        for _ in range(2):
            split = 1 + (((rng - 1) * 128) >> 8)
            if value >= split << 8:
                bits.append(1); rng -= split; value -= split << 8
            else:
                bits.append(0); rng = split
            while rng < 128:
                value <<= 1; rng <<= 1
        if any(bits):
            return "reserved"
    return "partition sizes" if len(frame) > 10 + p0 else "other"
