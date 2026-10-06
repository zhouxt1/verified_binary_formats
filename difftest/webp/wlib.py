"""Shared by the WebP differential tests: run records through a decoder
speaking the batch protocol, and compare results.

A decoder is `vwebp-tool batch-*` (ours) or `build/wdec` (libwebp). Both
read records (u32 length + bytes) on stdin; see their headers for the
replies. `run_*` return one result per input:
  None                 no image (an error)
  'skip'               not a VP8L image (ours only: lossy, ALPH, ...)
  (w, h, px_bytes, extra)   px_bytes: little-endian ARGB u32s, row by row
"""
import os
import struct
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
TOOL = os.path.join(ROOT, "target", "release", "vwebp-tool")
WDEC = os.path.join(HERE, "build", "wdec")


def _feed(cmd, inputs):
    data = b"".join(struct.pack("<I", len(x)) + x for x in inputs)
    r = subprocess.run(cmd, input=data, stdout=subprocess.PIPE, check=True)
    return r.stdout


def run_ours(inputs, tool="batch-spec", limit=None):
    env = dict(os.environ, **({"VW_LIMIT": str(limit)} if limit else {}))
    data = b"".join(struct.pack("<I", len(x)) + x for x in inputs)
    out = subprocess.run([TOOL, tool], input=data, stdout=subprocess.PIPE, check=True, env=env).stdout
    res, i = [], 0
    for _ in inputs:
        st = out[i]
        i += 1
        if st == 0:
            res.append(None)
        elif st == 2:
            res.append("skip")
        else:
            w, h, strict, bits = struct.unpack_from("<IIBQ", out, i)
            i += 17
            n = 4 * w * h
            res.append((w, h, out[i:i + n], {"strict": bool(strict), "bits": bits}))
            i += n
    assert i == len(out), "trailing output from " + tool
    return res


def even(vp8l):
    """A bare stream of even length: a zero byte appended to an odd one.

    libwebp's VP8L decoder reads past the end of its chunk (its bit reader
    gets the rest of the input, io.data_size in DecodeInto, not the chunk
    size): into the RIFF padding byte of an odd-sized chunk, the chunks
    after it, and bytes after the RIFF. So the bitstream tests give both
    decoders the same even-length stream, which needs no padding and has
    nothing after it. The container behaviour is its own finding (see
    README)."""
    return vp8l + b"\0" if len(vp8l) & 1 else vp8l


def riff(vp8l):
    """A bare VP8L bitstream in a simple lossless WebP file (RFC 9649 2.6).
    libwebp's API refuses any input shorter than a RIFF header (12 bytes),
    bare bitstream or not (ParseHeadersInternal), so bare streams are
    wrapped before they go to wdec."""
    pad = b"\0" if len(vp8l) & 1 else b""
    return (b"RIFF" + struct.pack("<I", 4 + 8 + len(vp8l) + len(pad)) + b"WEBP" +
            b"VP8L" + struct.pack("<I", len(vp8l)) + vp8l + pad)


def run_libwebp(inputs, limit=None):
    cmd = [WDEC] + (["-n", str(limit)] if limit else [])
    out = _feed(cmd, [x if x.startswith(b"RIFF") else riff(x) for x in inputs])
    res, i = [], 0
    for _ in inputs:
        st, code = struct.unpack_from("<Bi", out, i)
        i += 5
        if st == 0:
            res.append(None)
        else:
            w, h = struct.unpack_from("<II", out, i)
            i += 8
            n = 4 * w * h
            res.append((w, h, out[i:i + n], {"code": code}))
            i += n
    assert i == len(out), "trailing output from wdec"
    return res


def same(a, b):
    """Our result `a` and libwebp's `b` agree (a 'skip' agrees with anything)."""
    if a == "skip":
        return True
    if a is None or b is None:
        return a is None and b is None
    return a[:3] == b[:3]


def describe(r):
    if r is None:
        return "error"
    if r == "skip":
        return "skip"
    w, h, px, extra = r
    return "%dx%d %s" % (w, h, " ".join("%s=%s" % kv for kv in sorted(extra.items())))


def first_diff(a, b):
    """Index of the first differing pixel of two results with images."""
    for k in range(0, min(len(a[2]), len(b[2])), 4):
        if a[2][k:k + 4] != b[2][k:k + 4]:
            return k // 4, a[2][k:k + 4][::-1].hex(), b[2][k:k + 4][::-1].hex()
    return None
