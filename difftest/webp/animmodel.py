"""An executable model of the animation spec (to be vwebp/src/aspec.rs):
the ANIM and ANMF chunks of an extended file with the Animation flag
(RFC 9649 2.7.1.1), and canvas assembly as libwebp's WebPAnimDecoder does
it (src/demux/anim_decode.c), since the RFC's own is not exact ("MAY",
"SHOULD be done in linear color space").

`anim(f, frame_decode)` returns None (invalid), "lossy", or
(canvas_w, canvas_h, loop_count, bgcolor, [(timestamp, canvas pixels)], lib)
with canvas pixels a list of ARGB ints; `frame_decode(bytes)` is the VP8L
spec's image (w, h, pixels, alpha_hint) or None.

Where the RFC is explicit the model follows it; `lib` is False where
libwebp refuses such a file (reserved VP8X bits set, which its demuxer
rejects; a VP8X of other than 10 bytes, which WebPGetFeatures refuses).
Where the RFC is silent, libwebp:
  * the canvas starts transparent (0) and disposal clears to transparent;
    the ANIM background color is reported, not used ("MAY");
  * a frame's size is its bitstream's (the ANMF's width and height are
    only checked to have an area below 2^32);
  * the key-frame rule and the blend formula of anim_decode.c, including
    no blending inside the previous frame's rectangle after it was
    disposed to the background, and a frame's "has alpha" being its VP8L
    alpha hint.
Invalid, as the RFC: no ANIM before the first ANMF; an image chunk (ALPH,
VP8, VP8L) outside an ANMF; a second VP8X; an ANMF of less than 16 bytes or
without a bitstream chunk (libwebp drops such a frame: difference
"frameless"); ALPH before VP8L in a frame; no frames; a frame outside the
canvas; ANIM of less than 6 bytes. Chunks must fit the RIFF data, padding
included.
"""
import struct

ANMF, ANIM, VP8L, VP8, ALPH, VP8X = b"ANMF", b"ANIM", b"VP8L", b"VP8 ", b"ALPH", b"VP8X"


WHY = []


def fail(why):
    """Refuse, recording why (for triage)."""
    WHY.append(why)
    return None


def le(b, i, n):
    return int.from_bytes(b[i:i + n], "little")


def chunks(body, i, end):
    """(tag, payload start, payload end, next) of the chunks from i to end;
    None if one does not fit (payload and padding)."""
    out = []
    while i < end:
        if i + 8 > end:
            return fail("line 46: if i + 8 > end:")
        size = le(body, i + 4, 4)
        a, e = i + 8, i + 8 + size
        nxt = e + (size & 1)
        if nxt > end:
            return fail("line 51: if nxt > end:")
        out.append((body[i:i + 4], a, e, nxt))
        i = nxt
    return out


def blend(src, dst):
    """BlendPixelNonPremult."""
    sa = src >> 24
    if sa == 0:
        return dst
    da = dst >> 24
    dfa = (da * (256 - sa)) >> 8
    ba = sa + dfa
    scale = (1 << 24) // ba
    out = ba << 24
    for sh in (0, 8, 16):
        sc, dc = (src >> sh) & 255, (dst >> sh) & 255
        out |= ((((sc * sa + dc * dfa) * scale) & 0xffffffff) >> 24) << sh
    return out


def anim(f, frame_decode):
    if len(f) < 12 or f[:4] != b"RIFF" or f[8:12] != b"WEBP":
        return fail("line 75: if len(f) < 12 or f[:4] != b'RIFF' or f[8:12] != b'WEBP':")
    rs = le(f, 4, 4)
    if rs < 12 or rs > 0xfffffff6 or 8 + rs > len(f):
        return fail("line 78: if rs < 12 or rs > 0xfffffff6 or 8 + rs > len(f):")
    body = f[12:8 + rs]
    cl = chunks(body, 0, len(body))
    if not cl or cl[0][0] != VP8X or cl[0][2] - cl[0][1] < 10:
        return fail("line 82: if not cl or cl[0][0] != VP8X or cl[0][2] - cl[0][1] < 10:")
    _, a, e, _ = cl[0]
    flags = body[a]
    lib = (e - a == 10) and not (flags & ~0x3e & 0xff)
    cw, ch = le(body, a + 4, 3) + 1, le(body, a + 7, 3) + 1
    if cw * ch > 0xffffffff or not flags & 2:
        return fail("line 88: if cw * ch > 0xffffffff or not flags & 2:")
    bg = loops = None
    frames = []
    for tag, a, e, _ in cl[1:]:
        if tag == VP8X or tag in (ALPH, VP8, VP8L):
            return fail("line 93: if tag == VP8X or tag in (ALPH, VP8, VP8L):")
        if tag == ANIM:
            if e - a < 6:
                return fail("line 96: if e - a < 6:")
            if bg is None:
                bg, loops = le(body, a, 4), le(body, a + 4, 2)
        elif tag == ANMF:
            if bg is None or e - a < 16:
                return fail("line 101: if bg is None or e - a < 16:")
            fx, fy = 2 * le(body, a, 3), 2 * le(body, a + 3, 3)
            fw, fh = le(body, a + 6, 3) + 1, le(body, a + 9, 3) + 1
            dur, bits = le(body, a + 12, 3), body[a + 15]
            if fw * fh > 0xffffffff:
                return fail("line 106: if fw * fh > 0xffffffff:")
            sub = chunks(body, a + 16, e + ((e - a) & 1))
            if not sub:
                return fail("line 109: if not sub:")
            img = None
            k = 0
            if sub[0][0] == ALPH:
                k = 1
                if len(sub) < 2 or sub[1][0] == VP8L:
                    return fail("line 115: if len(sub) < 2 or sub[1][0] == VP8L:")
            if k >= len(sub) or sub[k][0] not in (VP8, VP8L):
                return fail("line 117: if k >= len(sub) or sub[k][0] not in (VP8, VP8L):")  # no bitstream chunk
            if sub[k][0] == VP8:
                return "lossy"
            dec = frame_decode(body[sub[k][1]:sub[k][2]])
            if dec is None:
                return fail("line 122: if dec is None:")
            w, h, px, hint = dec
            if fx + w > cw or fy + h > ch:
                return fail("line 125: if fx + w > cw or fy + h > ch:")
            frames.append(dict(x=fx, y=fy, w=w, h=h, px=px, alpha=hint, dur=dur,
                               dispose_bg=bool(bits & 1), no_blend=bool(bits & 2)))
    if not frames:
        return fail("line 129: if not frames:")
    # canvas assembly (WebPAnimDecoderGetNext)
    out = []
    prev_disposed = [0] * (cw * ch)
    prev = None
    prev_key = False
    ts = 0
    for k, fr in enumerate(frames):
        full = fr["w"] == cw and fr["h"] == ch
        if k == 0:
            key = True
        elif (not fr["alpha"] or fr["no_blend"]) and full:
            key = True
        else:
            key = prev["dispose_bg"] and ((prev["w"] == cw and prev["h"] == ch) or prev_key)
        cur = [0] * (cw * ch) if key else list(prev_disposed)
        for y in range(fr["h"]):
            for x in range(fr["w"]):
                cur[(fr["y"] + y) * cw + fr["x"] + x] = fr["px"][y * fr["w"] + x]
        if k > 0 and not fr["no_blend"] and not key:
            for y in range(fr["h"]):
                cy = fr["y"] + y
                for x in range(fr["w"]):
                    cx = fr["x"] + x
                    if prev["dispose_bg"] and prev["y"] <= cy < prev["y"] + prev["h"] and \
                            prev["x"] <= cx < prev["x"] + prev["w"]:
                        continue  # inside the disposed rectangle: no blending
                    i = cy * cw + cx
                    if cur[i] >> 24 != 255:
                        cur[i] = blend(cur[i], prev_disposed[i])
        ts += fr["dur"]
        out.append((ts, cur))
        prev_disposed = list(cur)
        if fr["dispose_bg"]:
            for y in range(fr["h"]):
                for x in range(fr["w"]):
                    prev_disposed[(fr["y"] + y) * cw + fr["x"] + x] = 0
        prev, prev_key = fr, key
    return (cw, ch, loops, bg, out, lib)
