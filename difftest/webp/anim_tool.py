"""Run files through `vwebp-tool batch-anim` (the verified animation
decoder), with results in animmodel.anim's form."""
import os
import struct
import subprocess

import wlib


def run(files, limit):
    data = b"".join(struct.pack("<I", len(x)) + x for x in files)
    env = dict(os.environ, VW_LIMIT=str(limit))
    out = subprocess.run([wlib.TOOL, "batch-anim"], input=data, stdout=subprocess.PIPE, check=True, env=env).stdout
    res, i = [], 0
    for _ in files:
        st, lib = out[i], out[i + 1]
        i += 2
        if st == 0 or st == 5:
            res.append(None if st == 0 else "toobig")
        elif st == 3:
            res.append("lossy")
        else:
            cw, ch, loops, bg, n = struct.unpack_from("<5I", out, i)
            i += 20
            frames = []
            for _ in range(n):
                ts = struct.unpack_from("<Q", out, i)[0]
                px = list(struct.unpack_from("<%dI" % (cw * ch), out, i + 8))
                i += 8 + 4 * cw * ch
                frames.append((ts, px))
            res.append((cw, ch, loops, bg, frames, bool(lib)))
    assert i == len(out)
    return res
