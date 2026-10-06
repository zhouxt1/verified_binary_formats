"""The lossy corpus: every WebP file in libwebp-test-data with a VP8 frame,
decoded by RFC 6386's reference decoder (on the bare frame), libwebp (on
the file) and, with --tool, ours (on the bare frame). Differences are
listed; the exit status is 1 if ours disagrees with the reference decoder
or with libwebp where both accept.

  python3 lcorpus.py [--tool batch-vp8-spec|batch-vp8|none]
"""
import argparse
import glob
import os
import sys

import llib

ap = argparse.ArgumentParser()
ap.add_argument("--tool", default="batch-vp8-spec")
ap.add_argument("-v", action="store_true")
args = ap.parse_args()

names, files, frames = [], [], []
for p in sorted(glob.glob(os.path.join(llib.HERE, "build", "test-data", "*.webp"))):
    f = open(p, "rb").read()
    fr = llib.vp8_payload(f)
    if fr is None:
        continue
    names.append(os.path.basename(p)); files.append(f); frames.append(fr)
rfc = llib.run_rfc(frames)
lib = llib.run_libwebp(files)
ours = llib.run_ours(frames, args.tool) if args.tool != "none" else [None] * len(frames)
bad = 0
rl = 0
for n, r, l, o in zip(names, rfc, lib, ours):
    notes = []
    if not llib.same(r, l):
        rl += 1
        d = llib.first_diff(r, l) if r and l and r[:2] == l[:2] else None
        notes.append("rfc %s vs libwebp %s%s" % (llib.describe(r), llib.describe(l), " first diff %s" % (d,) if d else ""))
    if args.tool != "none":
        if not llib.same(o, r):
            bad += 1
            d = llib.first_diff(o, r) if o and r and o[:2] == r[:2] else None
            notes.append("OURS %s vs rfc %s%s" % (llib.describe(o), llib.describe(r), " first diff %s" % (d,) if d else ""))
    if notes or args.v:
        print(n, "; ".join(notes) or "ok", llib.describe(r))
print("lcorpus: %d frames, rfc/libwebp differ on %d, ours/rfc differ on %d" % (len(frames), rl, bad))
sys.exit(1 if bad else 0)
