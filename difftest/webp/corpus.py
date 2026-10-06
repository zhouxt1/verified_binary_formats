#!/usr/bin/env python3
"""Every WebP file of libwebp-test-data (build/test-data), and any files or
directories given, through our decoder and libwebp's: images compared pixel
by pixel. Files that are not VP8L images (lossy, ALPH, animations) are
counted and skipped."""
import glob
import os
import sys

import wlib


def main():
    tool = "batch-spec"
    args = sys.argv[1:]
    if args[:1] == ["--tool"]:
        tool, args = args[1], args[2:]
    paths = []
    for a in args or [os.path.join(wlib.HERE, "build", "test-data")]:
        paths += sorted(glob.glob(os.path.join(a, "*.webp"))) if os.path.isdir(a) else [a]
    inputs = [open(p, "rb").read() for p in paths]
    ours = wlib.run_ours(inputs, tool)
    ref = wlib.run_libwebp(inputs)
    fails = skipped = ok = rejected = 0
    for p, a, b in zip(paths, ours, ref):
        if a == "skip":
            skipped += 1
        elif wlib.same(a, b):
            ok += 1
            rejected += a is None
            if a is not None and not a[3]["strict"]:
                print("lenient  %s: %s" % (os.path.basename(p), wlib.describe(a)))
        else:
            fails += 1
            print("FAIL %s: ours %s, libwebp %s" % (os.path.basename(p), wlib.describe(a), wlib.describe(b)))
            if a is not None and b is not None and a[:2] == b[:2]:
                print("     first differing pixel (index, ours, libwebp):", wlib.first_diff(a, b))
    print("%d files: %d agree (%d both refuse), %d skipped (not VP8L), %d FAIL" %
          (len(paths), ok, rejected, skipped, fails))
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
