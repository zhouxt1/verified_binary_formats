"""Extract the VP8 reference decoder (RFC 6386 section 20, "Attachment One")
from the RFC text into build/rfc/: one file per subsection, code blocks
only, with the RFC's page breaks (footer, form feed, header) removed.

RFC 6386 section 1: "The bitstream is defined by the reference source code
and not this narrative." So this decoder is the lossy spec's primary oracle.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RFC = os.path.join(HERE, "..", "..", "..", "docs", "spec", "rfc6386.txt")
OUT = os.path.join(HERE, "..", "build", "rfc")

lines = open(RFC, encoding="latin-1").read().split("\n")
start = next(i for i, l in enumerate(lines) if l.startswith("20.  Attachment One"))
end = next(i for i, l in enumerate(lines) if l.startswith("20.25.  AUTHORS"))
os.makedirs(OUT, exist_ok=True)
name, code, inblock, files, skip = None, [], False, {}, False
for l in lines[start:end]:
    m = re.match(r"^20\.\d+\.  (\S+)$", l)
    if m:
        name = m.group(1)
        files[name] = []
        continue
    if "---- Begin code block" in l:
        inblock = True
        continue
    if "---- End code block" in l:
        inblock = False
        continue
    if not inblock or name is None:
        continue
    # A page break: drop the footer, form feed and header, and the blank
    # lines padding them (a break can fall inside a macro's continuation).
    if l.startswith("Bankoski, et al."):
        while files[name] and not files[name][-1].strip():
            files[name].pop()
        skip = True
        continue
    if l.startswith("RFC 6386 ") or l.startswith("\f"):
        continue
    if skip and not l.strip():
        continue
    skip = False
    files[name].append(l[3:] if l.startswith("   ") else l.lstrip())
for n, body in files.items():
    with open(os.path.join(OUT, n), "w") as f:
        f.write("\n".join(body) + "\n")
print(len(files), "files ->", os.path.relpath(OUT))
