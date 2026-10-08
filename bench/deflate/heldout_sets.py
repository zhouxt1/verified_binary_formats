import os, shutil, struct, sys, zlib, hashlib
H = sys.argv[1]; D = os.path.join(H, "dl"); T = os.path.join(H, "sets")
def put(setname, name, data):
    d = os.path.join(T, setname); os.makedirs(d, exist_ok=True)
    open(os.path.join(d, name), "wb").write(data)
for sub in ("cant", "large"):
    for f in sorted(os.listdir(os.path.join(D, sub))):
        put("canterbury", f, open(os.path.join(D, sub, f), "rb").read())
put("enwik8", "enwik8", open(os.path.join(D, "enwik", "enwik8"), "rb").read())
for sub in ("zlib", "lua"):
    for root, _, fs in os.walk(os.path.join(D, sub)):
        for f in sorted(fs):
            p = os.path.join(root, f); data = open(p, "rb").read()
            if len(data) == 0: continue
            rel = os.path.relpath(p, os.path.join(D, sub)).replace("/", "__")
            put("source", sub + "__" + rel, data)
for f in sorted(os.listdir(os.path.join(D, "web"))):
    put("web", f, open(os.path.join(D, "web", f), "rb").read())
for f in sorted(os.listdir(os.path.join(D, "kodak"))):
    b = open(os.path.join(D, "kodak", f), "rb").read()
    assert b[:8] == b"\x89PNG\r\n\x1a\n"
    p = 8; idat = b""
    while p < len(b):
        n = struct.unpack(">I", b[p:p + 4])[0]; t = b[p + 4:p + 8]
        if t == b"IDAT": idat += b[p + 8:p + 8 + n]
        p += 12 + n
    put("png", f[:-4] + ".idat", zlib.decompress(idat))
with open(os.path.join(H, "MANIFEST.sha256"), "w") as m:
    for s in sorted(os.listdir(T)):
        for f in sorted(os.listdir(os.path.join(T, s))):
            data = open(os.path.join(T, s, f), "rb").read()
            m.write("%s  %s/%s  %d\n" % (hashlib.sha256(data).hexdigest(), s, f, len(data)))
for s in sorted(os.listdir(T)):
    fs = os.listdir(os.path.join(T, s))
    print(s, len(fs), "files", sum(os.path.getsize(os.path.join(T, s, f)) for f in fs), "bytes")
