#!/usr/bin/env python3
"""Check vbrotli's static dictionary (vbrotli/data/dictionary.bin) byte for
byte against RFC 7932 Appendix A and its CRC-32, and against Google's
dictionary.bin in build/brotli (from build.sh). Fetches the RFC's text into
build/ if it is not there."""
import os, re, sys, urllib.request, zlib

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
rfc = os.path.join(HERE, 'build', 'rfc7932.txt')
if not os.path.exists(rfc):
    os.makedirs(os.path.dirname(rfc), exist_ok=True)
    urllib.request.urlretrieve('https://www.rfc-editor.org/rfc/rfc7932.txt', rfc)
t = open(rfc).read()
a = t[t.rindex('Appendix A.  Static Dictionary Data'):t.rindex('Appendix B.  List of Word')]
a = a[a.index('0x5136cb04.') + 11:a.index('The number of words for each length')]
d = bytes.fromhex(''.join(re.findall(r'^\s+([0-9a-f]{2,64})\s*$', a, re.M)))
ours = open(os.path.join(ROOT, 'vbrotli', 'data', 'dictionary.bin'), 'rb').read()
google = open(os.path.join(HERE, 'build', 'brotli', 'c', 'common', 'dictionary.bin'), 'rb').read()
ok = len(d) == 122784 and zlib.crc32(d) == 0x5136cb04 and ours == d and google == d
print(f'RFC Appendix A: {len(d)} bytes, CRC-32 {zlib.crc32(d):#010x}; vbrotli\'s '
      f'{"matches" if ours == d else "DIFFERS"}; Google\'s {"matches" if google == d else "DIFFERS"}')
sys.exit(0 if ok else 1)
