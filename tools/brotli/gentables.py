#!/usr/bin/env python3
"""Generate vbrotli/src/tables.rs from the text of RFC 7932.

Usage: gentables.py rfc7932.txt > vbrotli/src/tables.rs

Each table is emitted twice, as a spec sequence and as an exec constant,
with a lemma (by compute) that they are equal. The RFC's own check values
(the CRC-32s in 7.1 and Appendix B) are checked here.
"""
import re, sys, zlib

t = open(sys.argv[1]).read()
t = re.sub(r'\n\n\nAlakuijala & Szabadka.*?\n\x0c?\nRFC 7932 +Brotli +July 2016\n', '\n', t)
t = re.sub(r'.*Alakuijala & Szabadka.*\n|RFC 7932 +Brotli +July 2016\n', '', t)

def nums(name):
    """The numbers after `name :=`, up to the first line that is not numbers."""
    rest = t[t.index(name + ' :=') + len(name) + 3:].split('\n')
    v = []
    for line in rest:
        if line.strip() and not re.fullmatch(r'[\d,\s]+', line):
            break
        v += [int(x) for x in re.findall(r'\d+', line)]
    return v

lut = {n: nums(n) for n in ['Lut0', 'Lut1', 'Lut2']}
crc = {'Lut0': 0x8e91efb7, 'Lut1': 0xd01a32f4, 'Lut2': 0x0dd7a0d6}
for n, v in lut.items():
    assert len(v) == 256 and zlib.crc32(bytes(v)) == crc[n], n
ndbits = nums('NDBITS')
assert len(ndbits) == 25

# Appendix B
b = t[t.rindex('Appendix B.  List of Word Transformations'):t.rindex('Appendix C.  Computing')]
rows = re.findall(r'^\s+(\d+)\s+("(?:[^"\\]|\\.)*")\s+(\w+)\s+("(?:[^"\\]|\\.)*")\s*$', b, re.M)
assert [int(r[0]) for r in rows] == list(range(121)), len(rows)

def cstr(s):
    s = s[1:-1]
    out = bytearray(); i = 0
    while i < len(s):
        c = s[i]
        if c == '\\':
            d = s[i + 1]
            if d == 'x':
                out.append(int(s[i + 2:i + 4], 16)); i += 4; continue
            out.append({'n': 10, 't': 9, '"': 34, '\\': 92, "'": 39}[d]); i += 2; continue
        out.append(ord(c)); i += 1
    return bytes(out)

def ttype(name):
    if name == 'Identity': return 0
    if name == 'FermentFirst': return 1
    if name == 'FermentAll': return 2
    m = re.fullmatch(r'OmitFirst(\d)', name)
    if m: return 2 + int(m.group(1))
    m = re.fullmatch(r'OmitLast(\d)', name)
    return 11 + int(m.group(1))

pre = [cstr(r[1]) for r in rows]
typ = [ttype(r[2]) for r in rows]
suf = [cstr(r[3]) for r in rows]
ser = b''.join(p + b'\0' + bytes([ty]) + s + b'\0' for p, ty, s in zip(pre, typ, suf))
assert len(ser) == 648 and zlib.crc32(ser) == 0x3d965f81

def offs(parts):
    o = [0]
    for p in parts: o.append(o[-1] + len(p))
    return o

tables = [
    ('lut0', 'LUT0', 'u8', lut['Lut0'], 'Lut0 of 7.1 (the UTF8 context mode, from p1).'),
    ('lut1', 'LUT1', 'u8', lut['Lut1'], 'Lut1 of 7.1 (the UTF8 context mode, from p2).'),
    ('lut2', 'LUT2', 'u8', lut['Lut2'], 'Lut2 of 7.1 (the Signed context mode).'),
    ('ndbits', 'NDBITS', 'u8', ndbits, 'NDBITS of 8: log2 of the number of dictionary words of each length.'),
    ('tr_type', 'TR_TYPE', 'u8', typ,
     'The elementary transform of each of the 121 transforms (Appendix B): 0 Identity, 1 FermentFirst, 2 FermentAll, 3..11 OmitFirst1..9, 12..20 OmitLast1..9.'),
    ('tr_pre', 'TR_PRE', 'u8', list(b''.join(pre)), 'The prefixes of the 121 transforms, one after another (Appendix B).'),
    ('tr_pre_off', 'TR_PRE_OFF', 'u16', offs(pre), 'Where each prefix starts in `tr_pre`, and where the last ends.'),
    ('tr_suf', 'TR_SUF', 'u8', list(b''.join(suf)), 'The suffixes of the 121 transforms, one after another (Appendix B).'),
    ('tr_suf_off', 'TR_SUF_OFF', 'u16', offs(suf), 'Where each suffix starts in `tr_suf`, and where the last ends.'),
]

o = []
w = o.append
w('//! The tables of RFC 7932, generated from its text by')
w('//! `tools/brotli/gentables.py` (which checks the RFC\'s CRC-32s of them).')
w('//! Each is a spec sequence and an exec constant, proved equal.')
w('use vstd::prelude::*;')
w('')
w('verus! {')
w('')
for spec, ex, ty, v, doc in tables:
    body = ', '.join((f'{x}{ty}' if i == 0 else str(x)) for i, x in enumerate(v))
    w(f'/// {doc}')
    w(f'pub open spec fn {spec}() -> Seq<{ty}> {{')
    w(f'    seq![{body}]')
    w('}')
    w('')
    w(f'pub const {ex}: [{ty}; {len(v)}] = [{", ".join(map(str, v))}];')
    w('')
    w(f'pub proof fn lemma_{spec}()')
    w(f'    ensures {ex}@ == {spec}(), {spec}().len() == {len(v)},')
    w('{')
    w(f'    assert({ex}@ =~= {spec}()) by (compute);')
    w('}')
    w('')
w('} // verus!')
print('\n'.join(o))
