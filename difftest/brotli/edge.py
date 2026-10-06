#!/usr/bin/env python3
"""Hand-built Brotli streams at the rules Google's encoder never exercises
(metadata, fill bits, reserved bits, WBITS patterns, length nibbles, simple
prefix codes, dictionary references), each with RFC 7932's verdict. The spec
(`vbrotli-tool batch-spec`, or --tool) and Google's decoder (build/gdec) must
both give it.
"""
import argparse, os, struct, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bdiff import Proc, GDEC, TOOL, ROOT

DICT = open(os.path.join(ROOT, 'vbrotli', 'data', 'dictionary.bin'), 'rb').read()


class W:
    """An LSB-first bit writer."""

    def __init__(self):
        self.bits = []

    def put(self, v, n):  # an integer, least significant bit first
        self.bits += [(v >> i) & 1 for i in range(n)]
        return self

    def fill(self, v=0):  # to the next byte boundary
        while len(self.bits) % 8:
            self.bits.append(v)
        return self

    def raw(self, bs):
        assert len(self.bits) % 8 == 0
        for x in bs:
            self.put(x, 8)
        return self

    def bytes(self):
        b = self.bits + [0] * (-len(self.bits) % 8)
        return bytes(sum(b[i + j] << j for j in range(8)) for i in range(0, len(b), 8))


def last_empty(w):
    return w.put(1, 1).put(1, 1)  # ISLAST, ISLASTEMPTY


def simple1(w, sym, abits):
    """A simple prefix code of one symbol: HSKIP 1, NSYM-1 0, the symbol."""
    return w.put(1, 2).put(0, 2).put(sym, abits)


def mb_compressed(w, mlen, cmd, lit=0x41, dist=0, last=True, extra=None, lit_code=None):
    """A compressed meta-block whose codes are all single symbols (no bits
    per symbol): one block type, no context map, literal `lit`, command
    `cmd`, distance symbol `dist`; `extra` writes the command's extra bits."""
    if last:
        w.put(1, 1).put(0, 1)
    else:
        w.put(0, 1)
    w.put(0, 2).put(mlen - 1, 16)  # MNIBBLES 4
    if not last:
        w.put(0, 1)  # ISUNCOMPRESSED
    w.put(0, 1).put(0, 1).put(0, 1)  # NBLTYPESL, I, D = 1
    w.put(0, 2).put(0, 4)  # NPOSTFIX, NDIRECT
    w.put(0, 2)  # context mode of the one literal block type
    w.put(0, 1).put(0, 1)  # NTREESL, NTREESD = 1
    if lit_code:
        lit_code(w)
    else:
        simple1(w, lit, 8)
    simple1(w, cmd, 10)
    simple1(w, dist, 6)
    if extra:
        extra(w)
    return w


def cases():
    c = []

    def add(name, data, valid, out=None):
        c.append((name, data, valid, out))

    add('empty stream (WBITS 16, last and empty)', last_empty(W().put(0, 1)).bytes(), True, b'')
    add('empty stream, fill bits not zero', last_empty(W().put(0, 1)).fill(1).bytes(), False)
    for pat, v in [('0100001', 10), ('1110001', 15), ('0000001', 17), ('0011', 18), ('1111', 24)]:
        w = W()
        for ch in reversed(pat):
            w.put(int(ch), 1)
        add(f'WBITS {v} ({pat})', last_empty(w).bytes(), True, b'')
    w = W()
    for ch in reversed('0010001'):
        w.put(int(ch), 1)
    add('WBITS pattern 0010001 (invalid; large-window marker)', last_empty(w).bytes(), False)

    def metadata(w, n, reserved=0, fillv=0, nbytes=1, top_zero=False, last=False):
        if last:
            w.put(1, 1).put(0, 1)
        else:
            w.put(0, 1)
        w.put(3, 2).put(reserved, 1).put(nbytes, 2)
        if nbytes:
            w.put(n - 1, 8 * nbytes)  # with nbytes 2 and n <= 256, the last byte is zero
        return w.fill(fillv).raw(bytes(i % 256 for i in range(n)))

    add('metadata of 5 bytes, then last empty', last_empty(metadata(W().put(0, 1), 5)).bytes(), True, b'')
    add('metadata, MSKIPBYTES 0', last_empty(W().put(0, 1).put(0, 1).put(3, 2).put(0, 1).put(0, 2).fill()).bytes(),
        True, b'')
    add('metadata, reserved bit set', last_empty(metadata(W().put(0, 1), 5, reserved=1)).bytes(), False)
    add('metadata, fill bits not zero', last_empty(metadata(W().put(0, 1), 5, fillv=1)).bytes(), False)
    add('metadata, 2 length bytes, the last zero',
        last_empty(metadata(W().put(0, 1), 5, nbytes=2, top_zero=True)).bytes(), False)
    add('metadata, 2 length bytes, the last not zero',
        last_empty(metadata(W().put(0, 1), 300, nbytes=2)).bytes(), True, b'')
    add('metadata as the last meta-block', metadata(W().put(0, 1), 3, last=True).bytes(), True, b'')
    add('metadata cut short', metadata(W().put(0, 1), 5).bytes()[:-2], False)

    def unc(w, data, fillv=0):
        w.put(0, 1).put(0, 2).put(len(data) - 1, 16).put(1, 1)
        return w.fill(fillv).raw(data)

    add('uncompressed meta-block', last_empty(unc(W().put(0, 1), b'hello')).bytes(), True, b'hello')
    add('uncompressed, fill bits not zero', last_empty(unc(W().put(0, 1), b'hello', 1)).bytes(), False)
    w = W().put(0, 1).put(0, 1).put(1, 2).put(4, 20).put(1, 1).fill().raw(b'hello')
    add('MNIBBLES 5, last nibble zero', last_empty(w).bytes(), False)
    w = W().put(0, 1).put(0, 1).put(1, 2).put(0x10004, 20).put(1, 1).fill().raw(b'x' * 0x10005)
    add('MNIBBLES 5, last nibble not zero', last_empty(w).bytes(), True, b'x' * 0x10005)

    # Compressed meta-blocks with single-symbol codes. Command 8: insert
    # code 1 (1 literal), copy code 0, last distance.
    add('one literal, compressed, last', mb_compressed(W().put(0, 1), 1, 8).bytes(), True, b'A')
    add('one literal, fill after the last not zero', mb_compressed(W().put(0, 1), 1, 8).fill(1).bytes(), False)
    # MLEN 3: after the literal, a copy of 2 from the last distance, 4, which
    # is past the output: a dictionary reference of length 2, which has no words.
    add('copy of 2 past the output (dictionary length 2)', mb_compressed(W().put(0, 1), 3, 8).bytes(), False)
    add('insert past MLEN', mb_compressed(W().put(0, 1), 1, 16).bytes(), False)  # insert 2 > 1

    # Command 130: cell 2 (explicit distance), insert 0, copy code 2 (4 bytes).
    # Distance symbol 0: the last distance, 4, past the empty output: word 3 of length 4.
    add('dictionary word 3 of length 4, from the first byte',
        mb_compressed(W().put(0, 1), 4, 130, dist=0).bytes(), True, DICT[12:16])
    add('dictionary word past MLEN', mb_compressed(W().put(0, 1), 3, 130, dist=0).bytes(), False)
    # Distance symbol 3: the fourth-to-last, 16: word 15.
    add('dictionary word 15 of length 4',
        mb_compressed(W().put(0, 1), 4, 130, dist=3).bytes(), True, DICT[60:64])
    # Command 128: copy code 0 (2 bytes) as a dictionary reference: length 2 has no words.
    add('dictionary reference of length 2', mb_compressed(W().put(0, 1), 2, 128, dist=0).bytes(), False)

    # Simple literal codes of two symbols.
    def lit2(a, b_):
        return lambda w: w.put(1, 2).put(1, 2).put(a, 8).put(b_, 8)

    add('simple code, two distinct symbols', mb_compressed(W().put(0, 1), 1, 8, lit_code=lit2(0x41, 0x42)).bytes(),
        True, b'A')
    add('simple code, a symbol repeated', mb_compressed(W().put(0, 1), 1, 8, lit_code=lit2(0x41, 0x41)).bytes(),
        False)
    add('simple command code, symbol 800 of 704', mb_compressed(W().put(0, 1), 1, 800).bytes(), False)
    return c


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tool', default='batch-spec')
    a = ap.parse_args()
    g = Proc([GDEC], 'g')
    t = Proc([TOOL, a.tool], 't')
    bad = 0
    for name, data, valid, out in cases():
        gr, tr = g.run(data), t.run(data)
        gv = gr[0] == 1 and gr[2] == len(data)
        tv = tr is not None and tr[1] and tr[0] == 8 * len(data)
        ok = gv == valid and tv == valid
        if valid and out is not None:
            ok = ok and gr[3] == out and tr[2] == out
        bad += not ok
        print(f'{"ok  " if ok else "FAIL"} rfc {"valid  " if valid else "invalid"} '
              f'google {"decodes" if gv else "refuses"} spec {"decodes" if tv else "refuses"}  {name}')
    print(f'{len(cases())} cases, {bad} failures')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
