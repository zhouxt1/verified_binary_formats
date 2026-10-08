"""Read a Verus VIR log (`--log vir-simple --log vir-option=no_span`) into
Python: S-expressions as nested lists, atoms as strings."""
import re

TOK = re.compile(r'\s*(?:(;;[^\n]*)|(\()|(\))|("(?:[^"\\]|\\.)*")|([^\s()"]+))')

def parse(text):
    """All top-level S-expressions in `text`."""
    out, stack = [], [[]]
    pos = 0
    n = len(text)
    while pos < n:
        m = TOK.match(text, pos)
        if not m:
            if text[pos:].strip() == "":
                break
            raise ValueError("bad VIR at %d: %r" % (pos, text[pos:pos + 40]))
        pos = m.end()
        comment, lp, rp, string, atom = m.groups()
        if comment is not None:
            continue
        if lp:
            stack.append([])
        elif rp:
            x = stack.pop()
            stack[-1].append(x)
        elif string is not None:
            stack[-1].append(string)
        elif atom is not None:
            stack[-1].append(atom)
    assert len(stack) == 1, "unbalanced VIR"
    return stack[0]

def kw(node, key):
    """The value after keyword `:key` in a node."""
    for i, x in enumerate(node):
        if x == ":" + key:
            return node[i + 1]
    raise KeyError(key)

def functions(items):
    """name -> Function node, for every (Function ...) item."""
    fs = {}
    for it in items:
        if isinstance(it, list) and it and it[0] == "Function":
            name = kw(it, "name")          # (Fun :path a::b::c)
            fs[name[2]] = it
    return fs

def calls(node, acc):
    """Every function path a node calls."""
    if isinstance(node, list):
        if node and node[0] == "CallTarget" and len(node) > 3 and node[1] == "Fun":
            acc.add(node[3][2])
        for x in node:
            calls(x, acc)
    return acc
