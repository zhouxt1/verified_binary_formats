# per-instruction self cost from a callgrind --dump-instr=yes file, joined with objdump
import sys, re, subprocess, collections
f, binary, fnpat = sys.argv[1], sys.argv[2], sys.argv[3]
cost = collections.Counter()
last = [0, 0]
skip = False
for line in open(f):
    line = line.rstrip('\n')
    if not line: continue
    if line.startswith('calls='):
        skip = True; continue
    c0 = line[0]
    if c0.isdigit() or c0 in '+-*' or line.startswith('0x'):
        toks = line.split()
        pos = []
        for i, t in enumerate(toks[:2]):
            if t == '*': v = last[i]
            elif t.startswith('0x'): v = int(t, 16)
            elif t[0] in '+-': v = last[i] + int(t)
            else: v = int(t)
            pos.append(v)
        last[0], last[1] = pos[0], pos[1]
        ev = int(toks[2]) if len(toks) > 2 else 0
        if skip: skip = False; continue
        cost[pos[0]] += ev
dis = subprocess.run(['objdump', '-d', '--no-show-raw-insn', '-C', binary], capture_output=True, text=True).stdout
cur = None; rows = []
for l in dis.splitlines():
    m = re.match(r'^([0-9a-f]+) <(.*)>:', l)
    if m: cur = m.group(2); continue
    m = re.match(r'^\s+([0-9a-f]+):\s+(.*)', l)
    if m and cur and re.search(fnpat, cur):
        a = int(m.group(1), 16)
        rows.append((a, cost.get(a, 0), m.group(2)))
thr = int(sys.argv[4]) if len(sys.argv) > 4 else 100000
for a, c, t in rows:
    if c >= thr or '--all' in sys.argv:
        print(f'{c:>10} {a:x} {t}')
