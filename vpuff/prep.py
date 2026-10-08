"""Prepare a lean4export NDJSON file for rocq-lean-import.

usage: prep.py IN OUT ROOT...

1. Every theorem becomes an axiom with the same statement. Lean's kernel has
   checked the proofs; Rocq then checks the definitions and the statements.
   (Checking the proofs again would pull in Lean's string and UInt32 library
   through omega's lemmas, which the importer does not handle.)
2. `autoParam α tac` and `optParam α d` are replaced by `α`, which they are
   by definition. (An autoParam's tactic script is a `Lean.Syntax` value full
   of strings, and `Array.set`'s type has one.)
3. Only the declarations reachable from ROOT... are kept, in their order,
   with the names, levels and expressions they use.
"""
import json
import sys
from collections import deque

src, dst, roots = sys.argv[1], sys.argv[2], sys.argv[3:]
lines = open(src, encoding="utf-8").read().splitlines()

names, exprs = {}, {}
for l in lines:
    d = json.loads(l)
    if "in" in d:
        v = d.get("str") or d.get("num")
        pre = names.get(v["pre"], "") if v["pre"] else ""
        names[d["in"]] = (pre + "." if pre else "") + str(v.get("str", v.get("i")))
    elif "ie" in d:
        exprs[d["ie"]] = d

EXPR_KEYS = ("fn", "arg", "type", "body", "value", "expr", "struct")

# autoParam α x and optParam α x are α
sub = {}
for i, d in exprs.items():
    if "app" in d:
        f = exprs.get(d["app"]["fn"])
        if f and "app" in f:
            g = exprs.get(f["app"]["fn"])
            if g and "const" in g and names[g["const"]["name"]] in ("autoParam", "optParam"):
                sub[i] = f["app"]["arg"]


def R(i):
    while i in sub:
        i = sub[i]
    return i


for d in exprs.values():
    for k in ("app", "lam", "forallE", "letE", "proj", "mdata"):
        if k in d:
            v = d[k]
            for kk in ("fn", "arg", "type", "body", "value", "struct", "expr"):
                if kk in v:
                    v[kk] = R(v[kk])


def consts(roots_e):
    out, stack, seen = set(), list(roots_e), set()
    while stack:
        i = stack.pop()
        if i in seen or i not in exprs:
            continue
        seen.add(i)
        d = exprs[i]
        if "const" in d:
            out.add(names[d["const"]["name"]])
        for v in d.values():
            if isinstance(v, dict):
                for k, x in v.items():
                    if k in EXPR_KEYS and isinstance(x, int):
                        stack.append(x)
    return out


def decl_info(d, as_axiom):
    """(names declared, expressions it depends on)"""
    for k in ("def", "thm", "opaque", "axiom"):
        if k in d:
            x = d[k]
            es = [R(x["type"])] + ([R(x["value"])] if "value" in x and not (k == "thm" and as_axiom) else [])
            return [names[x["name"]]], es
    if "inductive" in d:
        ind = d["inductive"]
        ns, es = [], []
        for part in ("types", "ctors", "recs"):
            for x in ind.get(part, []):
                ns.append(names[x["name"]])
                es.append(R(x["type"]))
        return ns, es
    return [], []


decls = []
for idx, l in enumerate(lines):
    d = json.loads(l)
    ns, es = decl_info(d, True)
    if ns:
        decls.append((idx, ns, es))

owner = {}
for idx, ns, es in decls:
    for n in ns:
        owner[n] = idx
deps = {idx: consts(es) for idx, ns, es in decls}

keep = set()
q = deque(owner[r] for r in roots)
while q:
    i = q.popleft()
    if i in keep:
        continue
    keep.add(i)
    for n in deps[i]:
        if n in owner and owner[n] not in keep:
            q.append(owner[n])

declidx = {idx for idx, _, _ in decls}
levels = {}
for l in lines:
    d = json.loads(l)
    if "il" in d:
        levels[d["il"]] = d

out_lines, nthm = [], 0
for idx, l in enumerate(lines):
    if idx in declidx:
        if idx not in keep:
            continue
        d = json.loads(l)
        if "thm" in d:
            t = d["thm"]
            d = {"axiom": {"isUnsafe": False, "levelParams": t["levelParams"],
                           "name": t["name"], "type": t["type"]}}
            nthm += 1
        for k in ("def", "axiom", "opaque", "quot"):
            if k in d:
                for kk in ("type", "value"):
                    if kk in d[k]:
                        d[k][kk] = R(d[k][kk])
        if "inductive" in d:
            for part in ("types", "ctors", "recs"):
                for x in d["inductive"].get(part, []):
                    x["type"] = R(x["type"])
                    for r in x.get("rules", []):
                        r["rhs"] = R(r["rhs"])
        l = json.dumps(d)
    elif "ie" in json.loads(l):
        l = json.dumps(exprs[json.loads(l)["ie"]])
    out_lines.append(l)

# the names, levels and expressions the kept declarations use
used_n, used_l, used_e = set(), set(), set()
estack, lstack, nstack = [], [], []
for l in out_lines:
    d = json.loads(l)
    if any(k in d for k in ("in", "il", "ie", "meta")):
        continue
    vals = []
    for k in ("def", "axiom", "opaque", "quot"):
        if k in d:
            vals.append(d[k])
    if "inductive" in d:
        for part in ("types", "ctors", "recs"):
            vals.extend(d["inductive"].get(part, []))
    for x in vals:
        nstack.append(x["name"])
        nstack.extend(x.get("levelParams", []))
        nstack.extend(x.get("all", []))
        nstack.extend(x.get("ctors", []))
        if "induct" in x:
            nstack.append(x["induct"])
        for k in ("type", "value"):
            if k in x:
                estack.append(x[k])
        for r in x.get("rules", []):
            nstack.append(r["ctor"])
            estack.append(r["rhs"])
while estack or lstack:
    while estack:
        i = estack.pop()
        if i in used_e or i not in exprs:
            continue
        used_e.add(i)
        d = exprs[i]
        if "sort" in d:
            lstack.append(d["sort"])
        elif "const" in d:
            nstack.append(d["const"]["name"])
            lstack.extend(d["const"]["us"])
        else:
            for k in ("app", "lam", "forallE", "letE", "proj", "mdata"):
                if k in d:
                    v = d[k]
                    for kk in ("fn", "arg", "type", "body", "value", "struct", "expr"):
                        if kk in v:
                            estack.append(v[kk])
                    for kk in ("name", "typeName"):
                        if kk in v:
                            nstack.append(v[kk])
    while lstack:
        i = lstack.pop()
        if i in used_l or i not in levels:
            continue
        used_l.add(i)
        d = levels[i]
        if "succ" in d:
            lstack.append(d["succ"])
        for k in ("max", "imax"):
            if k in d:
                lstack.extend(d[k])
        if "param" in d:
            nstack.append(d["param"])
namedefs = {}
for l in lines:
    d = json.loads(l)
    if "in" in d:
        namedefs[d["in"]] = d
while nstack:
    i = nstack.pop()
    if i in used_n or i not in namedefs:
        continue
    used_n.add(i)
    v = namedefs[i].get("str") or namedefs[i].get("num")
    nstack.append(v["pre"])

# the importer wants dense ids: names and levels from 1 (0 is the anonymous name
# and the zero level), expressions from 0
kept = []
for l in out_lines:
    d = json.loads(l)
    if ("in" in d and d["in"] not in used_n) or ("il" in d and d["il"] not in used_l) \
            or ("ie" in d and d["ie"] not in used_e):
        continue
    kept.append(d)
nmap, lmap, emap = {0: 0}, {0: 0}, {}
for d in kept:
    if "in" in d:
        nmap[d["in"]] = len(nmap)
    elif "il" in d:
        lmap[d["il"]] = len(lmap)
    elif "ie" in d:
        emap[d["ie"]] = len(emap)


def N(i): return nmap[i]
def LV(i): return lmap[i]
def E(i): return emap[i]


def renum(d):
    if "meta" in d:
        return d
    if "in" in d:
        v = d.get("str") or d.get("num")
        v["pre"] = N(v["pre"])
        d["in"] = N(d["in"])
        return d
    if "il" in d:
        if "succ" in d: d["succ"] = LV(d["succ"])
        for k in ("max", "imax"):
            if k in d: d[k] = [LV(x) for x in d[k]]
        if "param" in d: d["param"] = N(d["param"])
        d["il"] = LV(d["il"])
        return d
    if "ie" in d:
        if "sort" in d: d["sort"] = LV(d["sort"])
        if "const" in d:
            d["const"]["name"] = N(d["const"]["name"])
            d["const"]["us"] = [LV(x) for x in d["const"]["us"]]
        for k in ("app", "lam", "forallE", "letE", "proj", "mdata"):
            if k in d:
                v = d[k]
                for kk in ("fn", "arg", "type", "body", "value", "struct", "expr"):
                    if kk in v: v[kk] = E(v[kk])
                for kk in ("name", "typeName"):
                    if kk in v: v[kk] = N(v[kk])
        d["ie"] = E(d["ie"])
        return d
    vals = [d[k] for k in ("def", "axiom", "opaque", "quot") if k in d]
    if "inductive" in d:
        for part in ("types", "ctors", "recs"):
            vals.extend(d["inductive"].get(part, []))
    for x in vals:
        x["name"] = N(x["name"])
        for k in ("levelParams", "all", "ctors"):
            if k in x: x[k] = [N(i) for i in x[k]]
        if "induct" in x: x["induct"] = N(x["induct"])
        for k in ("type", "value"):
            if k in x: x[k] = E(x[k])
        for r in x.get("rules", []):
            r["ctor"] = N(r["ctor"])
            r["rhs"] = E(r["rhs"])
    return d


with open(dst, "w", encoding="utf-8") as out:
    for d in kept:
        out.write(json.dumps(renum(d), ensure_ascii=False, separators=(",", ":")) + "\n")
print(f"{len(keep)} of {len(decls)} declarations kept, {nthm} theorems as axioms", file=sys.stderr)
