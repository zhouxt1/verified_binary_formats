#!/usr/bin/env python3
"""Translate Verus spec functions from VIR into Lean definitions, with proofs.

    vir2lean.py VIR_LOG ROOT_FN... [-o OUT.lean] [--hints H.lean] [--validate V.lean]

VIR_LOG is a `--log vir-simple --log vir-option=no_span` dump. Every spec function reachable
from the ROOT_FNs becomes a Lean definition over the shallow model (`Bridge/Vstd.lean`), with
its exact Rust path as its Lean name: `vdeflate::spec::inflate` becomes
`V.vdeflate.spec.inflate`. With --validate, it also writes, for each function, a proof that
the definition computes what the VIR semantics (`Lspec/VIR/Sem.lean`) gives the function's
VIR as Lean reads it (`vir_program`). So this translator is **not trusted**: if it
mistranslated a node, that proof would fail.

A node outside the fragment stops the translation with an error.
"""
import argparse, sys
import vir

# vstd function -> (model function, whether it takes `u` and the element type)
VSTD = {
    "vstd::seq::Seq::empty": ("VModel.Seq.empty", False),
    "vstd::seq::Seq::len": ("VModel.Seq.len", False),
    "vstd::seq::Seq::index": ("VModel.Seq.index", True),
    "vstd::seq::impl&%2::spec_index": ("VModel.Seq.index", True),
    "vstd::seq::Seq::push": ("VModel.Seq.push", False),
    "vstd::seq::Seq::update": ("VModel.Seq.update", True),
    "vstd::seq::Seq::subrange": ("VModel.Seq.subrange", False),
    "vstd::seq::Seq::add": ("VModel.Seq.add", False),
    "vstd::seq::impl&%2::spec_add": ("VModel.Seq.add", False),
    "vstd::seq::Seq::new": ("VModel.Seq.new", True),
    "vstd::seq::Seq::last": ("VModel.Seq.last", True),
    "vstd::seq_lib::impl&%0::drop_last": ("VModel.Seq.dropLast", False),
    "vstd::seq::impl&%2::skip": ("VModel.Seq.skip", False),
    "vstd::seq::impl&%2::take": ("VModel.Seq.take", False),
}

class Unsupported(Exception):
    pass

def fail(what, node):
    raise Unsupported("%s: %s" % (what, str(node)[:300]))

def unq(s):
    assert s.startswith('"') and s.endswith('"'), s
    return s[1:-1]

def lean_path(path):
    return "«" + path.replace("::", "».«") + "»"

# ------------------------------------------------------------------ types

def int_range(r):
    # (IntRange Int) | (IntRange Nat) | (IntRange U 8) | (IntRange I 8) | USize | ISize
    k = r[1]
    if k == "Int": return "VModel.IntRange.int"
    if k == "Nat": return "VModel.IntRange.nat"
    if k == "U": return "(VModel.IntRange.u %s)" % r[2]
    if k == "I": return "(VModel.IntRange.i %s)" % r[2]
    if k == "USize": return "VModel.IntRange.usize"
    if k == "ISize": return "VModel.IntRange.isize"
    fail("int range", r)

def overflow_range(ob):
    """The range `Truncate r`/`Error r` arithmetic is clipped to (ast_to_sst.rs), or None."""
    if ob == ["OverflowBehavior", "Allow"]:
        return None
    if ob[1] in ("Truncate", "Error"):
        r = int_range(ob[2])
        return None if r == "VModel.IntRange.int" else r
    fail("overflow behavior", ob)

INT_INT = "(VModel.VTy.int VModel.IntRange.int)"

def unsigned_range(t):
    """The range of an unsigned integer type, else None (bitwise operators need one)."""
    if t[0] == "Typ" and t[1] == "Int" and t[2][1] in ("U", "USize"):
        return int_range(t[2])
    return None

def nonneg_const(e):
    """A non-negative integer constant: (@@ (> Const (Constant Int n)) t)."""
    return (e[0] == "@@" and isinstance(e[1], list) and len(e[1]) == 3 and e[1][1] == "Const"
            and e[1][2][:2] == ["Constant", "Int"] and e[1][2][2].isdigit())

def bitwise(op, t, x, y, fn):
    """`&`/`>>`/`^` on unsigned operands, clipped to the result type as Verus does."""
    if op[3] != ["BitshiftBehavior", "Allow"] or op[2][1] not in ("BitAnd", "Shr", "BitXor"):
        fail("bitwise operator", op)
    r = unsigned_range(t)
    # the amount of a `>>` may also be a non-negative constant of a signed type (`c >> 1`)
    y_ok = unsigned_range(y[2]) is not None or (op[2][1] == "Shr" and nonneg_const(y))
    if r is None or unsigned_range(x[2]) is None or not y_ok:
        fail("bitwise operator on a signed or non-integer type", op)
    return fn({"BitAnd": "band", "Shr": "shr", "BitXor": "bxor"}[op[2][1]], r)

def ty(t):
    assert t[0] == "Typ", t
    k = t[1]
    if k == "Int":
        return "Int"
    if k == "Bool":
        return "Bool"
    if k == "Decorate":
        return ty(t[3])
    if k == "SpecFn":
        args, ret = t[2], t[3]
        return "(" + " → ".join([ty(a) for a in args] + [ty(ret)]) + ")"
    if k == "Datatype":
        dt, targs = t[2], t[3]
        if dt[1] == "Path" and dt[2] == "vstd::seq::Seq":
            return "(List %s)" % ty(targs[0])
        if dt[1] == "Path" and dt[2] == "core::option::Option":
            return "(Option %s)" % ty(targs[0])
        if dt[1] == "Tuple":
            n = int(dt[2])
            if n == 0:
                return "Unit"
            return "(" + " × ".join(ty(a) for a in targs) + ")"
    fail("type", t)

def vty(t):
    """The VModel.VTy code of a VIR type (see Lspec/VIR/Ty.lean)."""
    assert t[0] == "Typ", t
    k = t[1]
    if k == "Int":
        return "(VModel.VTy.int %s)" % int_range(t[2])
    if k == "Bool":
        return "VModel.VTy.bool"
    if k == "Decorate":
        return vty(t[3])
    if k == "Datatype":
        dt, targs = t[2], t[3]
        if dt[1] == "Path" and dt[2] == "vstd::seq::Seq":
            return "(VModel.VTy.seq %s)" % vty(targs[0])
        if dt[1] == "Path" and dt[2] == "core::option::Option":
            return "(VModel.VTy.opt %s)" % vty(targs[0])
        if dt[1] == "Tuple":
            return "(VModel.VTy.tup [%s])" % ", ".join(vty(a) for a in targs)
    fail("VIR type code", t)

# ------------------------------------------------------------ expressions

class Tr:
    def __init__(self):
        self.calls = set()
        self.fresh = 0

    def name(self, v):
        # (VarIdent "x" (VarIdentDisambiguate VirParam)) or ... VirTemp N, etc.
        assert v[0] == "VarIdent", v
        base = unq(v[1]).replace("%", "_")
        d = v[2] if len(v) > 2 else None
        suffix = ""
        if isinstance(d, list) and len(d) > 2:
            suffix = "_" + "_".join(str(x) for x in d[2:])
        if base == "tmp__":
            base = "tmp"
        return "«%s%s»" % (base, suffix)

    def place(self, p):
        ptyp = None
        if p[0] == "@@":
            ptyp = p[2]
            p = p[1]
        if p[0] != "Place":
            fail("place", p)
        k = p[1]
        if k == "Local":
            return self.name(p[2])
        if k == "Temporary":
            return self.ex(p[2])
        if k == "Field":
            fo, inner = p[2], p[3]
            dt = vir.kw(fo, "datatype")
            variant = unq(vir.kw(fo, "variant"))
            field = unq(vir.kw(fo, "field"))
            check = vir.kw(fo, "check")
            if check != ["VariantCheck", "None"]:
                fail("field check", fo)
            x = self.place(inner)
            if dt[1] == "Tuple":
                n, i = int(dt[2]), int(field)
                return "(%s)%s" % (x, ".2" * i + (".1" if i < n - 1 else ""))
            if dt[1] == "Path" and dt[2] == "core::option::Option" and variant == "Some" and field == "0":
                if ptyp is None:
                    fail("untyped field place", p)
                return "(VModel.someVal u %s (α := %s) rfl %s)" % (vty(ptyp), ty(ptyp), x)
            fail("field", fo)
        fail("place kind", p)

    def ex(self, node):
        """A typed expression (@@ (> Kind ...) Typ)."""
        if node[0] != "@@":
            fail("expected typed expression", node)
        e, t = node[1], node[2]
        if e[0] != ">":
            fail("expression", e)
        k = e[1]
        a = e[2:]
        if k == "Const":
            c = a[0]
            if c[1] == "Int":
                return "(%s : Int)" % c[2]
            if c[1] == "Bool":
                return c[2]
            fail("constant", c)
        if k == "ReadPlace":
            return self.place(a[0])
        if k == "Var":
            return self.name(a[0])
        if k == "Block":
            stmts, body = a[0], a[1]
            out = self.ex(body)
            for st in reversed(stmts):
                out = self.stmt(st, out)
            return out
        if k == "If":
            c, th, el = a[0], a[1], a[2]
            if el == "None":
                fail("if without else", e)
            self.fresh += 1
            return "(if h%d : %s = true then %s else %s)" % (self.fresh, self.ex(c), self.ex(th), self.ex(el))
        if k == "Call":
            tgt = vir.kw(e, "target")
            args = vir.kw(e, "args")
            if tgt[1] != "Fun":
                fail("call target", tgt)
            path = tgt[3][2]
            xs = [self.ex(x) for x in args]
            if path in VSTD:
                f, needs_u = VSTD[path]
                targs = tgt[4]
                pre = ""
                if needs_u:
                    if len(targs) != 1:
                        fail("vstd call without its element type", tgt)
                    pre = " u %s (α := %s) rfl" % (vty(targs[0]), ty(targs[0]))
                return "(%s%s %s)" % (f, pre, " ".join(xs))
            if path.startswith("vstd::"):
                fail("vstd function not in the model", path)
            self.calls.add(path)
            return "(%s u %s)" % (lean_path(path), " ".join(xs))
        if k == "Ctor":
            dt, variant, fields = a[0], unq(a[1]), a[2]
            vals = {int(unq(f[1])) if f[1].startswith('"') else int(f[1]): self.ex(f[2]) for f in fields}
            if dt[1] == "Tuple":
                n = int(dt[2])
                if n == 0:
                    return "()"
                return "(" + ", ".join(vals[i] for i in range(n)) + ")"
            if dt[1] == "Path" and dt[2] == "core::option::Option":
                if variant == "Some":
                    return "(some %s)" % vals[0]
                if variant == "None":
                    return "(none : %s)" % ty(t)
            fail("constructor", e)
        if k == "Closure":
            params, body = a[0], a[1]
            bs = " ".join("(%s : %s)" % (self.name(p[1]), ty(p[2])) for p in params)
            return "(fun %s => %s)" % (bs, self.ex(body))
        if k == "Quant":
            q, params, body = a[0], a[1], a[2]
            if len(params) != 1:
                fail("quantifier with several binders", e)
            x, xt = self.name(params[0][1]), params[0][2]
            sym = {"Exists": "∃", "Forall": "∀"}[q[0]]
            if vty(xt) == INT_INT:
                prop = "%s (%s : %s), %s = true" % (sym, x, ty(xt), self.ex(body))
            else:
                # over the values of the binder's type (`VTy.wt`), as Verus's `has_type`
                conn = "∧" if q[0] == "Exists" else "→"
                prop = "%s (%s : %s), VModel.VTy.wt %s %s %s %s = true" % (
                    sym, x, ty(xt), vty(xt), x, conn, self.ex(body))
            return "(@decide (%s) (Classical.propDecidable _))" % prop
        if k == "WithTriggers":
            return self.ex(vir.kw(e, "body"))
        if k == "Unary":
            op, x = a[0], self.ex(a[1])
            if op[1] == "Not":
                return "(!%s)" % x
            if op[1] == "Trigger":
                return x
            if op[1] == "Clip":
                # `truncate` only changes the checks Verus asks for, not the value:
                # sst_to_air.rs encodes every Clip as nat_clip/u_clip/i_clip.
                return "(VModel.clip u %s %s)" % (int_range(vir.kw(op, "range")), x)
            fail("unary", op)
        if k == "UnaryOpr":
            op, x = a[0], self.ex(a[1])
            if op[1] == "IsVariant":
                dt = vir.kw(op, "datatype")
                variant = unq(vir.kw(op, "variant"))
                if dt[1] == "Tuple":
                    return "true"
                if dt[1] == "Path" and dt[2] == "core::option::Option":
                    return "(Option.%s %s)" % ({"Some": "isSome", "None": "isNone"}[variant], x)
            fail("unary operator", op)
        if k == "Binary":
            op, x, y = a[0], self.ex(a[1]), self.ex(a[2])
            if op[1] == "Arith":
                ao = op[2][1]
                if ao in ("Add", "Sub", "Mul"):
                    r = overflow_range(op[2][2])
                    out = "(%s %s %s)" % (x, {"Add": "+", "Sub": "-", "Mul": "*"}[ao], y)
                    return out if r is None else "(VModel.clip u %s %s)" % (r, out)
                if ao == "EuclideanDiv" and op[2][2] == ["Div0Behavior", "Allow"]:
                    return "(VModel.ediv u %s %s)" % (x, y)
                if ao == "EuclideanMod" and op[2][2] == ["Div0Behavior", "Allow"]:
                    return "(VModel.emod u %s %s)" % (x, y)
            if op[1] == "Bitwise":
                return bitwise(op, t, a[1], a[2],
                               lambda f, r: "(VModel.clip u %s (VModel.%s %s %s))" % (r, f, x, y))
            if op[1] == "Eq" and op[2] == "Spec":
                return "(decide (%s = %s))" % (x, y)
            if op[1] == "Ne":
                return "(decide (%s ≠ %s))" % (x, y)
            if op[1] == "Inequality":
                sym = {"Le": "≤", "Lt": "<", "Ge": "≥", "Gt": ">"}[op[2][1]]
                return "(decide (%s %s %s))" % (x, sym, y)
            fail("binary", op)
        if k == "Logical":
            op, x, y = a[0][1], self.ex(a[1]), self.ex(a[2])
            if op == "And": return "(%s && %s)" % (x, y)
            if op == "Or": return "(%s || %s)" % (x, y)
            if op == "Implies": return "(!%s || %s)" % (x, y)
            fail("logical", a[0])
        fail("expression kind " + k, e)

    def stmt(self, st, body):
        if st[0] != "Stmt" or st[1] != "Decl":
            fail("statement", st)
        pat = vir.kw(st, "pattern")
        init = vir.kw(st, "init")
        if init == "None":
            fail("declaration without value", st)
        if pat[0] == "@@":
            pat = pat[1]
        if pat[0] != "Pattern" or pat[1] != "Var":
            fail("pattern", pat)
        b = pat[2]
        x = self.name(vir.kw(b, "name"))
        return "(let %s : %s := %s\n  %s)" % (x, ty(vir.kw(b, "typ")), self.place(init), body)

# ----------------------------------------------------- validation proofs
#
# For each node, a proof term of `Eval P (Oracle.ofUnspec u) ρ e v`, where `v` is the
# encoding of the node's shallow translation (Lspec/VIR/Steps.lean). The shallow values
# are not written here: Lean finds them by unification, and checks them against the
# shallow definition. Nothing here is trusted.

PRIM_LEMMA = {
    "vstd::seq::Seq::empty": "VIR.ev_empty",
    "vstd::seq::Seq::len": "VIR.ev_len",
    "vstd::seq::Seq::index": "VIR.ev_index",
    "vstd::seq::impl&%2::spec_index": "VIR.ev_index",
    "vstd::seq::Seq::push": "VIR.ev_push",
    "vstd::seq::Seq::update": "VIR.ev_update",
    "vstd::seq::Seq::subrange": "VIR.ev_subrange",
    "vstd::seq::Seq::add": "VIR.ev_add",
    "vstd::seq::impl&%2::spec_add": "VIR.ev_add",
    "vstd::seq::Seq::last": "VIR.ev_last",
    "vstd::seq_lib::impl&%0::drop_last": "VIR.ev_dropLast",
    "vstd::seq::impl&%2::skip": "VIR.ev_skip",
    "vstd::seq::impl&%2::take": "VIR.ev_take",
}

def runs_name(path):
    return "V.«runs»." + lean_path(path)

def qual(path):
    return "V." + lean_path(path)

class Pf:
    def __init__(self, fn, arity, valdec):
        self.fn = fn            # the function being validated (for its recursive calls)
        self.arity = arity
        self.valdec = valdec    # tactic for a recursive call's measure decrease
        self.fresh = 0

    def all2(self, args):
        out = "VIR.All2.nil"
        for a in reversed(args):
            out = "(VIR.All2.cons %s %s)" % (self.ex(a), out)
        return out

    def place(self, p):
        if p[0] == "@@":
            p = p[1]
        k = p[1]
        if k == "Local":
            return "(VIR.ev_var rfl)"
        if k == "Temporary":
            return self.ex(p[2])
        if k == "Field":
            fo, inner = p[2], p[3]
            dt = vir.kw(fo, "datatype")
            x = self.place(inner)
            if dt[1] == "Tuple":
                return "(VIR.ev_tupField %s rfl)" % x
            return "(VIR.ev_someField %s)" % x
        fail("place kind", p)

    def ex(self, node):
        e, t = node[1], node[2]
        k = e[1]
        a = e[2:]
        if k == "Const":
            return "(VIR.ev_int _)" if a[0][1] == "Int" else "(VIR.ev_bool _)"
        if k == "ReadPlace":
            return self.place(a[0])
        if k == "Var":
            return "(VIR.ev_var rfl)"
        if k == "Block":
            stmts, body = a[0], a[1]
            out = self.ex(body)
            for st in reversed(stmts):
                init = vir.kw(st, "init")
                out = "(VIR.ev_lett %s %s)" % (self.place(init), out)
            return out
        if k == "If":
            c, th, el = a[0], a[1], a[2]
            self.fresh += 1
            h = "h%d" % self.fresh
            return "(VIR.ev_dite (τ := %s) %s (fun %s => %s) (fun %s => %s))" % (
                vty(t), self.ex(c), h, self.ex(th), h, self.ex(el))
        if k == "Call":
            tgt = vir.kw(e, "target")
            args = vir.kw(e, "args")
            path = tgt[3][2]
            if path == "vstd::seq::Seq::new":
                n, clo = args
                ce = clo[1]
                return "(VIR.ev_new %s (fun _ => %s))" % (self.ex(n), self.ex(ce[3]))
            if path in PRIM_LEMMA:
                return "(%s %s)" % (PRIM_LEMMA[path], " ".join(self.ex(x) for x in args))
            if path == self.fn:
                run = "(ih _ (by subst hm; %s) %s rfl)" % (self.valdec, " ".join("_" for _ in range(self.arity)))
            else:
                run = "(%s u %s)" % (runs_name(path), " ".join("_" for _ in args))
            return "(VIR.ev_call %s %s)" % (self.all2(args), run)
        if k == "Ctor":
            dt, variant, fields = a[0], unq(a[1]), a[2]
            if dt[1] == "Tuple":
                vals = sorted(((int(unq(f[1])) if f[1].startswith('"') else int(f[1])), f[2]) for f in fields)
                return "(VIR.ev_tuple %s)" % self.all2([v for _, v in vals])
            if variant == "Some":
                return "(VIR.ev_some %s)" % self.ex(fields[0][2])
            return "VIR.ev_none"
        if k == "Quant":
            q, xt = a[0][0], a[1][0][2]
            if vty(xt) == INT_INT:
                return "(VIR.%s _ (fun _ => %s))" % ({"Exists": "ev_ex", "Forall": "ev_all"}[q], self.ex(a[2]))
            return "(VIR.%s %s _ (fun _ => %s))" % ({"Exists": "ev_exT", "Forall": "ev_allT"}[q],
                                                   vty(xt), self.ex(a[2]))
        if k == "WithTriggers":
            return self.ex(vir.kw(e, "body"))
        if k == "Unary":
            op = a[0]
            if op[1] == "Trigger":
                return self.ex(a[1])
            return "(VIR.%s %s)" % ("ev_not" if op[1] == "Not" else "ev_clip", self.ex(a[1]))
        if k == "UnaryOpr":
            op = a[0]
            dt = vir.kw(op, "datatype")
            if dt[1] == "Tuple":
                return "(VIR.ev_isTuple %s)" % self.ex(a[1])
            variant = unq(vir.kw(op, "variant"))
            ot = a[1][2]   # the operand's type, Option<T>
            return "(VIR.%s %s %s)" % ({"Some": "ev_isSome", "None": "ev_isNone"}[variant],
                                      vty(ot[3][0]), self.ex(a[1]))
        if k == "Binary":
            op, x, y = a[0], a[1], a[2]
            px, py = self.ex(x), self.ex(y)
            if op[1] == "Arith":
                lem = {"Add": "ev_iadd", "Sub": "ev_isub", "Mul": "ev_imul",
                       "EuclideanDiv": "ev_ediv", "EuclideanMod": "ev_emod"}[op[2][1]]
                out = "(VIR.%s %s %s)" % (lem, px, py)
                if op[2][1] in ("Add", "Sub", "Mul") and overflow_range(op[2][2]) is not None:
                    out = "(VIR.ev_clip %s)" % out
                return out
            if op[1] == "Bitwise":
                return bitwise(op, t, x, y, lambda f, r: "(VIR.ev_clip (VIR.ev_%s %s %s))" % (f, px, py))
            if op[1] == "Eq":
                return "(VIR.ev_eq %s %s %s)" % (vty(x[2]), px, py)
            if op[1] == "Ne":
                return "(VIR.ev_ne %s %s %s)" % (vty(x[2]), px, py)
            if op[1] == "Inequality":
                lem = {"Le": "ev_le", "Lt": "ev_lt", "Ge": "ev_ge", "Gt": "ev_gt"}[op[2][1]]
                return "(VIR.%s %s %s)" % (lem, px, py)
        if k == "Logical":
            lem = {"And": "ev_and", "Or": "ev_or", "Implies": "ev_implies"}[a[0][1]]
            return "(VIR.%s %s %s)" % (lem, self.ex(a[1]), self.ex(a[2]))
        fail("proof for expression kind " + k, e)

def validate(fs, order, prog, hints):
    """The validation theorem of each function, in dependency order."""
    out = []
    for p in order:
        f = fs[p]
        tr = Tr()
        params = vir.kw(f, "params")
        names = [tr.name(vir.kw(q, "name")) for q in params]
        tys = [vir.kw(q, "typ") for q in params]
        rt = vir.kw(vir.kw(f, "ret"), "typ")
        body = vir.kw(f, "body")
        tr.ex(body)
        recursive = p in tr.calls
        inv = ["(VModel.IntRange.contains %s %s)" % (int_range(t[2]), n)
               for n, t in zip(names, tys) if t[1] == "Int" and t[2] != ["IntRange", "Int"]]
        binders = " ".join("(%s : %s)" % (n, ty(t)) for n, t in zip(names, tys))
        vs = "[%s]" % ", ".join("VIR.enc %s %s" % (vty(t), n) for n, t in zip(names, tys))
        stmt = ("theorem %s (u : VModel.Unspec) %s :\n    VIR.RunsTo %s (VIR.Oracle.ofUnspec u) \"%s\" %s\n"
                "      (VIR.enc %s (%s u %s)) := by\n") % (
            "«runs»." + lean_path(p), binders, prog, p, vs, vty(rt), qual(p), " ".join(names))
        pf = Pf(p, len(names), hints.get(("validdec", p), "vir_valid_dec")).ex(body)
        lines = []
        if recursive:
            dec = vir.kw(f, "decrease")
            if len(dec) != 1:
                raise Unsupported("validation of a lexicographic measure: " + p)
            lines.append("  induction hm : (%s).toNat using Nat.strongRecOn generalizing %s with"
                         % (Tr().ex(dec[0]), " ".join(names)))
            lines.append("  | _ m ih =>")
        lines.append("  refine VIR.runs_intro (by rfl) (by rfl) (fun hi => ?_) (fun hi => ?_)")
        if inv:
            cond = "(%s) = true" % " && ".join(inv)
            lines.append("  · rw [%s, dif_pos (show %s by simpa [VIR.invOk, VIR.enc, VModel.IntRange.contains] using hi)]" % (qual(p), cond))
            lines.append("    exact %s" % pf)
            lines.append("  · rw [%s, dif_neg (show ¬(%s) by simpa [VIR.invOk, VIR.enc, VModel.IntRange.contains] using hi)]; rfl" % (qual(p), cond))
        else:
            lines.append("  · rw [%s]" % qual(p))
            lines.append("    exact %s" % pf)
            lines.append("  · exact absurd (by simp [VIR.invOk, VIR.enc, VModel.IntRange.contains]) hi")
        out.append(stmt + "\n".join(lines))
    return out

# --------------------------------------------------------------- functions

def read_hints(path):
    """Hand-written Lean for the generated file, which Lean checks, so not
    trusted. Blocks start with `-- @before PATH`, `-- @after PATH` (lemmas
    placed around a definition) or `-- @decreasing PATH` (its termination
    proof)."""
    hints, key, buf = {}, None, []
    if path is None:
        return hints
    for line in open(path).read().splitlines():
        if line.startswith("-- @"):
            if key:
                hints[key] = "\n".join(buf).strip("\n")
            kind, fn = line[4:].split()
            key, buf = (kind, fn), []
        elif key:
            buf.append(line)
    if key:
        hints[key] = "\n".join(buf).strip("\n")
    return hints

def translate(fs, roots, hints):
    order, seen, defs = [], set(), {}
    def visit(p):
        if p in seen:
            return
        seen.add(p)
        if p in VSTD:
            return
        if p not in fs:
            raise Unsupported("no VIR for " + p)
        f = fs[p]
        if vir.kw(f, "mode") != "Spec":
            raise Unsupported("not a spec function: " + p)
        if vir.kw(f, "typ_params") != []:
            raise Unsupported("generic function: " + p)
        body = vir.kw(f, "body")
        if body == "None":
            raise Unsupported("no body (uninterpreted or external): " + p)
        tr = Tr()
        params = vir.kw(f, "params")
        ps = " ".join("(%s : %s)" % (tr.name(vir.kw(q, "name")), ty(vir.kw(q, "typ"))) for q in params)
        ret = ty(vir.kw(vir.kw(f, "ret"), "typ"))
        b = tr.ex(body)
        # Verus's type invariants on integer parameters (see Vstd.lean)
        inv = []
        for q in params:
            t = vir.kw(q, "typ")
            if t[1] == "Int" and t[2] != ["IntRange", "Int"]:
                inv.append("(VModel.IntRange.contains %s %s)" % (int_range(t[2]), tr.name(vir.kw(q, "name"))))
        if inv:
            rt = vir.kw(vir.kw(f, "ret"), "typ")
            b = "(if hinv : (%s) = true then %s else VModel.arbAt u %s (α := %s) rfl)" % (
                " && ".join(inv), b, vty(rt), ty(rt))
        dec = vir.kw(f, "decrease")
        recursive = p in tr.calls
        src = "def %s (u : VModel.Unspec) %s : %s :=\n  %s" % (lean_path(p), ps, ret, b)
        if recursive:
            if not dec:
                raise Unsupported("recursive without decreases: " + p)
            measures = [Tr().ex(d) for d in dec]
            src += "\ntermination_by %s" % ", ".join("(%s).toNat" % m for m in measures)
            src += "\ndecreasing_by\n  %s" % hints.get(("decreasing", p), "all_goals vir_decreasing")
        if ("before", p) in hints:
            src = hints[("before", p)] + "\n\n" + src
        if ("after", p) in hints:
            src = src + "\n\n" + hints[("after", p)]
        for c in sorted(tr.calls):
            if c != p:
                visit(c)
        order.append(p)
        defs[p] = src
    for r in roots:
        visit(r)
    return [defs[p] for p in order], order

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("vir")
    ap.add_argument("roots", nargs="+")
    ap.add_argument("-o", default="-")
    ap.add_argument("--namespace", default="V")
    ap.add_argument("--hints", default=None)
    ap.add_argument("--validate", default=None, metavar="OUT.lean",
                    help="also write the validation proofs against the VIR semantics")
    ap.add_argument("--prog", default="V.vdeflateProg", help="the VIR.Prog the proofs are about")
    ap.add_argument("--module", default="Lspec.Bridge.VDeflate", help="the generated module, for --validate")
    a = ap.parse_args()
    fs = vir.functions(vir.parse(open(a.vir).read()))
    hints = read_hints(a.hints)
    defs, order = translate(fs, a.roots, hints)
    if a.validate:
        vout = open(a.validate, "w")
        vout.write("-- Generated by Lspec/Bridge/vir2lean.py --validate; do not edit. Checked by Lean.\n")
        vout.write("import %s\nimport Lspec.Bridge.VDeflateAst\nimport Lspec.VIR.Steps\n\n" % a.module)
        vout.write("set_option linter.unusedVariables false\nset_option maxRecDepth 8000\n"
                   "set_option maxHeartbeats 4000000\n\nnamespace V\n\nopen VModel\n\n")
        for d in validate(fs, order, a.prog, hints):
            vout.write(d + "\n\n")
        vout.write("end V\n")
    out = sys.stdout if a.o == "-" else open(a.o, "w")
    out.write("-- Generated by Lspec/Bridge/vir2lean.py from Verus's VIR; do not edit.\n")
    out.write("-- Roots: %s\n" % " ".join(a.roots))
    out.write("import Lspec.Bridge.Vstd\n\nset_option linter.unusedVariables false\n")
    out.write("set_option maxRecDepth 4000\n\n")
    out.write("namespace %s\n\nopen VModel\n\nnoncomputable section\n\n" % a.namespace)
    for d in defs:
        out.write(d + "\n\n")
    out.write("end\n\nend %s\n" % a.namespace)

if __name__ == "__main__":
    main()
