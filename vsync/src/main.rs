//! vsync: compiles transcribed syntax tables (`.syn`: H.264, H.265, AV1) to the
//! tables vsyn's verified interpreter runs.
//!
//! The notation is the standards' own (H.264 §7.1, H.265 §7.1): syntax
//! structures with syntax elements and their descriptors, `if`, `for`,
//! `while`, `do ... while`, assignments, and the functions
//! `more_rbsp_data( )` and `byte_alignment( )`. Added to it:
//!
//! * after a descriptor, the constraints a decoder checks: `range(lo, hi)`,
//!   `eq(v)`, `assert(e)`; and the ones it must not reject on,
//!   `confeq(v)`, `conf(e)`: "shall be ... decoders shall ignore";
//! * `assert(e)` and `conf(e)` as statements, for constraints between
//!   syntax elements;
//! * `array name[d1][d2]` declares an array's dimensions, and `discard name`
//!   a syntax element kept only in the trace;
//! * `program NAME = structure(args) uses CTX, ...` makes a syntax
//!   structure a program, whose names not defined in it are looked up in
//!   the programs it uses, in order; `ctx.name` names one explicitly;
//! * for AV1 (§4): `const NAME = n` for the symbols of §3; `def f(a, b) =
//!   e`, a function that is one expression (`get_relative_dist`), expanded
//!   where it is called; `return [e]` and `break` in syntax structures,
//!   lowered to flags that guard what follows; calls to syntax structures
//!   that return values, in assignments (`x = read_delta_q( )`), hoisted
//!   before them; `x = get_position( )`; and `align zeros`, which makes
//!   `byte_alignment( )` AV1's, zero bits only.
//!
//! This compiler is not verified. What it writes is data: the proofs of
//! vh26x hold for any tables, so a mistake here makes a verified codec
//! for the wrong syntax, which differential testing is there to catch.
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write as _;

// ---------------------------------------------------------------- lexing

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Id(String),
    Num(i64),
    P(&'static str),
    Eof,
}

const PUNCT: &[&str] = &[
    "<<=", ">>=", "==", "!=", "<=", ">=", "&&", "||", "<<", ">>", "++", "--", "+=", "-=", "..",
    "(", ")", "[", "]", "{", "}", ",", ";", "=", "<", ">", "+", "-", "*", "/", "%", "!", "?", ":", ".", "&", "|", "^",
];

fn lex(src: &str) -> Result<Vec<(Tok, usize)>, String> {
    let b = src.as_bytes();
    let mut i = 0;
    let mut line = 1;
    let mut out = Vec::new();
    while i < b.len() {
        let c = b[i];
        if c == b'\n' { line += 1; i += 1; continue; }
        if c.is_ascii_whitespace() { i += 1; continue; }
        if c == b'#' || (c == b'/' && i + 1 < b.len() && b[i + 1] == b'/') {
            while i < b.len() && b[i] != b'\n' { i += 1; }
            continue;
        }
        if c == b'/' && i + 1 < b.len() && b[i + 1] == b'*' {
            i += 2;
            while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') {
                if b[i] == b'\n' { line += 1; }
                i += 1;
            }
            i += 2;
            continue;
        }
        if c.is_ascii_digit() {
            let s = i;
            if c == b'0' && i + 1 < b.len() && (b[i + 1] == b'x' || b[i + 1] == b'X') {
                i += 2;
                while i < b.len() && b[i].is_ascii_hexdigit() { i += 1; }
                let v = i64::from_str_radix(&src[s + 2..i], 16).map_err(|e| format!("line {line}: {e}"))?;
                out.push((Tok::Num(v), line));
            } else {
                while i < b.len() && b[i].is_ascii_digit() { i += 1; }
                let v: i64 = src[s..i].parse().map_err(|e| format!("line {line}: {e}"))?;
                out.push((Tok::Num(v), line));
            }
            continue;
        }
        if c.is_ascii_alphabetic() || c == b'_' {
            let s = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') { i += 1; }
            out.push((Tok::Id(src[s..i].to_string()), line));
            continue;
        }
        let mut hit = None;
        for p in PUNCT {
            if src[i..].starts_with(p) { hit = Some(*p); break; }
        }
        match hit {
            Some(p) => { out.push((Tok::P(p), line)); i += p.len(); }
            None => return Err(format!("line {line}: unexpected character {:?}", c as char)),
        }
    }
    out.push((Tok::Eof, line));
    Ok(out)
}

// ------------------------------------------------------------------- AST

#[derive(Clone, Debug)]
enum Expr {
    Num(i64),
    Var(Option<String>, String, Vec<Expr>),
    Un(&'static str, Box<Expr>),
    Bin(&'static str, Box<Expr>, Box<Expr>),
    Cond(Box<Expr>, Box<Expr>, Box<Expr>),
    Call(String, Vec<Expr>),
}

#[derive(Clone, Debug)]
enum Desc { U(Expr), UE, SE, FF, SU(Expr), NS(Expr), LE(Expr), Uvlc, Leb128 }

#[derive(Clone, Debug)]
enum Check { Range(Expr, Expr), Eq(Expr), ConfEq(Expr) }

#[derive(Clone, Debug)]
enum Stmt {
    Elem { name: String, idx: Vec<Expr>, desc: Desc, checks: Vec<Check>, line: usize },
    Assign { name: String, idx: Vec<Expr>, e: Expr },
    If(Expr, Vec<Stmt>, Vec<Stmt>),
    While(Expr, Vec<Stmt>),
    More(u64, u64, Vec<Stmt>),
    Call(String, Vec<Expr>, usize),
    Align,
    Assert(Expr),
    Conf(Expr),
    Return(Option<Expr>),
    Break,
    Pos { name: String, idx: Vec<Expr> },
    ZAlign,
    Nop,
}

struct Syntax { params: Vec<String>, body: Vec<Stmt>, loop_vars: HashSet<String> }

struct ProgDecl { name: String, root: String, args: Vec<Expr>, uses: Vec<String> }

#[derive(Default)]
struct File {
    syntax: BTreeMap<String, Syntax>,
    arrays: HashMap<String, Vec<u32>>,
    discard: HashSet<String>,
    /// Arrays whose elements share one slot: the environment keeps the last.
    scalar: HashSet<String>,
    /// Constant arrays (the default scaling lists): assigned at the start of
    /// every program that refers to them.
    tables: BTreeMap<String, Vec<i64>>,
    progs: Vec<ProgDecl>,
    /// `def` functions: parameters and body.
    defs: HashMap<String, (Vec<String>, Expr)>,
    /// `input NAME`: a variable the tables read and never set, which the
    /// driver sets in the environment a structure starts from.
    inputs: Vec<String>,
}

// ---------------------------------------------------------------- parsing

struct Parser {
    t: Vec<(Tok, usize)>,
    i: usize,
    loop_vars: HashSet<String>,
    consts: HashMap<String, i64>,
    zalign: bool,
    /// `scoped params`: a structure's parameters are its own, like its `for`
    /// variables (a call does not overwrite its caller's).
    scoped: bool,
    /// `global NAME`: a variable that stays global even as a `for` variable.
    globals: HashSet<String>,
}

const DESCS: &[&str] = &["u", "ue", "se", "f", "b", "ff", "ae", "su", "ns", "le", "uvlc", "leb128"];

impl Parser {
    fn peek(&self) -> &Tok { &self.t[self.i].0 }
    fn peek2(&self) -> &Tok { &self.t[(self.i + 1).min(self.t.len() - 1)].0 }
    fn line(&self) -> usize { self.t[self.i].1 }
    fn next(&mut self) -> Tok { let t = self.t[self.i].0.clone(); if self.i + 1 < self.t.len() { self.i += 1; } t }
    fn err<T>(&self, m: &str) -> Result<T, String> { Err(format!("line {}: {} (at {:?})", self.line(), m, self.peek())) }
    fn eat(&mut self, p: &str) -> bool {
        if let Tok::P(q) = self.peek() { if *q == p { self.i += 1; return true; } }
        false
    }
    fn expect(&mut self, p: &str) -> Result<(), String> {
        if self.eat(p) { Ok(()) } else { self.err(&format!("expected `{p}`")) }
    }
    fn id(&mut self) -> Result<String, String> {
        match self.next() { Tok::Id(s) => Ok(s), _ => { self.i -= 1; self.err("expected a name") } }
    }
    fn is_id(&self, s: &str) -> bool { matches!(self.peek(), Tok::Id(x) if x == s) }
    fn num(&mut self) -> Result<i64, String> {
        if let Tok::Id(n) = self.peek().clone() {
            if let Some(&v) = self.consts.get(&n) { self.next(); return Ok(v); }
        }
        let neg = self.eat("-");
        match self.next() { Tok::Num(v) => Ok(if neg { -v } else { v }), _ => { self.i -= 1; self.err("expected a number") } }
    }

    fn file(&mut self) -> Result<File, String> {
        let mut f = File::default();
        loop {
            match self.peek().clone() {
                Tok::Eof => break,
                Tok::Id(k) if k == "array" => {
                    self.next();
                    let n = self.id()?;
                    let mut dims = Vec::new();
                    while self.eat("[") { dims.push(self.num()? as u32); self.expect("]")?; }
                    f.arrays.insert(n, dims);
                }
                Tok::Id(k) if k == "scalar" => {
                    self.next();
                    loop {
                        f.scalar.insert(self.id()?);
                        if !self.eat(",") { break; }
                    }
                }
                Tok::Id(k) if k == "table" => {
                    self.next();
                    let n = self.id()?;
                    self.expect("=")?;
                    self.expect("{")?;
                    let mut v = Vec::new();
                    if !self.eat("}") {
                        loop { v.push(self.num()?); if self.eat("}") { break; } self.expect(",")?; }
                    }
                    f.arrays.insert(n.clone(), vec![v.len() as u32]);
                    f.tables.insert(n, v);
                }
                Tok::Id(k) if k == "const" => {
                    self.next();
                    let n = self.id()?;
                    self.expect("=")?;
                    let e = self.expr()?;
                    let v = match e { Expr::Num(v) => v, _ => return self.err("a const is a number") };
                    self.consts.insert(n, v);
                }
                Tok::Id(k) if k == "def" => {
                    self.next();
                    let n = self.id()?;
                    self.expect("(")?;
                    let mut params = Vec::new();
                    if !self.eat(")") {
                        loop { params.push(self.id()?); if self.eat(")") { break; } self.expect(",")?; }
                    }
                    self.expect("=")?;
                    let e = self.expr()?;
                    f.defs.insert(n, (params, e));
                }
                Tok::Id(k) if k == "input" => {
                    self.next();
                    loop {
                        f.inputs.push(self.id()?);
                        if !self.eat(",") { break; }
                    }
                }
                Tok::Id(k) if k == "global" => {
                    self.next();
                    loop {
                        let n = self.id()?;
                        self.globals.insert(n);
                        if !self.eat(",") { break; }
                    }
                }
                Tok::Id(k) if k == "scoped" && matches!(self.peek2(), Tok::Id(z) if z == "params") => {
                    self.next();
                    self.next();
                    self.scoped = true;
                }
                Tok::Id(k) if k == "align" && matches!(self.peek2(), Tok::Id(z) if z == "zeros") => {
                    self.next();
                    self.next();
                    self.zalign = true;
                }
                Tok::Id(k) if k == "discard" => {
                    self.next();
                    loop {
                        f.discard.insert(self.id()?);
                        if !self.eat(",") { break; }
                    }
                }
                Tok::Id(k) if k == "program" => {
                    self.next();
                    let name = self.id()?;
                    self.expect("=")?;
                    let root = self.id()?;
                    self.expect("(")?;
                    let mut args = Vec::new();
                    if !self.eat(")") {
                        loop { args.push(self.expr()?); if self.eat(")") { break; } self.expect(",")?; }
                    }
                    let mut uses = Vec::new();
                    if self.is_id("uses") {
                        self.next();
                        loop { uses.push(self.id()?); if !self.eat(",") { break; } }
                    }
                    f.progs.push(ProgDecl { name, root, args, uses });
                }
                Tok::Id(_) => {
                    let name = self.id()?;
                    self.expect("(")?;
                    let mut params = Vec::new();
                    if !self.eat(")") {
                        loop { params.push(self.id()?); if self.eat(")") { break; } self.expect(",")?; }
                    }
                    self.expect("{")?;
                    self.loop_vars.clear();
                    if self.scoped { for p in &params { self.loop_vars.insert(p.clone()); } }
                    let body = self.stmts_until_close()?;
                    let loop_vars = std::mem::take(&mut self.loop_vars);
                    if f.syntax.insert(name.clone(), Syntax { params, body, loop_vars }).is_some() {
                        return Err(format!("syntax structure {name} defined twice"));
                    }
                }
                _ => return self.err("expected a declaration"),
            }
        }
        Ok(f)
    }

    fn stmts_until_close(&mut self) -> Result<Vec<Stmt>, String> {
        let mut v = Vec::new();
        while !self.eat("}") {
            if *self.peek() == Tok::Eof { return self.err("unclosed `{`"); }
            v.push(self.stmt()?);
        }
        Ok(v)
    }

    fn block(&mut self) -> Result<Vec<Stmt>, String> {
        if self.eat("{") { self.stmts_until_close() } else { Ok(vec![self.stmt()?]) }
    }

    fn is_more_call(&self) -> bool {
        matches!(self.peek(), Tok::Id(x) if x == "more_rbsp_data")
    }

    fn more_call(&mut self) -> Result<(), String> {
        self.next();
        self.expect("(")?;
        self.expect(")")
    }

    fn stmt(&mut self) -> Result<Stmt, String> {
        let line = self.line();
        let name = self.id()?;
        match name.as_str() {
            "if" => {
                self.expect("(")?;
                if self.is_more_call() {
                    self.more_call()?;
                    self.expect(")")?;
                    let b = self.block()?;
                    if self.is_id("else") { return self.err("`else` after `if( more_rbsp_data( ) )`"); }
                    return Ok(Stmt::More(0, 1, b));
                }
                let c = self.expr()?;
                self.expect(")")?;
                let t = self.block()?;
                let f = if self.is_id("else") { self.next(); self.block()? } else { vec![] };
                Ok(Stmt::If(c, t, f))
            }
            "while" => {
                self.expect("(")?;
                if self.is_more_call() {
                    self.more_call()?;
                    self.expect(")")?;
                    let b = self.block()?;
                    return Ok(Stmt::More(0, 281474976710656, b));
                }
                let c = self.expr()?;
                self.expect(")")?;
                let b = self.block()?;
                Ok(Stmt::While(c, b))
            }
            "do" => {
                let b = self.block()?;
                if !self.is_id("while") { return self.err("expected `while`"); }
                self.next();
                self.expect("(")?;
                if !self.is_more_call() {
                    // do S while( c ): S, then while( c ) S
                    let c = self.expr()?;
                    self.expect(")")?;
                    let mut v = b.clone();
                    v.push(Stmt::While(c, b));
                    return Ok(Stmt::If(Expr::Num(1), v, vec![]));
                }
                self.more_call()?;
                self.expect(")")?;
                Ok(Stmt::More(1, 281474976710656, b))
            }
            "for" => {
                self.expect("(")?;
                let init = self.simple()?;
                if let Stmt::Assign { name, .. } = &init {
                    if !self.globals.contains(name) { self.loop_vars.insert(name.clone()); }
                }
                self.expect(";")?;
                let c = self.expr()?;
                self.expect(";")?;
                let step = self.simple()?;
                self.expect(")")?;
                let mut b = self.block()?;
                b.push(step);
                Ok(Stmt::If(Expr::Num(1), vec![init, Stmt::While(c, b)], vec![]))
            }
            "byte_alignment" => { self.expect("(")?; self.expect(")")?; Ok(if self.zalign { Stmt::ZAlign } else { Stmt::Align }) }
            "return" => {
                // a value is on the same line as the `return`
                if matches!(self.peek(), Tok::P("}")) || self.line() != line { return Ok(Stmt::Return(None)); }
                Ok(Stmt::Return(Some(self.expr()?)))
            }
            "break" => Ok(Stmt::Break),
            "local" => {
                loop {
                    let n = self.id()?;
                    self.loop_vars.insert(n);
                    if !self.eat(",") { break; }
                }
                Ok(Stmt::Nop)
            }
            "assert" => { self.expect("(")?; let e = self.expr()?; self.expect(")")?; Ok(Stmt::Assert(e)) }
            "conf" => { self.expect("(")?; let e = self.expr()?; self.expect(")")?; Ok(Stmt::Conf(e)) }
            _ => {
                if *self.peek() == Tok::P("(") {
                    self.next();
                    let mut args = Vec::new();
                    if !self.eat(")") {
                        loop { args.push(self.expr()?); if self.eat(")") { break; } self.expect(",")?; }
                    }
                    return Ok(Stmt::Call(name, args, line));
                }
                let mut idx = Vec::new();
                while self.eat("[") { idx.push(self.expr()?); self.expect("]")?; }
                if let Tok::Id(d) = self.peek().clone() {
                    if DESCS.contains(&d.as_str()) && *self.peek2() == Tok::P("(") || d == "ff" {
                        self.next();
                        let desc = self.desc(&d)?;
                        let mut checks = Vec::new();
                        loop {
                            let k = match self.peek() { Tok::Id(k) => k.clone(), _ => break };
                            let c = match k.as_str() {
                                "range" => { self.next(); self.expect("(")?; let a = self.expr()?; self.expect(",")?; let b = self.expr()?; self.expect(")")?; Check::Range(a, b) }
                                "eq" => { self.next(); self.expect("(")?; let a = self.expr()?; self.expect(")")?; Check::Eq(a) }
                                "confeq" => { self.next(); self.expect("(")?; let a = self.expr()?; self.expect(")")?; Check::ConfEq(a) }
                                _ => break,
                            };
                            checks.push(c);
                        }
                        return Ok(Stmt::Elem { name, idx, desc, checks, line });
                    }
                }
                self.assign_rest(name, idx)
            }
        }
    }

    fn desc(&mut self, d: &str) -> Result<Desc, String> {
        if d == "ff" { return Ok(Desc::FF); }
        self.expect("(")?;
        let r = match d {
            "u" | "f" | "b" => {
                if self.is_id("v") { return self.err("write u(v)'s width as an expression"); }
                Desc::U(self.expr()?)
            }
            "ue" => { if !self.is_id("v") { return self.err("ue(v)"); } self.next(); Desc::UE }
            "se" => { if !self.is_id("v") { return self.err("se(v)"); } self.next(); Desc::SE }
            "su" => Desc::SU(self.expr()?),
            "ns" => Desc::NS(self.expr()?),
            "le" => Desc::LE(self.expr()?),
            "uvlc" => { self.expect(")")?; return Ok(Desc::Uvlc); }
            "leb128" => { self.expect(")")?; return Ok(Desc::Leb128); }
            _ => return self.err("unsupported descriptor"),
        };
        self.expect(")")?;
        Ok(r)
    }

    /// An assignment or increment, as in a `for` header.
    fn simple(&mut self) -> Result<Stmt, String> {
        let name = self.id()?;
        let mut idx = Vec::new();
        while self.eat("[") { idx.push(self.expr()?); self.expect("]")?; }
        self.assign_rest(name, idx)
    }

    fn assign_rest(&mut self, name: String, idx: Vec<Expr>) -> Result<Stmt, String> {
        let me = Expr::Var(None, name.clone(), idx.clone());
        let e = if self.eat("=") {
            self.expr()?
        } else if self.eat("++") {
            Expr::Bin("+", Box::new(me), Box::new(Expr::Num(1)))
        } else if self.eat("--") {
            Expr::Bin("-", Box::new(me), Box::new(Expr::Num(1)))
        } else if self.eat("+=") {
            Expr::Bin("+", Box::new(me), Box::new(self.expr()?))
        } else if self.eat("-=") {
            Expr::Bin("-", Box::new(me), Box::new(self.expr()?))
        } else {
            return self.err("expected a descriptor, `=`, or `(`");
        };
        if let Expr::Call(g, a) = &e {
            if g == "get_position" && a.is_empty() { return Ok(Stmt::Pos { name, idx }); }
        }
        Ok(Stmt::Assign { name, idx, e })
    }

    fn expr(&mut self) -> Result<Expr, String> {
        let c = self.bin(0)?;
        if self.eat("?") {
            let a = self.expr()?;
            self.expect(":")?;
            let b = self.expr()?;
            return Ok(Expr::Cond(Box::new(c), Box::new(a), Box::new(b)));
        }
        Ok(c)
    }

    fn bin(&mut self, lvl: usize) -> Result<Expr, String> {
        const LV: &[&[&str]] = &[&["||"], &["&&"], &["|"], &["^"], &["&"], &["==", "!="], &["<", "<=", ">", ">="], &["<<", ">>"], &["+", "-"], &["*", "/", "%"]];
        if lvl == LV.len() { return self.unary(); }
        let mut l = self.bin(lvl + 1)?;
        loop {
            let op = match self.peek() { Tok::P(p) if LV[lvl].contains(p) => *p, _ => break };
            self.next();
            let r = self.bin(lvl + 1)?;
            l = Expr::Bin(op, Box::new(l), Box::new(r));
        }
        Ok(l)
    }

    fn unary(&mut self) -> Result<Expr, String> {
        if self.eat("!") { return Ok(Expr::Un("!", Box::new(self.unary()?))); }
        if self.eat("-") { return Ok(Expr::Un("-", Box::new(self.unary()?))); }
        if self.eat("(") { let e = self.expr()?; self.expect(")")?; return Ok(e); }
        match self.next() {
            Tok::Num(v) => Ok(Expr::Num(v)),
            Tok::Id(n) => {
                if *self.peek() == Tok::P("(") {
                    self.next();
                    let mut args = Vec::new();
                    if !self.eat(")") {
                        loop { args.push(self.expr()?); if self.eat(")") { break; } self.expect(",")?; }
                    }
                    return Ok(Expr::Call(n, args));
                }
                if let Some(&v) = self.consts.get(&n) {
                    if *self.peek() != Tok::P("[") && *self.peek() != Tok::P(".") { return Ok(Expr::Num(v)); }
                }
                let (q, n) = if *self.peek() == Tok::P(".") { self.next(); (Some(n), self.id()?) } else { (None, n) };
                let mut idx = Vec::new();
                while self.eat("[") { idx.push(self.expr()?); self.expect("]")?; }
                Ok(Expr::Var(q, n, idx))
            }
            _ => { self.i -= 1; self.err("expected an expression") }
        }
    }
}

// -------------------------------------------------------------- lowering
//
// What the interpreter has no statement for, rewritten into what it has.
// Each rewrite keeps the meaning of the C-like notation of AV1 §4.

/// Expand the `def` functions in an expression.
fn expand(defs: &HashMap<String, (Vec<String>, Expr)>, e: &Expr, depth: u32) -> Result<Expr, String> {
    if depth > 16 { return Err("def functions nest too deep".into()); }
    let r = |x: &Expr| expand(defs, x, depth);
    Ok(match e {
        Expr::Num(_) => e.clone(),
        Expr::Var(q, n, idx) => Expr::Var(q.clone(), n.clone(), idx.iter().map(r).collect::<Result<_, _>>()?),
        Expr::Un(o, a) => Expr::Un(o, Box::new(r(a)?)),
        Expr::Bin(o, a, b) => Expr::Bin(o, Box::new(r(a)?), Box::new(r(b)?)),
        Expr::Cond(a, b, c) => Expr::Cond(Box::new(r(a)?), Box::new(r(b)?), Box::new(r(c)?)),
        Expr::Call(f, a) => {
            let a: Vec<Expr> = a.iter().map(r).collect::<Result<_, _>>()?;
            match defs.get(f) {
                Some((ps, body)) => {
                    if ps.len() != a.len() { return Err(format!("{f} takes {} arguments", ps.len())); }
                    let sub: HashMap<&str, &Expr> = ps.iter().map(|p| p.as_str()).zip(a.iter()).collect();
                    let b = subst(body, &sub);
                    expand(defs, &b, depth + 1)?
                }
                None => Expr::Call(f.clone(), a),
            }
        }
    })
}

fn subst(e: &Expr, sub: &HashMap<&str, &Expr>) -> Expr {
    match e {
        Expr::Var(None, n, idx) if idx.is_empty() && sub.contains_key(n.as_str()) => sub[n.as_str()].clone(),
        Expr::Var(q, n, idx) => Expr::Var(q.clone(), n.clone(), idx.iter().map(|x| subst(x, sub)).collect()),
        Expr::Un(o, a) => Expr::Un(o, Box::new(subst(a, sub))),
        Expr::Bin(o, a, b) => Expr::Bin(o, Box::new(subst(a, sub)), Box::new(subst(b, sub))),
        Expr::Cond(a, b, c) => Expr::Cond(Box::new(subst(a, sub)), Box::new(subst(b, sub)), Box::new(subst(c, sub))),
        Expr::Call(f, a) => Expr::Call(f.clone(), a.iter().map(|x| subst(x, sub)).collect()),
        Expr::Num(_) => e.clone(),
    }
}

fn map_exprs(v: &mut [Stmt], f: &mut dyn FnMut(&Expr) -> Result<Expr, String>) -> Result<(), String> {
    for s in v {
        match s {
            Stmt::Elem { idx, desc, checks, .. } => {
                for i in idx.iter_mut() { *i = f(i)?; }
                match desc { Desc::U(w) | Desc::SU(w) | Desc::NS(w) | Desc::LE(w) => *w = f(w)?, _ => {} }
                for c in checks.iter_mut() {
                    match c {
                        Check::Range(a, b) => { *a = f(a)?; *b = f(b)?; }
                        Check::Eq(a) | Check::ConfEq(a) => *a = f(a)?,
                    }
                }
            }
            Stmt::Assign { idx, e, .. } => { for i in idx.iter_mut() { *i = f(i)?; } *e = f(e)?; }
            Stmt::Pos { idx, .. } => { for i in idx.iter_mut() { *i = f(i)?; } }
            Stmt::If(c, a, b) => { *c = f(c)?; map_exprs(a, f)?; map_exprs(b, f)?; }
            Stmt::While(c, b) => { *c = f(c)?; map_exprs(b, f)?; }
            Stmt::More(_, _, b) => map_exprs(b, f)?,
            Stmt::Call(_, a, _) => { for x in a.iter_mut() { *x = f(x)?; } }
            Stmt::Assert(e) | Stmt::Conf(e) => *e = f(e)?,
            Stmt::Return(Some(e)) => *e = f(e)?,
            _ => {}
        }
    }
    Ok(())
}

fn has(v: &[Stmt], p: &dyn Fn(&Stmt) -> bool, into_loops: bool) -> bool {
    v.iter().any(|s| p(s) || match s {
        Stmt::If(_, a, b) => has(a, p, into_loops) || has(b, p, into_loops),
        Stmt::While(_, b) | Stmt::More(_, _, b) => into_loops && has(b, p, into_loops),
        _ => false,
    })
}

fn not(e: Expr) -> Expr { Expr::Un("!", Box::new(e)) }
fn var(n: &str) -> Expr { Expr::Var(None, n.to_string(), vec![]) }
fn set(n: &str, e: Expr) -> Stmt { Stmt::Assign { name: n.to_string(), idx: vec![], e } }

/// `break`: each loop whose body breaks gets a flag; a break sets it, the
/// loop's condition tests it, and what follows a statement that may break
/// runs only if it did not.
fn lower_breaks(v: Vec<Stmt>, fname: &str, n: &mut u32) -> Result<Vec<Stmt>, String> {
    let mut out = Vec::new();
    for s in v {
        match s {
            Stmt::While(c, b) => {
                let b = lower_breaks(b, fname, n)?;
                if has(&b, &|s| matches!(s, Stmt::Break), false) {
                    *n += 1;
                    let flag = format!("__brk_{fname}_{n}");
                    out.push(set(&flag, Expr::Num(0)));
                    let body = guard(b, &flag, &|s| matches!(s, Stmt::Break), &|| vec![set(&flag, Expr::Num(1))]);
                    out.push(Stmt::While(Expr::Bin("&&", Box::new(not(var(&flag))), Box::new(c)), body));
                } else {
                    out.push(Stmt::While(c, b));
                }
            }
            Stmt::If(c, a, b) => out.push(Stmt::If(c, lower_breaks(a, fname, n)?, lower_breaks(b, fname, n)?)),
            Stmt::More(x, y, b) => {
                let b = lower_breaks(b, fname, n)?;
                if has(&b, &|s| matches!(s, Stmt::Break), false) { return Err(format!("{fname}: break in more_rbsp_data( )")); }
                out.push(Stmt::More(x, y, b));
            }
            s => out.push(s),
        }
    }
    Ok(out)
}

/// Replace each statement `hit` matches by `repl( )`, and guard what
/// follows a statement that may reach one with `!flag`. Loops are not
/// entered (their own flags handle them), except for `return`, which the
/// caller handles by testing the flag in their conditions.
fn guard(v: Vec<Stmt>, flag: &str, hit: &dyn Fn(&Stmt) -> bool, repl: &dyn Fn() -> Vec<Stmt>) -> Vec<Stmt> {
    let mut out = Vec::new();
    let mut it = v.into_iter();
    while let Some(s) = it.next() {
        if hit(&s) {
            out.extend(repl());
            return out;
        }
        let reaches = has(std::slice::from_ref(&s), hit, false);
        let s = match s {
            Stmt::If(c, a, b) => Stmt::If(c, guard(a, flag, hit, repl), guard(b, flag, hit, repl)),
            s => s,
        };
        out.push(s);
        if reaches {
            let rest: Vec<Stmt> = it.collect();
            if !rest.is_empty() {
                out.push(Stmt::If(not(var(flag)), guard(rest, flag, hit, repl), vec![]));
            }
            return out;
        }
    }
    out
}

/// `return`: a flag per syntax structure, cleared on entry. A return sets
/// the result and the flag; loops that may return test the flag; what
/// follows a statement that may return runs only if it did not.
fn lower_returns(v: Vec<Stmt>, fname: &str) -> Vec<Stmt> {
    let done = format!("__done_{fname}");
    let ret = format!("__ret_{fname}");
    let is_ret = |s: &Stmt| matches!(s, Stmt::Return(_));
    fn go(v: Vec<Stmt>, done: &str, ret: &str, is_ret: &dyn Fn(&Stmt) -> bool) -> Vec<Stmt> {
        let mut out = Vec::new();
        let mut it = v.into_iter();
        while let Some(s) = it.next() {
            let reaches = has(std::slice::from_ref(&s), is_ret, true);
            match s {
                Stmt::Return(e) => {
                    if let Some(e) = e { out.push(set(ret, e)); }
                    out.push(set(done, Expr::Num(1)));
                    return out;
                }
                Stmt::If(c, a, b) => out.push(Stmt::If(c, go(a, done, ret, is_ret), go(b, done, ret, is_ret))),
                Stmt::While(c, b) if reaches => {
                    out.push(Stmt::While(Expr::Bin("&&", Box::new(not(var(done))), Box::new(c)), go(b, done, ret, is_ret)));
                }
                s => out.push(s),
            }
            if reaches {
                let rest: Vec<Stmt> = it.collect();
                if !rest.is_empty() {
                    out.push(Stmt::If(not(var(done)), go(rest, done, ret, is_ret), vec![]));
                }
                return out;
            }
        }
        out
    }
    let mut out = vec![set(&done, Expr::Num(0))];
    out.extend(go(v, &done, &ret, &is_ret));
    out
}

/// Calls to syntax structures inside an assignment's expression: each is
/// made first, into a temporary, and the expression reads the temporary.
fn hoist(f: &File, v: Vec<Stmt>, tmp: &mut u32) -> Result<Vec<Stmt>, String> {
    fn calls(f: &File, e: &Expr, pre: &mut Vec<Stmt>, tmp: &mut u32) -> Result<Expr, String> {
        let r = |x: &Expr, pre: &mut Vec<Stmt>, tmp: &mut u32| calls(f, x, pre, tmp);
        Ok(match e {
            Expr::Num(_) => e.clone(),
            Expr::Var(q, n, idx) => {
                let mut ix = Vec::new();
                for i in idx { ix.push(r(i, pre, tmp)?); }
                Expr::Var(q.clone(), n.clone(), ix)
            }
            Expr::Un(o, a) => Expr::Un(o, Box::new(r(a, pre, tmp)?)),
            Expr::Bin(o, a, b) => {
                if matches!(*o, "&&" | "||") && (user_call(f, a) || user_call(f, b)) {
                    return Err("a call to a syntax structure under && or ||: assign it first".into());
                }
                Expr::Bin(o, Box::new(r(a, pre, tmp)?), Box::new(r(b, pre, tmp)?))
            }
            Expr::Cond(a, b, c) => {
                if user_call(f, b) || user_call(f, c) { return Err("a call to a syntax structure under ?:".into()); }
                Expr::Cond(Box::new(r(a, pre, tmp)?), Box::new(r(b, pre, tmp)?), Box::new(r(c, pre, tmp)?))
            }
            Expr::Call(g, a) if f.syntax.contains_key(g) => {
                let mut args = Vec::new();
                for x in a { args.push(r(x, pre, tmp)?); }
                pre.push(Stmt::Call(g.clone(), args, 0));
                *tmp += 1;
                let t = format!("__tmp{tmp}");
                pre.push(set(&t, var(&format!("__ret_{g}"))));
                var(&t)
            }
            Expr::Call(g, a) => {
                let mut args = Vec::new();
                for x in a { args.push(r(x, pre, tmp)?); }
                Expr::Call(g.clone(), args)
            }
        })
    }
    let mut out = Vec::new();
    for s in v {
        match s {
            Stmt::Assign { name, idx, e } => {
                let mut pre = Vec::new();
                let e = calls(f, &e, &mut pre, tmp)?;
                let mut ix = Vec::new();
                for i in &idx { ix.push(calls(f, i, &mut pre, tmp)?); }
                out.extend(pre);
                out.push(Stmt::Assign { name, idx: ix, e });
            }
            Stmt::If(c, a, b) => {
                if user_call(f, &c) { return Err("a call to a syntax structure in a condition: assign it first".into()); }
                out.push(Stmt::If(c, hoist(f, a, tmp)?, hoist(f, b, tmp)?));
            }
            Stmt::While(c, b) => {
                if user_call(f, &c) { return Err("a call to a syntax structure in a loop condition: assign it first".into()); }
                out.push(Stmt::While(c, hoist(f, b, tmp)?));
            }
            Stmt::More(x, y, b) => out.push(Stmt::More(x, y, hoist(f, b, tmp)?)),
            Stmt::Call(g, a, l) => {
                let mut pre = Vec::new();
                let mut args = Vec::new();
                for x in &a { args.push(calls(f, x, &mut pre, tmp)?); }
                out.extend(pre);
                out.push(Stmt::Call(g, args, l));
            }
            s => out.push(s),
        }
    }
    Ok(out)
}

fn user_call(f: &File, e: &Expr) -> bool {
    match e {
        Expr::Num(_) => false,
        Expr::Var(_, _, idx) => idx.iter().any(|i| user_call(f, i)),
        Expr::Un(_, a) => user_call(f, a),
        Expr::Bin(_, a, b) => user_call(f, a) || user_call(f, b),
        Expr::Cond(a, b, c) => user_call(f, a) || user_call(f, b) || user_call(f, c),
        Expr::Call(g, a) => f.syntax.contains_key(g) || a.iter().any(|x| user_call(f, x)),
    }
}

/// `leb128( )` sets Leb128Bytes to the bytes it read (AV1 §4.10.5): the
/// positions before and after it.
fn leb_bytes(v: Vec<Stmt>) -> Vec<Stmt> {
    let mut out = Vec::new();
    for s in v {
        match s {
            Stmt::Elem { desc: Desc::Leb128, .. } => {
                out.push(Stmt::Pos { name: "__leb_start".into(), idx: vec![] });
                out.push(s);
                out.push(Stmt::Pos { name: "__leb_end".into(), idx: vec![] });
                out.push(set("Leb128Bytes", Expr::Bin(">>", Box::new(Expr::Bin("-", Box::new(var("__leb_end")), Box::new(var("__leb_start")))), Box::new(Expr::Num(3)))));
            }
            Stmt::If(c, a, b) => out.push(Stmt::If(c, leb_bytes(a), leb_bytes(b))),
            Stmt::While(c, b) => out.push(Stmt::While(c, leb_bytes(b))),
            Stmt::More(x, y, b) => out.push(Stmt::More(x, y, leb_bytes(b))),
            s => out.push(s),
        }
    }
    out
}

fn lower(f: &mut File) -> Result<(), String> {
    let defs = f.defs.clone();
    let names: Vec<String> = f.syntax.keys().cloned().collect();
    let mut tmp = 0u32;
    for n in &names {
        let mut body = std::mem::take(&mut f.syntax.get_mut(n).unwrap().body);
        map_exprs(&mut body, &mut |e| expand(&defs, e, 0)).map_err(|e| format!("{n}: {e}"))?;
        body = leb_bytes(body);
        let mut k = 0;
        body = lower_breaks(body, n, &mut k)?;
        if has(&body, &|s| matches!(s, Stmt::Break), true) { return Err(format!("{n}: break outside a loop")); }
        if has(&body, &|s| matches!(s, Stmt::Return(_)), true) { body = lower_returns(body, n); }
        f.syntax.get_mut(n).unwrap().body = body;
    }
    for n in &names {
        let body = std::mem::take(&mut f.syntax.get_mut(n).unwrap().body);
        let body = hoist(f, body, &mut tmp).map_err(|e| format!("{n}: {e}"))?;
        f.syntax.get_mut(n).unwrap().body = body;
    }
    for p in f.progs.iter_mut() {
        for a in p.args.iter_mut() { *a = expand(&defs, a, 0)?; }
    }
    Ok(())
}

// -------------------------------------------------------------- compiling

#[derive(Clone)]
struct VarInfo { slot: u32, dims: Vec<u32> }

struct Scope { vars: BTreeMap<String, VarInfo>, nslots: u32 }

struct Comp<'a> {
    f: &'a File,
    scope: Scope,
    ctx: Vec<(String, &'a Scope)>,
    xs: Vec<(u8, i64, u64, u64, u64)>,
    xmemo: HashMap<(u8, i64, u64, u64, u64), u64>,
    blocks: Vec<Vec<(u8, u64, u64, u64, u64, u64, u32)>>,
    callee_block: HashMap<String, u64>,
    labels: Vec<(String, u32)>,
    label_memo: HashMap<String, u32>,
    var_index: HashMap<String, u32>,
    stack: Vec<String>,
}

fn collect_names(f: &File, name: &str, acc: &mut Vec<String>, seen: &mut HashSet<String>, stack: &mut Vec<String>) -> Result<(), String> {
    if stack.contains(&name.to_string()) { return Err(format!("recursive syntax structure {name}")); }
    let s = f.syntax.get(name).ok_or(format!("no syntax structure {name}"))?;
    if !seen.insert(name.to_string()) { return Ok(()); }
    stack.push(name.to_string());
    for p in &s.params { acc.push(if s.loop_vars.contains(p) { format!("{name}.{p}") } else { p.clone() }); }
    fn ex(f: &File, e: &Expr, acc: &mut Vec<String>) {
        match e {
            Expr::Num(_) => {}
            Expr::Var(q, n, idx) => {
                if q.is_none() && f.tables.contains_key(n) { acc.push(n.clone()); }
                for i in idx { ex(f, i, acc); }
            }
            Expr::Un(_, a) => ex(f, a, acc),
            Expr::Bin(_, a, b) => { ex(f, a, acc); ex(f, b, acc); }
            Expr::Cond(a, b, c) => { ex(f, a, acc); ex(f, b, acc); ex(f, c, acc); }
            Expr::Call(_, a) => for x in a { ex(f, x, acc); },
        }
    }
    let lv = &s.loop_vars;
    let mangle = |n: &String| if lv.contains(n) { format!("{name}.{n}") } else { n.clone() };
    fn walk(f: &File, v: &[Stmt], acc: &mut Vec<String>, seen: &mut HashSet<String>, stack: &mut Vec<String>, mg: &dyn Fn(&String) -> String) -> Result<(), String> {
        for s in v {
            match s {
                Stmt::Elem { name, idx, .. } => { acc.push(mg(name)); for i in idx { ex(f, i, acc); } }
                Stmt::Assign { name, idx, e } => { acc.push(mg(name)); for i in idx { ex(f, i, acc); } ex(f, e, acc); }
                Stmt::If(c, a, b) => { ex(f, c, acc); walk(f, a, acc, seen, stack, mg)?; walk(f, b, acc, seen, stack, mg)?; }
                Stmt::While(c, b) => { ex(f, c, acc); walk(f, b, acc, seen, stack, mg)?; }
                Stmt::More(_, _, b) => walk(f, b, acc, seen, stack, mg)?,
                Stmt::Call(n, a, _) => { for x in a { ex(f, x, acc); } collect_names(f, n, acc, seen, stack)?; }
                Stmt::Pos { name, idx } => { acc.push(mg(name)); for i in idx { ex(f, i, acc); } }
                _ => {}
            }
        }
        Ok(())
    }
    walk(f, &s.body, acc, seen, stack, &mangle)?;
    stack.pop();
    Ok(())
}

fn make_scope(f: &File, root: &str) -> Result<Scope, String> {
    let mut names = f.inputs.clone();
    collect_names(f, root, &mut names, &mut HashSet::new(), &mut Vec::new())?;
    let mut vars = BTreeMap::new();
    let mut n: u32 = 0;
    for nm in names {
        if vars.contains_key(&nm) || f.discard.contains(&nm) { continue; }
        let dims = if f.scalar.contains(&nm) { vec![] } else { f.arrays.get(&nm).cloned().unwrap_or_default() };
        let size: u32 = dims.iter().product::<u32>().max(1);
        vars.insert(nm, VarInfo { slot: n, dims });
        n += size;
    }
    Ok(Scope { vars, nslots: n })
}

const BOPS: &[(&str, i64)] = &[
    ("+", 0), ("-", 1), ("*", 2), ("/", 3), ("%", 4), ("<<", 5), (">>", 6), ("<", 7), ("<=", 8),
    (">", 9), (">=", 10), ("==", 11), ("!=", 12), ("&&", 13), ("||", 14),
    ("&", 17), ("|", 18), ("^", 19),
];

impl<'a> Comp<'a> {
    fn node(&mut self, n: (u8, i64, u64, u64, u64)) -> u64 {
        if let Some(&i) = self.xmemo.get(&n) { return i; }
        let i = self.xs.len() as u64;
        self.xs.push(n);
        self.xmemo.insert(n, i);
        i
    }

    fn lit(&mut self, v: i64) -> u64 { self.node((0, v, 0, 0, 0)) }

    fn bin(&mut self, op: i64, a: u64, b: u64) -> u64 { self.node((6, op, a, b, 0)) }

    /// A flattened index, and the array's length. Each subscript is
    /// checked against its own dimension: one out of range makes the
    /// index -1, which fails.
    fn index(&mut self, dims: &[u32], idx: &[Expr], what: &str) -> Result<(u64, u64), String> {
        if dims.len() != idx.len() {
            return Err(format!("{what}: {} subscripts for {} dimensions", idx.len(), dims.len()));
        }
        let mut acc: Option<u64> = None;
        let mut ok: Option<u64> = None;
        for (d, e) in dims.iter().zip(idx) {
            let ie = self.expr(e)?;
            let z = self.lit(0);
            let dl = self.lit(*d as i64);
            let ge = self.bin(10, ie, z);
            let lt = self.bin(7, ie, dl);
            let inr = self.bin(13, ge, lt);
            ok = Some(match ok { None => inr, Some(o) => self.bin(13, o, inr) });
            acc = Some(match acc {
                None => ie,
                Some(a) => { let m = self.bin(2, a, dl); self.bin(0, m, ie) }
            });
        }
        let len: u64 = dims.iter().map(|&d| d as u64).product();
        if dims.len() == 1 {
            return Ok((acc.unwrap(), len));
        }
        let neg = self.lit(-1);
        let c = self.node((7, 0, ok.unwrap(), acc.unwrap(), neg));
        Ok((c, len))
    }

    /// A `for` variable is local to its syntax structure.
    fn local(&self, name: &str) -> String {
        if let Some(cur) = self.stack.last() {
            if self.f.syntax[cur].loop_vars.contains(name) { return format!("{cur}.{name}"); }
        }
        name.to_string()
    }

    fn lookup(&self, q: &Option<String>, name: &str) -> Result<(Option<usize>, VarInfo), String> {
        let mangled = self.local(name);
        let name = if q.is_none() { mangled.as_str() } else { name };
        if let Some(q) = q {
            for (k, (cn, sc)) in self.ctx.iter().enumerate() {
                if cn == q {
                    return sc.vars.get(name).map(|v| (Some(k), v.clone())).ok_or(format!("{q} has no {name}"));
                }
            }
            return Err(format!("no context {q}"));
        }
        if let Some(v) = self.scope.vars.get(name) { return Ok((None, v.clone())); }
        for (k, (_, sc)) in self.ctx.iter().enumerate() {
            if let Some(v) = sc.vars.get(name) { return Ok((Some(k), v.clone())); }
        }
        Err(format!("unknown name {name}"))
    }

    fn expr(&mut self, e: &Expr) -> Result<u64, String> {
        Ok(match e {
            Expr::Num(v) => self.lit(*v),
            Expr::Var(q, n, idx) => {
                let (k, v) = self.lookup(q, n)?;
                if v.dims.is_empty() {
                    if !idx.is_empty() && !self.f.scalar.contains(n) { return Err(format!("{n} is not an array")); }
                    match k { None => self.node((1, 0, v.slot as u64, 0, 0)), Some(k) => self.node((3, k as i64, v.slot as u64, 0, 0)) }
                } else {
                    let (ix, len) = self.index(&v.dims, idx, n)?;
                    match k { None => self.node((2, 0, v.slot as u64, len, ix)), Some(k) => self.node((4, k as i64, v.slot as u64, len, ix)) }
                }
            }
            Expr::Un(op, a) => {
                let a = self.expr(a)?;
                match *op { "-" => self.node((5, 0, a, 0, 0)), _ => self.node((5, 1, a, 0, 0)) }
            }
            Expr::Bin(op, a, b) => {
                let code = BOPS.iter().find(|(o, _)| o == op).ok_or(format!("operator {op} is not supported"))?.1;
                let a = self.expr(a)?;
                let b = self.expr(b)?;
                self.bin(code, a, b)
            }
            Expr::Cond(c, a, b) => {
                let c = self.expr(c)?;
                let a = self.expr(a)?;
                let b = self.expr(b)?;
                self.node((7, 0, c, a, b))
            }
            Expr::Call(f, args) => match (f.as_str(), args.len()) {
                ("Min", 2) => { let a = self.expr(&args[0])?; let b = self.expr(&args[1])?; self.bin(15, a, b) }
                ("Max", 2) => { let a = self.expr(&args[0])?; let b = self.expr(&args[1])?; self.bin(16, a, b) }
                ("Abs", 1) => { let a = self.expr(&args[0])?; self.node((5, 2, a, 0, 0)) }
                ("CeilLog2", 1) => { let a = self.expr(&args[0])?; self.node((5, 3, a, 0, 0)) }
                ("FloorLog2", 1) => { let a = self.expr(&args[0])?; self.node((5, 4, a, 0, 0)) }
                ("Ceil", 1) => match &args[0] {
                    Expr::Call(g, a2) if g == "Log2" && a2.len() == 1 => { let a = self.expr(&a2[0])?; self.node((5, 3, a, 0, 0)) }
                    _ => return Err("Ceil is supported only as Ceil( Log2( x ) )".into()),
                },
                ("Clip3", 3) => {
                    let lo = self.expr(&args[0])?; let hi = self.expr(&args[1])?; let x = self.expr(&args[2])?;
                    let m = self.bin(16, x, lo);
                    self.bin(15, m, hi)
                }
                _ => return Err(format!("function {f}/{} is not supported", args.len())),
            },
        })
    }

    fn dst(&mut self, name: &str, idx: &[Expr]) -> Result<(u64, u64, u64, u64), String> {
        if self.f.discard.contains(name) { return Ok((0, 0, 0, 0)); }
        let mangled = self.local(name);
        let name = mangled.as_str();
        let v = self.scope.vars.get(name).cloned().ok_or(format!("unknown name {name}"))?;
        if v.dims.is_empty() {
            if !idx.is_empty() && !self.f.scalar.contains(name) { return Err(format!("{name} is not declared an array")); }
            Ok((1, v.slot as u64, 0, 0))
        } else {
            let (ix, len) = self.index(&v.dims, idx, name)?;
            Ok((2, v.slot as u64, len, ix))
        }
    }

    fn label(&mut self, name: &str) -> u32 {
        if let Some(&l) = self.label_memo.get(name) { return l; }
        let l = self.labels.len() as u32;
        let vi = self.var_index.get(name).copied().unwrap_or(u32::MAX);
        self.labels.push((name.to_string(), vi));
        self.label_memo.insert(name.to_string(), l);
        l
    }

    fn block(&mut self, v: &[Stmt]) -> Result<u64, String> {
        let id = self.blocks.len();
        self.blocks.push(Vec::new());
        let mut out = Vec::new();
        for s in v { self.stmt(s, &mut out)?; }
        self.blocks[id] = out;
        Ok(id as u64)
    }

    fn stmt(&mut self, s: &Stmt, out: &mut Vec<(u8, u64, u64, u64, u64, u64, u32)>) -> Result<(), String> {
        match s {
            Stmt::Elem { name, idx, desc, checks, line } => {
                let (k, b, c, d) = self.dst(name, idx).map_err(|e| format!("line {line}: {e}"))?;
                let dcode = match desc {
                    Desc::U(w) => { let w = self.expr(w)?; w << 8 }
                    Desc::UE => 1,
                    Desc::SE => 2,
                    Desc::FF => 3,
                    Desc::SU(w) => { let w = self.expr(w)?; (w << 8) | 4 }
                    Desc::NS(w) => { let w = self.expr(w)?; (w << 8) | 5 }
                    Desc::LE(w) => { let w = self.expr(w)?; (w << 8) | 6 }
                    Desc::Uvlc => 7,
                    Desc::Leb128 => 8,
                };
                let lab = self.label(name);
                out.push((0, k, b, c, d, dcode, lab));
                let me = Expr::Var(None, name.clone(), idx.clone());
                let discarded = self.f.discard.contains(name);
                for ch in checks {
                    if discarded { return Err(format!("line {line}: a constraint on discarded {name}")); }
                    match ch {
                        Check::Range(lo, hi) => {
                            let e = Expr::Bin("&&", Box::new(Expr::Bin("<=", Box::new(lo.clone()), Box::new(me.clone()))),
                                              Box::new(Expr::Bin("<=", Box::new(me.clone()), Box::new(hi.clone()))));
                            let e = self.expr(&e)?;
                            out.push((2, 0, 0, 0, 0, e, 0));
                        }
                        Check::Eq(v) => {
                            let e = self.expr(&Expr::Bin("==", Box::new(me.clone()), Box::new(v.clone())))?;
                            out.push((2, 0, 0, 0, 0, e, 0));
                        }
                        Check::ConfEq(v) => {
                            let e = self.expr(&Expr::Bin("==", Box::new(me.clone()), Box::new(v.clone())))?;
                            out.push((3, 0, 0, 0, 0, e, 0));
                        }
                    }
                }
            }
            Stmt::Assign { name, idx, e } => {
                let ex = self.expr(e)?;
                let (k, b, c, d) = self.dst(name, idx)?;
                out.push((1, k, b, c, d, ex, 0));
            }
            Stmt::If(c, t, f) => {
                let c = self.expr(c)?;
                let t = self.block(t)?;
                let f = self.block(f)?;
                out.push((4, c, t, f, 0, 0, 0));
            }
            Stmt::While(c, b) => {
                let c = self.expr(c)?;
                let b = self.block(b)?;
                out.push((5, c, b, 0, 0, 0, 0));
            }
            Stmt::More(mn, mx, b) => {
                let b = self.block(b)?;
                let lab = self.label("more_rbsp_data");
                out.push((6, *mn, *mx, b, 0, 0, lab));
            }
            Stmt::Call(n, args, line) => {
                let sy = self.f.syntax.get(n).ok_or(format!("line {line}: no syntax structure {n}"))?;
                if sy.params.len() != args.len() {
                    return Err(format!("line {line}: {n} takes {} arguments", sy.params.len()));
                }
                let params = sy.params.clone();
                let scoped: Vec<bool> = params.iter().map(|p| sy.loop_vars.contains(p)).collect();
                for ((p, a), sc) in params.iter().zip(args).zip(scoped) {
                    let ex = self.expr(a)?;
                    let pn = if sc { format!("{n}.{p}") } else { p.clone() };
                    let (k, b, c, d) = self.dst(&pn, &[])?;
                    out.push((1, k, b, c, d, ex, 0));
                }
                let blk = self.callee(n)?;
                out.push((7, blk, 0, 0, 0, 0, 0));
            }
            Stmt::Align => out.push((8, 0, 0, 0, 0, 0, 0)),
            Stmt::ZAlign => out.push((10, 0, 0, 0, 0, 0, 0)),
            Stmt::Pos { name, idx } => {
                let (k, b, c, d) = self.dst(name, idx)?;
                out.push((9, k, b, c, d, 0, 0));
            }
            Stmt::Return(_) | Stmt::Break => return Err("a `return` or `break` left after lowering".into()),
            Stmt::Nop => {}
            Stmt::Assert(e) => { let e = self.expr(e)?; out.push((2, 0, 0, 0, 0, e, 0)); }
            Stmt::Conf(e) => { let e = self.expr(e)?; out.push((3, 0, 0, 0, 0, e, 0)); }
        }
        Ok(())
    }

    fn callee(&mut self, n: &str) -> Result<u64, String> {
        if let Some(&b) = self.callee_block.get(n) { return Ok(b); }
        if self.stack.iter().any(|s| s == n) { return Err(format!("recursive {n}")); }
        self.stack.push(n.to_string());
        let body = self.f.syntax[n].body.clone();
        let b = self.block(&body)?;
        self.stack.pop();
        self.callee_block.insert(n.to_string(), b);
        Ok(b)
    }
}

// --------------------------------------------------------------- emitting

struct Compiled {
    name: String,
    xs: Vec<(u8, i64, u64, u64, u64)>,
    sts: Vec<(u8, u64, u64, u64, u64, u64, u32)>,
    blocks: Vec<(u32, u32)>,
    nslots: u32,
    main: u64,
    vars: Vec<(String, u32, Vec<u32>)>,
    labels: Vec<(String, u32)>,
}

fn compile(f: &File) -> Result<Vec<Compiled>, String> {
    let mut scopes: HashMap<String, Scope> = HashMap::new();
    for p in &f.progs {
        scopes.insert(p.name.clone(), make_scope(f, &p.root).map_err(|e| format!("program {}: {e}", p.name))?);
    }
    let mut out = Vec::new();
    for p in &f.progs {
        let sc = make_scope(f, &p.root)?;
        let mut ctx = Vec::new();
        for u in &p.uses {
            let s = scopes.get(u).ok_or(format!("program {}: uses unknown program {u}", p.name))?;
            ctx.push((u.clone(), s));
        }
        let vars: Vec<(String, u32, Vec<u32>)> = sc.vars.iter().map(|(k, v)| (k.clone(), v.slot, v.dims.clone())).collect();
        let var_index: HashMap<String, u32> = vars.iter().enumerate().map(|(i, v)| (v.0.clone(), i as u32)).collect();
        let nslots = sc.nslots;
        let mut c = Comp {
            f, scope: sc, ctx, xs: Vec::new(), xmemo: HashMap::new(), blocks: Vec::new(),
            callee_block: HashMap::new(), labels: Vec::new(), label_memo: HashMap::new(), var_index, stack: Vec::new(),
        };
        // main: the arguments, then the root structure
        let root = f.syntax.get(&p.root).ok_or(format!("program {}: no syntax structure {}", p.name, p.root))?;
        let mut body = Vec::new();
        for (pa, a) in root.params.iter().zip(&p.args) {
            let pn = if root.loop_vars.contains(pa) { format!("{}.{pa}", p.root) } else { pa.clone() };
            body.push(Stmt::Assign { name: pn, idx: vec![], e: a.clone() });
        }
        body.push(Stmt::Call(p.root.clone(), vec![], 0));
        // `Call` with no arguments: the parameters were assigned above
        let main_id = c.blocks.len() as u64;
        c.blocks.push(Vec::new());
        let mut mb = Vec::new();
        for (tn, tv) in &f.tables {
            if c.scope.vars.contains_key(tn) {
                for (k, v) in tv.iter().enumerate() {
                    let st = Stmt::Assign { name: tn.clone(), idx: vec![Expr::Num(k as i64)], e: Expr::Num(*v) };
                    c.stmt(&st, &mut mb)?;
                }
            }
        }
        for s in &body[..body.len() - 1] { c.stmt(s, &mut mb).map_err(|e| format!("program {}: {e}", p.name))?; }
        let rb = c.callee(&p.root).map_err(|e| format!("program {}: {e}", p.name))?;
        mb.push((7, rb, 0, 0, 0, 0, 0));
        c.blocks[main_id as usize] = mb;
        let mut sts = Vec::new();
        let mut blocks = Vec::new();
        for b in &c.blocks {
            blocks.push((sts.len() as u32, b.len() as u32));
            sts.extend_from_slice(b);
        }
        out.push(Compiled { name: p.name.clone(), xs: c.xs, sts, blocks, nslots, main: main_id, vars, labels: c.labels });
    }
    Ok(out)
}

fn emit(src_name: &str, progs: &[Compiled]) -> String {
    let mut s = String::new();
    writeln!(s, "// Generated by vsync from `{src_name}`. Do not edit.").unwrap();
    writeln!(s, "#![allow(dead_code)]\nuse vsyn::raw::*;\n").unwrap();
    for p in progs {
        let up = p.name.to_uppercase();
        writeln!(s, "pub static {up}: RawProg = RawProg {{\n    name: {:?},", p.name).unwrap();
        write!(s, "    xs: &[").unwrap();
        for (i, x) in p.xs.iter().enumerate() {
            if i % 6 == 0 { write!(s, "\n        ").unwrap(); }
            write!(s, "({}, {}, {}, {}, {}), ", x.0, x.1, x.2, x.3, x.4).unwrap();
        }
        writeln!(s, "\n    ],").unwrap();
        write!(s, "    sts: &[").unwrap();
        for (i, x) in p.sts.iter().enumerate() {
            if i % 4 == 0 { write!(s, "\n        ").unwrap(); }
            write!(s, "({}, {}, {}, {}, {}, {}, {}), ", x.0, x.1, x.2, x.3, x.4, x.5, x.6).unwrap();
        }
        writeln!(s, "\n    ],").unwrap();
        write!(s, "    blocks: &[").unwrap();
        for (i, b) in p.blocks.iter().enumerate() {
            if i % 8 == 0 { write!(s, "\n        ").unwrap(); }
            write!(s, "({}, {}), ", b.0, b.1).unwrap();
        }
        writeln!(s, "\n    ],").unwrap();
        writeln!(s, "    nslots: {},\n    main: {},", p.nslots, p.main).unwrap();
        writeln!(s, "    vars: &[").unwrap();
        for v in &p.vars { writeln!(s, "        ({:?}, {}, &{:?}),", v.0, v.1, v.2).unwrap(); }
        writeln!(s, "    ],").unwrap();
        writeln!(s, "    labels: &[").unwrap();
        for l in &p.labels { writeln!(s, "        ({:?}, {}),", l.0, l.1).unwrap(); }
        writeln!(s, "    ],\n}};\n").unwrap();
    }
    s
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: vsync TABLES.syn OUT.rs");
        std::process::exit(2);
    }
    let src = std::fs::read_to_string(&args[1]).unwrap_or_else(|e| { eprintln!("{}: {e}", args[1]); std::process::exit(1) });
    let r = lex(&src)
        .and_then(|t| Parser { t, i: 0, loop_vars: HashSet::new(), consts: HashMap::new(), zalign: false, scoped: false, globals: HashSet::new() }.file())
        .and_then(|mut f| { lower(&mut f)?; Ok(f) })
        .and_then(|f| compile(&f));
    match r {
        Ok(progs) => {
            let name = std::path::Path::new(&args[1]).file_name().unwrap().to_string_lossy().to_string();
            std::fs::write(&args[2], emit(&name, &progs)).unwrap();
            for p in &progs {
                eprintln!("{}: {} expressions, {} statements, {} blocks, {} slots", p.name, p.xs.len(), p.sts.len(), p.blocks.len(), p.nslots);
            }
        }
        Err(e) => { eprintln!("{}: {e}", args[1]); std::process::exit(1); }
    }
}
