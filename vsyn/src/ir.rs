//! The syntax tables as data, and the arithmetic of their conditions.
//!
//! A program is what one syntax structure of H.264 §7.3 or H.265 §7.3
//! becomes: blocks of statements, and a pool of expressions the statements
//! point into. Its variables (the syntax elements, and the variables the
//! semantics clauses derive from them) are slots of one environment, a
//! sequence of integers. Arrays are runs of slots. The parameter sets a
//! structure depends on are read-only environments, the context.
//!
//! Expressions are the operators of H.264 §5 / H.265 §5, over integers:
//! every intermediate value must lie within ±2^48 (`vb`), and an operation
//! outside its domain (a division by zero, a `%` of a negative, an index
//! out of its array) fails. A failure is a decoding error in both
//! directions, so it never breaks the correspondence between the decoder
//! and the encoder; no syntax element or derived variable of either
//! standard comes near the bound.
use vstd::prelude::*;
use vbits::bitspec::*;
use crate::eg::*;
use crate::avd::*;

verus! {

pub open spec fn vb() -> int { 281474976710656int }

pub open spec fn inb(v: int) -> bool { -vb() <= v <= vb() }

pub open spec fn chk(v: int) -> Option<int> { if inb(v) { Some(v) } else { None } }

#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]
pub enum UOp {
    /// `−x`
    Neg,
    /// `!x`
    Not,
    /// `Abs( x )`
    Abs,
    /// `Ceil( Log2( x ) )`, for x ≥ 1
    CeilLog2,
    /// `FloorLog2( x )`, for x ≥ 1 (AV1 §4.7)
    FloorLog2,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Structural)]
pub enum BOp {
    Add, Sub, Mul,
    /// `/`: integer division with truncation toward zero (§5.7).
    Div,
    /// `%`: defined only for x ≥ 0 and y > 0.
    Mod,
    /// `<<` and `>>`, for shift amounts 0 to 48.
    Shl, Shr,
    Lt, Le, Gt, Ge, Eq, Ne,
    /// `&&` and `||`, short-circuit.
    And, Or,
    Min, Max,
    /// `&`, `|`, `^` on two's-complement integers (AV1 §4.5), for operands
    /// within ±2^48.
    BAnd, BOr, BXor,
}

pub enum Ex {
    Lit(int),
    /// A scalar variable.
    Slot(nat),
    /// `base[i]`: slot `base + i`, for 0 ≤ i < len, with `i` an expression.
    Elem(nat, nat, nat),
    /// A scalar of context environment `k`.
    CSlot(nat, nat),
    /// An array element of context environment `k`.
    CElem(nat, nat, nat, nat),
    Un(UOp, nat),
    Bin(BOp, nat, nat),
    /// `c ? a : b`
    Cond(nat, nat, nat),
}

/// Where a value goes: nowhere (it is only in the trace), a scalar, or an
/// array element.
pub enum Dst {
    Nil,
    Slot(nat),
    Elem(nat, nat, nat),
}

/// A descriptor. `u(n)`'s width is an expression (`u(v)`), 0 to 48; so
/// are `su(n)`'s (1 to 48), `ns(n)`'s range (1 to 2^40) and `le(n)`'s
/// bytes (0 to 6).
pub enum Desc {
    U(nat),
    UE,
    SE,
    FF,
    /// AV1 `su(n)`
    SU(nat),
    /// AV1 `ns(n)`
    NS(nat),
    /// AV1 `le(n)`
    LE(nat),
    /// AV1 `uvlc()`
    UVLC,
    /// AV1 `leb128()`
    LEB128,
}

pub enum St {
    /// A syntax element.
    Read(Dst, Desc),
    /// An assignment, as the syntax tables and the semantics clauses make
    /// them (`nextScale = ...`, and the derived variables).
    Let(Dst, nat),
    /// A constraint the decoder checks: "shall be in the range", and the
    /// like. False rejects.
    Assert(nat),
    /// A constraint on this version's bitstreams that a decoder must not
    /// reject: "shall be equal to 0 ... decoders shall ignore". False
    /// clears the conformance flag.
    Conf(nat),
    If(nat, nat, nat),
    /// `while( c ) body`; a `for` loop is an assignment, then this, with
    /// the step at the end of the body.
    While(nat, nat),
    /// `more_rbsp_data( )` loops: at least `min` and at most `max`
    /// iterations of the body; past `min`, one more exactly when data
    /// remains. `if( more_rbsp_data( ) )` is (0, 1), `do ... while` is
    /// (1, ∞). After it nothing may be read: the data is at its end.
    More(nat, nat, nat),
    /// A syntax structure used in another; its arguments are assignments
    /// before it.
    Call(nat),
    /// `byte_alignment( )` (H.265 §7.3.2.12): a 1, then 0s to a byte
    /// boundary.
    Align,
    /// `x = get_position( )` (AV1 §4.10): the bit position, from the start
    /// of the syntax structure.
    Pos(Dst),
    /// `byte_alignment( )` (AV1 §5.3.5): 0s to a byte boundary.
    ZAlign,
}

pub struct Prog {
    pub xs: Seq<Ex>,
    pub blocks: Seq<Seq<St>>,
    pub nslots: nat,
    pub main: nat,
}

pub type Ctx = Seq<Seq<int>>;

pub open spec fn ld(env: Seq<int>, i: int) -> Option<int> {
    if 0 <= i < env.len() { Some(env[i]) } else { None }
}

pub open spec fn b2i(b: bool) -> int { if b { 1 } else { 0 } }

pub open spec fn iabs(x: int) -> int { if x < 0 { -x } else { x } }

/// Integer division with truncation toward zero.
pub open spec fn tdiv(x: int, y: int) -> int {
    let q = iabs(x) / iabs(y);
    if (x >= 0) == (y > 0) { q } else { -q }
}

/// `Ceil( Log2( x ) )` for x ≥ 1.
pub open spec fn clog2(x: nat) -> nat {
    if x <= 1 { 0 } else { ilog2((x - 1) as nat) + 1 }
}

pub open spec fn un(op: UOp, x: int) -> Option<int> {
    match op {
        UOp::Neg => chk(-x),
        UOp::Not => Some(b2i(x == 0)),
        UOp::Abs => chk(iabs(x)),
        UOp::CeilLog2 => if x >= 1 { Some(clog2(x as nat) as int) } else { None },
        UOp::FloorLog2 => if x >= 1 { Some(ilog2(x as nat) as int) } else { None },
    }
}

/// The strict binary operators (all but `&&` and `||`).
pub open spec fn bin(op: BOp, x: int, y: int) -> Option<int> {
    match op {
        BOp::Add => chk(x + y),
        BOp::Sub => chk(x - y),
        BOp::Mul => chk(x * y),
        BOp::Div => if y != 0 { chk(tdiv(x, y)) } else { None },
        BOp::Mod => if x >= 0 && y > 0 { Some(x % y) } else { None },
        BOp::Shl => if 0 <= y <= 48 { chk(x * p2(y as nat)) } else { None },
        BOp::Shr => if 0 <= y <= 48 { Some(x / (p2(y as nat) as int)) } else { None },
        BOp::Lt => Some(b2i(x < y)),
        BOp::Le => Some(b2i(x <= y)),
        BOp::Gt => Some(b2i(x > y)),
        BOp::Ge => Some(b2i(x >= y)),
        BOp::Eq => Some(b2i(x == y)),
        BOp::Ne => Some(b2i(x != y)),
        BOp::And => Some(b2i(x != 0 && y != 0)),
        BOp::Or => Some(b2i(x != 0 || y != 0)),
        BOp::Min => Some(if x <= y { x } else { y }),
        BOp::Max => Some(if x >= y { x } else { y }),
        BOp::BAnd => if inb(x) && inb(y) { chk(((x as i64) & (y as i64)) as int) } else { None },
        BOp::BOr => if inb(x) && inb(y) { chk(((x as i64) | (y as i64)) as int) } else { None },
        BOp::BXor => if inb(x) && inb(y) { chk(((x as i64) ^ (y as i64)) as int) } else { None },
    }
}

/// An expression's value. Operands have lower indices than the node, so
/// the pool is a DAG evaluated bottom-up; a table that breaks this fails.
pub open spec fn eval(xs: Seq<Ex>, env: Seq<int>, ctx: Ctx, e: nat) -> Option<int>
    decreases e,
{
    if e >= xs.len() {
        None
    } else {
        match xs[e as int] {
            Ex::Lit(v) => chk(v),
            Ex::Slot(s) => ld(env, s as int),
            Ex::Elem(base, len, i) => if i < e {
                match eval(xs, env, ctx, i) {
                    Some(iv) => if 0 <= iv < len { ld(env, base + iv) } else { None },
                    None => None,
                }
            } else {
                None
            },
            Ex::CSlot(k, s) => if k < ctx.len() { ld(ctx[k as int], s as int) } else { None },
            Ex::CElem(k, base, len, i) => if i < e && k < ctx.len() {
                match eval(xs, env, ctx, i) {
                    Some(iv) => if 0 <= iv < len { ld(ctx[k as int], base + iv) } else { None },
                    None => None,
                }
            } else {
                None
            },
            Ex::Un(op, a) => if a < e {
                match eval(xs, env, ctx, a) {
                    Some(x) => un(op, x),
                    None => None,
                }
            } else {
                None
            },
            Ex::Bin(op, a, b) => if a < e && b < e {
                match eval(xs, env, ctx, a) {
                    Some(x) => if op == BOp::And && x == 0 {
                        Some(0)
                    } else if op == BOp::Or && x != 0 {
                        Some(1)
                    } else {
                        match eval(xs, env, ctx, b) {
                            Some(y) => bin(op, x, y),
                            None => None,
                        }
                    },
                    None => None,
                }
            } else {
                None
            },
            Ex::Cond(c, a, b) => if c < e && a < e && b < e {
                match eval(xs, env, ctx, c) {
                    Some(cv) => if cv != 0 { eval(xs, env, ctx, a) } else { eval(xs, env, ctx, b) },
                    None => None,
                }
            } else {
                None
            },
        }
    }
}

/// Storing a value.
pub open spec fn store(xs: Seq<Ex>, env: Seq<int>, ctx: Ctx, d: Dst, v: int) -> Option<Seq<int>> {
    match d {
        Dst::Nil => Some(env),
        Dst::Slot(s) => if s < env.len() { Some(env.update(s as int, v)) } else { None },
        Dst::Elem(base, len, i) => match eval(xs, env, ctx, i) {
            Some(iv) => if 0 <= iv < len && base + iv < env.len() {
                Some(env.update(base + iv, v))
            } else {
                None
            },
            None => None,
        },
    }
}

// ----------------------------------------------------------- descriptors

/// A descriptor with its width evaluated.
pub enum DV {
    U(nat),
    UE,
    SE,
    FF,
    SU(nat),
    NS(nat),
    LE(nat),
    UVLC,
    LEB128,
}

/// The largest `ns(n)` range.
pub open spec fn ns_max() -> nat { 1099511627776nat }

pub open spec fn desc_val(xs: Seq<Ex>, env: Seq<int>, ctx: Ctx, d: Desc) -> Option<DV> {
    match d {
        Desc::U(w) => match eval(xs, env, ctx, w) {
            Some(n) => if 0 <= n <= 48 { Some(DV::U(n as nat)) } else { None },
            None => None,
        },
        Desc::UE => Some(DV::UE),
        Desc::SE => Some(DV::SE),
        Desc::FF => Some(DV::FF),
        Desc::SU(w) => match eval(xs, env, ctx, w) {
            Some(n) => if 1 <= n <= 48 { Some(DV::SU(n as nat)) } else { None },
            None => None,
        },
        Desc::NS(w) => match eval(xs, env, ctx, w) {
            Some(n) => if 1 <= n <= ns_max() { Some(DV::NS(n as nat)) } else { None },
            None => None,
        },
        Desc::LE(w) => match eval(xs, env, ctx, w) {
            Some(n) => if 0 <= n <= 6 { Some(DV::LE(n as nat)) } else { None },
            None => None,
        },
        Desc::UVLC => Some(DV::UVLC),
        Desc::LEB128 => Some(DV::LEB128),
    }
}

/// The widths `desc_val` allows.
pub open spec fn dv_ok(d: DV) -> bool {
    match d {
        DV::U(n) => n <= 48,
        DV::SU(n) => 1 <= n <= 48,
        DV::NS(n) => 1 <= n <= ns_max(),
        DV::LE(n) => n <= 6,
        _ => true,
    }
}

pub proof fn lemma_desc_val_ok(xs: Seq<Ex>, env: Seq<int>, ctx: Ctx, d: Desc)
    requires desc_val(xs, env, ctx, d) is Some,
    ensures dv_ok(desc_val(xs, env, ctx, d).unwrap()),
{
}

/// Reading a syntax element from the front of `s`: its value, the choice
/// its encoding made, and its length. A choice is what an encoder may pick
/// freely for the same value (the number of bytes a `leb128()` spends);
/// for a descriptor with one code per value, it is always 0.
pub open spec fn dparse(d: DV, s: Seq<bool>) -> Option<(int, nat, nat)> {
    match d {
        DV::U(n) => match u_parse(s, n) {
            Some((v, k)) => Some((v as int, 0, k)),
            None => None,
        },
        DV::UE => match ue_parse(s) {
            Some((v, k)) => Some((v as int, 0, k)),
            None => None,
        },
        DV::SE => match se_parse(s) {
            Some((v, k)) => Some((v, 0, k)),
            None => None,
        },
        DV::FF => match ff_parse(s) {
            Some((v, k)) => if v <= vb() { Some((v as int, 0, k)) } else { None },
            None => None,
        },
        DV::SU(n) => match su_parse(s, n) {
            Some((v, k)) => Some((v, 0, k)),
            None => None,
        },
        DV::NS(n) => match ns_parse(s, n) {
            Some((v, k)) => Some((v as int, 0, k)),
            None => None,
        },
        DV::LE(n) => match le_parse(s, n) {
            Some((v, k)) => Some((v as int, 0, k)),
            None => None,
        },
        DV::UVLC => match uvlc_parse(s) {
            Some((v, w, k)) => Some((v as int, w, k)),
            None => None,
        },
        // §4.10.5: the value shall be at most 2^32 − 1
        DV::LEB128 => match leb_parse(s, 0) {
            Some((v, k)) => if v <= uvlc_max() { Some((v as int, (k - leb_min(v)) as nat, 8 * k)) } else { None },
            None => None,
        },
    }
}

/// Writing one: its code, when the value is in the descriptor's domain and
/// the choice is one it has. Choice 0 is the canonical code.
pub open spec fn dcode(d: DV, v: int, w: nat) -> Option<Seq<bool>> {
    match d {
        DV::U(n) => if w == 0 && 0 <= v < p2(n) { Some(u_code(v as nat, n)) } else { None },
        DV::UE => if w == 0 && 0 <= v <= ue_max() { Some(ue_code(v as nat)) } else { None },
        DV::SE => if w == 0 && -se_max() <= v <= se_max() { Some(se_code(v)) } else { None },
        DV::FF => if w == 0 && 0 <= v <= vb() { Some(ff_code(v as nat)) } else { None },
        DV::SU(n) => if w == 0 && su_in(v, n) { Some(su_code(v, n)) } else { None },
        DV::NS(n) => if w == 0 && 0 <= v < n { Some(ns_code(v as nat, n)) } else { None },
        DV::LE(n) => if w == 0 && 0 <= v < p2(8 * n) { Some(le_code(v as nat, n)) } else { None },
        DV::UVLC => if v >= 0 { uvlc_code(v as nat, w) } else { None },
        DV::LEB128 => if 0 <= v <= uvlc_max() && leb_min(v as nat) + w <= 8 {
            Some(leb_code(v as nat, leb_min(v as nat) + w))
        } else {
            None
        },
    }
}

/// A descriptor with one code per value: every choice it reads is 0.
pub open spec fn dv_rigid(d: DV) -> bool {
    !(d is UVLC || d is LEB128)
}

pub open spec fn desc_rigid(d: Desc) -> bool {
    !(d is UVLC || d is LEB128)
}

proof fn lemma_ns_w_small(n: nat)
    requires 1 <= n <= ns_max(),
    ensures ns_w(n) <= 41,
{
    lemma_ilog2(n);
    assert(p2(40) == ns_max()) by {
        reveal_with_fuel(p2, 9);
        assert(p2(8) == 256);
        lemma_p2_adds(8, 8);
        lemma_p2_adds(16, 8);
        lemma_p2_adds(24, 8);
        lemma_p2_adds(32, 8);
    }
    if ilog2(n) > 40 {
        lemma_p2_mono_strict(40, ilog2(n));
    }
}

pub proof fn lemma_desc_rt(d: DV, v: int, w: nat, c: Seq<bool>, rest: Seq<bool>)
    requires dcode(d, v, w) == Some(c), dv_ok(d),
    ensures dparse(d, c + rest) == Some((v, w, c.len())),
{
    match d {
        DV::U(n) => { lemma_u_rt(v as nat, n, rest); }
        DV::UE => { lemma_ue_rt(v as nat, rest); }
        DV::SE => { lemma_se_rt(v, rest); }
        DV::FF => { lemma_ff_rt(v as nat, rest); }
        DV::SU(n) => { lemma_su_rt(v, n, rest); }
        DV::NS(n) => { lemma_ns_w_small(n); lemma_ns_rt(v as nat, n, rest); }
        DV::LE(n) => { lemma_le_rt(v as nat, n, rest); }
        DV::UVLC => { lemma_uvlc_rt(v as nat, w, rest); }
        DV::LEB128 => {
            let k = leb_min(v as nat) + w;
            lemma_leb_min(v as nat, k);
            lemma_leb_rt(v as nat, k, 0, rest);
        }
    }
}

pub proof fn lemma_desc_inv(d: DV, s: Seq<bool>)
    requires dparse(d, s) is Some, dv_ok(d),
    ensures ({
        let (v, w, k) = dparse(d, s).unwrap();
        &&& k <= s.len()
        &&& dcode(d, v, w) == Some(s.take(k as int))
        &&& inb(v)
        &&& w <= s.len()
        &&& dv_rigid(d) ==> w == 0
    }),
{
    lemma_p2_32();
    crate::xir::lemma_p2_48();
    match d {
        DV::U(n) => {
            lemma_u_inv(s, n);
            vbits::prim_read::lemma_p2_mono(n, 48);
        }
        DV::UE => { lemma_ue_inv(s); }
        DV::SE => { lemma_se_inv(s); }
        DV::FF => { lemma_ff_inv(s); }
        DV::SU(n) => {
            lemma_su_inv(s, n);
            vbits::prim_read::lemma_p2_mono((n - 1) as nat, 48);
        }
        DV::NS(n) => {
            lemma_ns_w_small(n);
            lemma_ns_inv(s, n);
            vbits::prim_read::lemma_p2_mono(40, 48);
            assert(p2(40) == ns_max()) by {
                reveal_with_fuel(p2, 9);
                assert(p2(8) == 256);
                lemma_p2_adds(32, 8);
            }
        }
        DV::LE(n) => {
            lemma_le_inv(s, n);
            vbits::prim_read::lemma_p2_mono(8 * n, 48);
        }
        DV::UVLC => { lemma_uvlc_inv(s); }
        DV::LEB128 => {
            lemma_leb_inv(s, 0);
            let (v, k) = leb_parse(s, 0).unwrap();
            lemma_leb_min(v, k);
        }
    }
}

/// A value with a code has a canonical one.
pub proof fn lemma_desc_canon(d: DV, v: int, w: nat)
    requires dcode(d, v, w) is Some,
    ensures dcode(d, v, 0) is Some,
{
}

pub proof fn lemma_desc_val_rigid(xs: Seq<Ex>, env: Seq<int>, ctx: Ctx, d: Desc)
    requires desc_val(xs, env, ctx, d) is Some, desc_rigid(d),
    ensures dv_rigid(desc_val(xs, env, ctx, d).unwrap()),
{
}

/// `byte_alignment( )` at bit position `pos`.
pub open spec fn align_code(pos: nat) -> Seq<bool> {
    seq![true] + zeros(((8 - (pos + 1) % 8) % 8) as nat)
}

/// AV1's `byte_alignment( )` at bit position `pos`.
pub open spec fn zalign_code(pos: nat) -> Seq<bool> {
    zeros(((8 - pos % 8) % 8) as nat)
}

} // verus!
