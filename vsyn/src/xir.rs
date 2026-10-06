//! The tables as executable data, and expression evaluation proved equal
//! to `ir::eval`.
use vstd::prelude::*;
use vbits::bitspec::*;
use crate::eg::*;
use crate::ir::*;
use crate::sem::Tr;
use crate::bits::*;

verus! {

pub enum ExX {
    Lit(i64),
    Slot(usize),
    Elem(usize, usize, usize),
    CSlot(usize, usize),
    CElem(usize, usize, usize, usize),
    Un(UOp, usize),
    Bin(BOp, usize, usize),
    Cond(usize, usize, usize),
}

pub enum DstX {
    Nil,
    Slot(usize),
    Elem(usize, usize, usize),
}

pub enum DescX {
    U(usize),
    UE,
    SE,
    FF,
    SU(usize),
    NS(usize),
    LE(usize),
    UVLC,
    LEB128,
}

pub enum StX {
    Read(DstX, DescX),
    Let(DstX, usize),
    Assert(usize),
    Conf(usize),
    If(usize, usize, usize),
    While(usize, usize),
    More(u64, u64, usize),
    Call(usize),
    Align,
    Pos(DstX),
    ZAlign,
}

pub struct ProgX {
    pub xs: Vec<ExX>,
    pub blocks: Vec<Vec<StX>>,
    pub nslots: usize,
    pub main: usize,
}

pub open spec fn ex_view(x: ExX) -> Ex {
    match x {
        ExX::Lit(v) => Ex::Lit(v as int),
        ExX::Slot(s) => Ex::Slot(s as nat),
        ExX::Elem(b, l, i) => Ex::Elem(b as nat, l as nat, i as nat),
        ExX::CSlot(k, s) => Ex::CSlot(k as nat, s as nat),
        ExX::CElem(k, b, l, i) => Ex::CElem(k as nat, b as nat, l as nat, i as nat),
        ExX::Un(op, a) => Ex::Un(op, a as nat),
        ExX::Bin(op, a, b) => Ex::Bin(op, a as nat, b as nat),
        ExX::Cond(c, a, b) => Ex::Cond(c as nat, a as nat, b as nat),
    }
}

pub open spec fn dst_view(d: DstX) -> Dst {
    match d {
        DstX::Nil => Dst::Nil,
        DstX::Slot(s) => Dst::Slot(s as nat),
        DstX::Elem(b, l, i) => Dst::Elem(b as nat, l as nat, i as nat),
    }
}

pub open spec fn desc_view(d: DescX) -> Desc {
    match d {
        DescX::U(w) => Desc::U(w as nat),
        DescX::UE => Desc::UE,
        DescX::SE => Desc::SE,
        DescX::FF => Desc::FF,
        DescX::SU(w) => Desc::SU(w as nat),
        DescX::NS(w) => Desc::NS(w as nat),
        DescX::LE(w) => Desc::LE(w as nat),
        DescX::UVLC => Desc::UVLC,
        DescX::LEB128 => Desc::LEB128,
    }
}

pub open spec fn st_view(s: StX) -> St {
    match s {
        StX::Read(d, ds) => St::Read(dst_view(d), desc_view(ds)),
        StX::Let(d, e) => St::Let(dst_view(d), e as nat),
        StX::Assert(e) => St::Assert(e as nat),
        StX::Conf(e) => St::Conf(e as nat),
        StX::If(c, t, f) => St::If(c as nat, t as nat, f as nat),
        StX::While(c, b) => St::While(c as nat, b as nat),
        StX::More(mn, mx, b) => St::More(mn as nat, mx as nat, b as nat),
        StX::Call(b) => St::Call(b as nat),
        StX::Align => St::Align,
        StX::Pos(d) => St::Pos(dst_view(d)),
        StX::ZAlign => St::ZAlign,
    }
}

pub open spec fn xs_view(xs: Seq<ExX>) -> Seq<Ex> {
    Seq::new(xs.len(), |i: int| ex_view(xs[i]))
}

pub open spec fn blk_view(b: Seq<StX>) -> Seq<St> {
    Seq::new(b.len(), |i: int| st_view(b[i]))
}

impl ProgX {
    pub open spec fn view(&self) -> Prog {
        Prog {
            xs: xs_view(self.xs@),
            blocks: Seq::new(self.blocks@.len(), |i: int| blk_view(self.blocks@[i]@)),
            nslots: self.nslots as nat,
            main: self.main as nat,
        }
    }
}

pub fn desc_rigid_x(d: &DescX) -> (r: bool)
    ensures r == desc_rigid(desc_view(*d)),
{
    match d {
        DescX::UVLC | DescX::LEB128 => false,
        _ => true,
    }
}

/// Whether no syntax element of the program has a choice: then each value
/// has one code (`rt::theorem_rigid`).
pub fn rigid_x(p: &ProgX) -> (r: bool)
    ensures r == crate::sem::prog_rigid(p@),
{
    let ghost pp = p@;
    let mut i: usize = 0;
    while i < p.blocks.len()
        invariant
            i <= p.blocks@.len(), pp == p@,
            forall|a: int, b: int| 0 <= a < i && 0 <= b < pp.blocks[a].len()
                ==> (#[trigger] pp.blocks[a][b] is Read ==> desc_rigid(pp.blocks[a][b]->Read_1)),
        decreases p.blocks@.len() - i,
    {
        let blk = &p.blocks[i];
        proof { assert(pp.blocks[i as int] == blk_view(blk@)); }
        let mut j: usize = 0;
        while j < blk.len()
            invariant
                i < p.blocks@.len(), j <= blk@.len(), pp == p@, blk == &p.blocks@[i as int],
                pp.blocks[i as int] == blk_view(blk@),
                forall|a: int, b: int| 0 <= a < i && 0 <= b < pp.blocks[a].len()
                    ==> (#[trigger] pp.blocks[a][b] is Read ==> desc_rigid(pp.blocks[a][b]->Read_1)),
                forall|b: int| 0 <= b < j
                    ==> (#[trigger] pp.blocks[i as int][b] is Read ==> desc_rigid(pp.blocks[i as int][b]->Read_1)),
            decreases blk@.len() - j,
        {
            proof { assert(pp.blocks[i as int][j as int] == st_view(blk@[j as int])); }
            match &blk[j] {
                StX::Read(_, d) => {
                    if !desc_rigid_x(d) {
                        return false;
                    }
                }
                _ => {}
            }
            j = j + 1;
        }
        i = i + 1;
    }
    true
}

pub open spec fn iview(v: Seq<i64>) -> Seq<int> {
    Seq::new(v.len(), |i: int| v[i] as int)
}

/// An executable trace: each value with its choice.
pub open spec fn tview(t: Seq<(i64, u64)>) -> Tr {
    Seq::new(t.len(), |i: int| (t[i].0 as int, t[i].1 as nat))
}

pub open spec fn nview(v: Seq<u64>) -> Seq<nat> {
    Seq::new(v.len(), |i: int| v[i] as nat)
}

pub open spec fn cview(c: Seq<Vec<i64>>) -> Ctx {
    Seq::new(c.len(), |k: int| iview(c[k]@))
}

pub open spec fn oview(r: Option<i64>) -> Option<int> {
    match r {
        Some(v) => Some(v as int),
        None => None,
    }
}

pub open spec fn ib(v: i128) -> bool { -281474976710656 <= v <= 281474976710656 }

fn chk_x(v: i128) -> (r: Option<i64>)
    ensures oview(r) == chk(v as int),
{
    if -281474976710656i128 <= v && v <= 281474976710656i128 { Some(v as i64) } else { None }
}

fn b2i_x(b: bool) -> (r: i64)
    ensures r as int == b2i(b),
{
    if b { 1 } else { 0 }
}

fn pow2_x(y: u64) -> (r: u64)
    requires y <= 48,
    ensures r as nat == p2(y as nat), r <= 281474976710656,
{
    proof {
        vbits::prim_read::lemma_p2_eq_pow2(y as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(y as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, y);
        vbits::prim_read::lemma_p2_mono(y as nat, 48);
        lemma_p2_48();
    }
    1u64 << y
}

pub proof fn lemma_p2_48()
    ensures p2(48) == 281474976710656nat,
{
    lemma_p2_32();
    reveal_with_fuel(p2, 9);
    assert(p2(8) == 256);
    lemma_p2_adds(8, 8);
    lemma_p2_adds(32, 16);
}

fn un_x(op: UOp, x: i64) -> (r: Option<i64>)
    ensures oview(r) == un(op, x as int),
{
    match op {
        UOp::Neg => chk_x(-(x as i128)),
        UOp::Not => Some(b2i_x(x == 0)),
        UOp::Abs => chk_x(if x < 0 { -(x as i128) } else { x as i128 }),
        UOp::CeilLog2 => {
            if x < 1 {
                None
            } else if x == 1 {
                Some(0)
            } else {
                let l = ilog2_x((x - 1) as u64);
                Some((l + 1) as i64)
            }
        }
        UOp::FloorLog2 => {
            if x < 1 {
                None
            } else {
                let l = ilog2_x(x as u64);
                Some(l as i64)
            }
        }
    }
}

fn bin_x(op: BOp, x: i64, y: i64) -> (r: Option<i64>)
    ensures oview(r) == bin(op, x as int, y as int),
{
    let xw = x as i128;
    let yw = y as i128;
    match op {
        BOp::Add => chk_x(xw + yw),
        BOp::Sub => chk_x(xw - yw),
        BOp::Mul => {
            assert(-0x4000_0000_0000_0000_0000_0000_0000_0000int <= x as int * y as int <= 0x4000_0000_0000_0000_0000_0000_0000_0000int) by (nonlinear_arith)
                requires -0x8000_0000_0000_0000int <= x <= 0x7fff_ffff_ffff_ffffint,
                         -0x8000_0000_0000_0000int <= y <= 0x7fff_ffff_ffff_ffffint;
            chk_x(xw * yw)
        }
        BOp::Div => {
            if y == 0 {
                None
            } else {
                let ax: u128 = if x < 0 { (-xw) as u128 } else { xw as u128 };
                let ay: u128 = if y < 0 { (-yw) as u128 } else { yw as u128 };
                let q: u128 = ax / ay;
                proof {
                    assert(q <= ax) by (nonlinear_arith) requires q == ax / ay, ay >= 1;
                }
                let qi = q as i128;
                if (x >= 0) == (y > 0) { chk_x(qi) } else { chk_x(-qi) }
            }
        }
        BOp::Mod => {
            if x >= 0 && y > 0 {
                let m = (x as u64) % (y as u64);
                proof { assert(m < y as u64); }
                Some(m as i64)
            } else {
                None
            }
        }
        BOp::Shl => {
            if 0 <= y && y <= 48 {
                let p = pow2_x(y as u64);
                assert(-0x8000_0000_0000_0000int * 281474976710656 <= x as int * p as int <= 0x8000_0000_0000_0000int * 281474976710656) by (nonlinear_arith)
                    requires -0x8000_0000_0000_0000int <= x <= 0x7fff_ffff_ffff_ffffint, 0 <= p <= 281474976710656;
                chk_x(xw * (p as i128))
            } else {
                None
            }
        }
        BOp::Shr => {
            if 0 <= y && y <= 48 {
                let p = pow2_x(y as u64);
                proof { lemma_p2_pos(y as nat); }
                if x >= 0 {
                    let q = (x as u64) / p;
                    proof { assert(q <= x as u64) by (nonlinear_arith) requires q == (x as u64) / p, p >= 1; }
                    Some(q as i64)
                } else {
                    let nx: u128 = (-xw) as u128;
                    let q: u128 = (nx + (p as u128) - 1) / (p as u128);
                    proof {
                        lemma_floor_neg(x as int, p as int, q as int);
                        assert(q as int <= nx as int) by (nonlinear_arith) requires q as int == (nx as int + p as int - 1) / (p as int), p >= 1, nx >= 1;
                    }
                    Some((-(q as i128)) as i64)
                }
            } else {
                None
            }
        }
        BOp::Lt => Some(b2i_x(x < y)),
        BOp::Le => Some(b2i_x(x <= y)),
        BOp::Gt => Some(b2i_x(x > y)),
        BOp::Ge => Some(b2i_x(x >= y)),
        BOp::Eq => Some(b2i_x(x == y)),
        BOp::Ne => Some(b2i_x(x != y)),
        BOp::And => Some(b2i_x(x != 0 && y != 0)),
        BOp::Or => Some(b2i_x(x != 0 || y != 0)),
        BOp::Min => Some(if x <= y { x } else { y }),
        BOp::Max => Some(if x >= y { x } else { y }),
        BOp::BAnd | BOp::BOr | BOp::BXor => {
            if x < -281474976710656i64 || x > 281474976710656i64 || y < -281474976710656i64 || y > 281474976710656i64 {
                return None;
            }
            let r: i64 = match op { BOp::BAnd => x & y, BOp::BOr => x | y, _ => x ^ y };
            chk_x(r as i128)
        }
    }
}

/// Floor division of a negative by a positive, from a ceiling division of
/// its magnitude.
proof fn lemma_floor_neg(x: int, p: int, q: int)
    requires x < 0, p >= 1, q == (-x + p - 1) / p,
    ensures x / p == -q,
{
    let n = -x;
    let r = (n + p - 1) % p;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n + p - 1, p);
    assert(n + p - 1 == p * q + r);
    assert(0 <= r < p);
    // -q * p <= x < (-q + 1) * p
    assert(p * (-q) <= x) by (nonlinear_arith) requires n + p - 1 == p * q + r, r < p, x == -n, p >= 1;
    assert(x < p * (-q) + p) by (nonlinear_arith) requires n + p - 1 == p * q + r, r >= 0, x == -n;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x, p, -q, x - p * (-q));
}

/// `ld` on an executable environment.
fn ld_x(env: &Vec<i64>, base: usize, iv: i64) -> (r: Option<i64>)
    requires iv >= 0,
    ensures oview(r) == ld(iview(env@), base as int + iv as int),
{
    if base >= env.len() || (iv as u64) >= ((env.len() - base) as u64) {
        return None;
    }
    Some(env[base + iv as usize])
}

pub fn eval_x(xs: &Vec<ExX>, env: &Vec<i64>, ctx: &Vec<Vec<i64>>, e: usize) -> (r: Option<i64>)
    ensures oview(r) == eval(xs_view(xs@), iview(env@), cview(ctx@), e as nat),
    decreases e,
{
    let ghost sx = xs_view(xs@);
    let ghost senv = iview(env@);
    let ghost sctx = cview(ctx@);
    if e >= xs.len() {
        return None;
    }
    proof { assert(sx[e as int] == ex_view(xs@[e as int])); }
    match &xs[e] {
        ExX::Lit(v) => chk_x(*v as i128),
        ExX::Slot(s) => ld_x(env, *s, 0),
        ExX::Elem(base, len, i) => {
            if *i >= e {
                return None;
            }
            match eval_x(xs, env, ctx, *i) {
                Some(iv) => {
                    if 0 <= iv && (iv as u64) < (*len as u64) { ld_x(env, *base, iv) } else { None }
                }
                None => None,
            }
        }
        ExX::CSlot(k, s) => {
            if *k >= ctx.len() {
                return None;
            }
            proof { assert(sctx[*k as int] == iview(ctx@[*k as int]@)); }
            ld_x(&ctx[*k], *s, 0)
        }
        ExX::CElem(k, base, len, i) => {
            if *i >= e || *k >= ctx.len() {
                return None;
            }
            proof { assert(sctx[*k as int] == iview(ctx@[*k as int]@)); }
            match eval_x(xs, env, ctx, *i) {
                Some(iv) => {
                    if 0 <= iv && (iv as u64) < (*len as u64) { ld_x(&ctx[*k], *base, iv) } else { None }
                }
                None => None,
            }
        }
        ExX::Un(op, a) => {
            if *a >= e {
                return None;
            }
            match eval_x(xs, env, ctx, *a) {
                Some(x) => un_x(*op, x),
                None => None,
            }
        }
        ExX::Bin(op, a, b) => {
            if *a >= e || *b >= e {
                return None;
            }
            match eval_x(xs, env, ctx, *a) {
                Some(x) => {
                    if *op == BOp::And && x == 0 {
                        Some(0)
                    } else if *op == BOp::Or && x != 0 {
                        Some(1)
                    } else {
                        match eval_x(xs, env, ctx, *b) {
                            Some(y) => bin_x(*op, x, y),
                            None => None,
                        }
                    }
                }
                None => None,
            }
        }
        ExX::Cond(c, a, b) => {
            if *c >= e || *a >= e || *b >= e {
                return None;
            }
            match eval_x(xs, env, ctx, *c) {
                Some(cv) => if cv != 0 { eval_x(xs, env, ctx, *a) } else { eval_x(xs, env, ctx, *b) },
                None => None,
            }
        }
    }
}

/// `store`, in place: on success the environment is updated.
pub fn store_x(xs: &Vec<ExX>, env: &mut Vec<i64>, ctx: &Vec<Vec<i64>>, d: &DstX, v: i64) -> (ok: bool)
    ensures
        ok == store(xs_view(xs@), iview(old(env)@), cview(ctx@), dst_view(*d), v as int) is Some,
        ok ==> Some(iview(final(env)@)) == store(xs_view(xs@), iview(old(env)@), cview(ctx@), dst_view(*d), v as int),
{
    match d {
        DstX::Nil => true,
        DstX::Slot(s) => {
            if *s < env.len() {
                env.set(*s, v);
                proof { assert(iview(env@) =~= iview(old(env)@).update(*s as int, v as int)); }
                true
            } else {
                false
            }
        }
        DstX::Elem(base, len, i) => {
            match eval_x(xs, env, ctx, *i) {
                Some(iv) => {
                    if iv < 0 || (iv as u64) >= (*len as u64) || *base >= env.len()
                        || (iv as u64) >= ((env.len() - *base) as u64) {
                        return false;
                    }
                    let j = *base + iv as usize;
                    env.set(j, v);
                    proof { assert(iview(env@) =~= iview(old(env)@).update(j as int, v as int)); }
                    true
                }
                None => false,
            }
        }
    }
}

} // verus!
