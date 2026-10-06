//! The tables as `vsync` writes them, and their conversion to `ProgX`.
//! Nothing here needs checking: the theorems of `rt` hold for every
//! program, and the interpreter checks every index it follows.
use crate::ir::{UOp, BOp};
use crate::xir::*;

/// An expression node: (tag, a, b, c, d).
/// 0 Lit(a) · 1 Slot(b) · 2 Elem(b base, c len, d index) · 3 CSlot(a ctx, b slot)
/// · 4 CElem(a ctx, b base, c len, d index) · 5 Un(a op, b) · 6 Bin(a op, b, c) · 7 Cond(b, c, d)
pub type RawEx = (u8, i64, u64, u64, u64);

/// A statement: (tag, a, b, c, d, e, label).
/// 0 Read: a dst kind (0 nil, 1 slot, 2 elem), b slot or base, c len, d index; e desc (0 u, 1 ue, 2 se, 3 ff, 4 su, 5 ns, 6 le, 7 uvlc, 8 leb128) | width << 8
/// · 1 Let: dst as Read, e expr · 2 Assert(e) · 3 Conf(e) · 4 If(a cond, b then, c else)
/// · 5 While(a cond, b body) · 6 More(a min, b max, c body) · 7 Call(a block) · 8 Align
/// · 9 Pos: dst as Read · 10 ZAlign (AV1's `byte_alignment( )`)
pub type RawSt = (u8, u64, u64, u64, u64, u64, u32);

pub struct RawProg {
    pub name: &'static str,
    pub xs: &'static [RawEx],
    pub sts: &'static [RawSt],
    /// Each block: (first statement, how many).
    pub blocks: &'static [(u32, u32)],
    pub nslots: usize,
    pub main: usize,
    /// Variables: (name, first slot, dimensions); a scalar has none.
    pub vars: &'static [(&'static str, u32, &'static [u32])],
    /// Syntax element names, by a Read's label: (name, variable index or u32::MAX).
    pub labels: &'static [(&'static str, u32)],
}

fn uop(a: i64) -> UOp {
    match a { 0 => UOp::Neg, 1 => UOp::Not, 2 => UOp::Abs, 3 => UOp::CeilLog2, _ => UOp::FloorLog2 }
}

fn bop(a: i64) -> BOp {
    match a {
        0 => BOp::Add, 1 => BOp::Sub, 2 => BOp::Mul, 3 => BOp::Div, 4 => BOp::Mod,
        5 => BOp::Shl, 6 => BOp::Shr, 7 => BOp::Lt, 8 => BOp::Le, 9 => BOp::Gt,
        10 => BOp::Ge, 11 => BOp::Eq, 12 => BOp::Ne, 13 => BOp::And, 14 => BOp::Or,
        15 => BOp::Min, 16 => BOp::Max, 17 => BOp::BAnd, 18 => BOp::BOr, _ => BOp::BXor,
    }
}

fn dst(kind: u64, b: u64, c: u64, d: u64) -> DstX {
    match kind {
        0 => DstX::Nil,
        1 => DstX::Slot(b as usize),
        _ => DstX::Elem(b as usize, c as usize, d as usize),
    }
}

impl RawProg {
    pub fn to_prog(&self) -> ProgX {
        let xs = self.xs.iter().map(|&(t, a, b, c, d)| match t {
            0 => ExX::Lit(a),
            1 => ExX::Slot(b as usize),
            2 => ExX::Elem(b as usize, c as usize, d as usize),
            3 => ExX::CSlot(a as usize, b as usize),
            4 => ExX::CElem(a as usize, b as usize, c as usize, d as usize),
            5 => ExX::Un(uop(a), b as usize),
            6 => ExX::Bin(bop(a), b as usize, c as usize),
            _ => ExX::Cond(b as usize, c as usize, d as usize),
        }).collect();
        let blocks = self.blocks.iter().map(|&(s, n)| {
            self.sts[s as usize..(s + n) as usize].iter().map(|&(t, a, b, c, d, e, _)| match t {
                0 => {
                    let desc = match e & 0xff {
                        0 => DescX::U((e >> 8) as usize),
                        1 => DescX::UE,
                        2 => DescX::SE,
                        3 => DescX::FF,
                        4 => DescX::SU((e >> 8) as usize),
                        5 => DescX::NS((e >> 8) as usize),
                        6 => DescX::LE((e >> 8) as usize),
                        7 => DescX::UVLC,
                        _ => DescX::LEB128,
                    };
                    StX::Read(dst(a, b, c, d), desc)
                }
                1 => StX::Let(dst(a, b, c, d), e as usize),
                2 => StX::Assert(e as usize),
                3 => StX::Conf(e as usize),
                4 => StX::If(a as usize, b as usize, c as usize),
                5 => StX::While(a as usize, b as usize),
                6 => StX::More(a, b, c as usize),
                7 => StX::Call(a as usize),
                8 => StX::Align,
                9 => StX::Pos(dst(a, b, c, d)),
                _ => StX::ZAlign,
            }).collect()
        }).collect();
        ProgX { xs, blocks, nslots: self.nslots, main: self.main }
    }

    /// The slot of a scalar variable, by name.
    pub fn slot(&self, name: &str) -> Option<usize> {
        self.vars.iter().find(|v| v.0 == name).map(|v| v.1 as usize)
    }
}
