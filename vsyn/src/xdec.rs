//! The executable decoder: it interprets the tables, and each function is
//! proved to return exactly what its `sem` counterpart does: `true` with
//! the same state and trace when the spec decodes, `false` when it fails.
use vstd::prelude::*;
use vbits::bitspec::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::prim_write::{bits_seq, lemma_bits_seq_of_val};
use crate::eg::*;
use crate::avd::*;
#[cfg(verus_keep_ghost)]
use crate::avx::lemma_ilog2_40;
use crate::ir::*;
use crate::sem::*;
use crate::bits::*;
use crate::xir::*;

verus! {

pub struct DStX {
    pub env: Vec<i64>,
    pub sealed: bool,
    pub conf: bool,
}

pub open spec fn dview(st: DStX, pos: usize) -> DSt {
    DSt { env: iview(st.env@), pos: pos as nat, sealed: st.sealed, conf: st.conf }
}

pub open spec fn tcat(r: Option<(DSt, Tr)>, acc: Tr) -> Option<(DSt, Tr)> {
    match r {
        Some((s, t)) => Some((s, acc + t)),
        None => None,
    }
}

pub open spec fn tcat3(r: Option<(DSt, nat, Tr)>, acc: Tr) -> Option<(DSt, nat, Tr)> {
    match r {
        Some((s, n, t)) => Some((s, n, acc + t)),
        None => None,
    }
}
proof fn lemma_tview_push(t: Seq<(i64, u64)>, v: i64, w: u64)
    ensures tview(t.push((v, w))) =~= tview(t) + seq![(v as int, w as nat)],
{
}

/// All-zero bits read as 0, and only they.
proof fn lemma_zero_val(s: Seq<bool>)
    requires s.len() <= 64,
    ensures (bits_val(s) == 0) == (s =~= zeros(s.len())),
{
    lemma_bits_seq_of_val(s);
    lemma_zeros_bits_seq(s.len());
    if s =~= zeros(s.len()) {
        vbits::prim_write::lemma_bits_seq_val(0u64, s.len());
        lemma_p2_pos(s.len());
    }
}

pub fn dblk_x(p: &ProgX, ctx: &Vec<Vec<i64>>, r: &mut Reader, fuel: u64, blk: usize,
              st: &mut DStX, tr: &mut Vec<(i64, u64)>) -> (ok: bool)
    requires old(r).wf(),
    ensures
        final(r).wf(), final(r).same(*old(r)),
        ok == (dblk(p@, cview(ctx@), old(r).win(), fuel as nat, blk as nat, 0, dview(*old(st), old(r).pos)) is Some),
        ok ==> dview(*final(st), final(r).pos) == dblk(p@, cview(ctx@), old(r).win(), fuel as nat, blk as nat, 0, dview(*old(st), old(r).pos)).unwrap().0,
        ok ==> tview(final(tr)@) =~= tview(old(tr)@) + dblk(p@, cview(ctx@), old(r).win(), fuel as nat, blk as nat, 0, dview(*old(st), old(r).pos)).unwrap().1,
    decreases fuel, 2nat,
{
    let ghost pp = p@;
    let ghost c = cview(ctx@);
    let ghost b = old(r).win();
    let ghost d0 = dview(*st, r.pos);
    let ghost t0 = tr@;
    if blk >= p.blocks.len() {
        assert(pp.blocks.len() == p.blocks@.len());
        assert(dblk(pp, c, b, fuel as nat, blk as nat, 0, d0) is None);
        assert(pp == p@);
        assert(d0 == dview(*old(st), old(r).pos));
        assert(t0 == old(tr)@);
        return false;
    }
    let stmts = &p.blocks[blk];
    proof { assert(pp.blocks[blk as int] == blk_view(stmts@)); }
    let mut i: usize = 0;
    proof { assert(tview(tr@) =~= tview(t0) + Seq::<(int, nat)>::empty()); }
    while i < stmts.len()
        invariant
            r.wf(), r.same(*old(r)),
            d0 == dview(*old(st), old(r).pos), t0 == old(tr)@,
            b == old(r).win(), pp == p@, c == cview(ctx@),
            stmts == &p.blocks@[blk as int],
            blk < p.blocks@.len(),
            i <= stmts@.len(),
            pp.blocks[blk as int] == blk_view(stmts@),
            tview(tr@).len() >= tview(t0).len(),
            tview(tr@).take(t0.len() as int) =~= tview(t0),
            dblk(pp, c, b, fuel as nat, blk as nat, 0, d0)
                == tcat(dblk(pp, c, b, fuel as nat, blk as nat, i as nat, dview(*st, r.pos)),
                        tview(tr@).skip(t0.len() as int)),
        decreases stmts@.len() - i,
    {
        let ghost di = dview(*st, r.pos);
        let ghost ti = tr@;
        proof { assert(pp.blocks[blk as int][i as int] == st_view(stmts@[i as int])); }
        if !dstmt_x(p, ctx, r, fuel, &stmts[i], st, tr) {
            return false;
        }
        proof {
            let (d1, t1) = dstmt(pp, c, b, fuel as nat, st_view(stmts@[i as int]), di).unwrap();
            assert(tview(tr@).skip(t0.len() as int) =~= tview(ti).skip(t0.len() as int) + t1);
            assert(tview(tr@).take(t0.len() as int) =~= tview(ti).take(t0.len() as int));
            match dblk(pp, c, b, fuel as nat, blk as nat, (i + 1) as nat, d1) {
                Some((d2, t2)) => {
                    assert(tview(ti).skip(t0.len() as int) + (t1 + t2)
                           =~= (tview(ti).skip(t0.len() as int) + t1) + t2);
                }
                None => {}
            }
        }
        i = i + 1;
    }
    proof {
        assert(tview(tr@) =~= tview(t0) + tview(tr@).skip(t0.len() as int));
        assert(tview(tr@).skip(t0.len() as int) + Seq::<(int, nat)>::empty() =~= tview(tr@).skip(t0.len() as int));
    }
    true
}

#[verifier::rlimit(60)]
pub fn dstmt_x(p: &ProgX, ctx: &Vec<Vec<i64>>, r: &mut Reader, fuel: u64, s: &StX,
               st: &mut DStX, tr: &mut Vec<(i64, u64)>) -> (ok: bool)
    requires old(r).wf(),
    ensures
        final(r).wf(), final(r).same(*old(r)),
        ok == (dstmt(p@, cview(ctx@), old(r).win(), fuel as nat, st_view(*s), dview(*old(st), old(r).pos)) is Some),
        ok ==> dview(*final(st), final(r).pos) == dstmt(p@, cview(ctx@), old(r).win(), fuel as nat, st_view(*s), dview(*old(st), old(r).pos)).unwrap().0,
        ok ==> tview(final(tr)@) =~= tview(old(tr)@) + dstmt(p@, cview(ctx@), old(r).win(), fuel as nat, st_view(*s), dview(*old(st), old(r).pos)).unwrap().1,
    decreases fuel, 1nat,
{
    let ghost pp = p@;
    let ghost c = cview(ctx@);
    let ghost b = old(r).win();
    let ghost d0 = dview(*st, r.pos);
    let ghost t0 = tr@;
    proof {
        assert(b.skip(r.pos as int) =~= r.rem());
        assert(tview(tr@) =~= tview(t0) + Seq::<(int, nat)>::empty());
    }
    match s {
        StX::Read(d, ds) => {
            if st.sealed {
                return false;
            }
            let (v, w) = match read_desc_x(p, ctx, r, &st.env, ds) {
                Some(vw) => vw,
                None => { return false; }
            };
            proof {
                let dv = desc_val(pp.xs, d0.env, c, desc_view(*ds)).unwrap();
                lemma_desc_val_ok(pp.xs, d0.env, c, desc_view(*ds));
                lemma_desc_inv(dv, b.skip(d0.pos as int));
            }
            if !store_x(&p.xs, &mut st.env, ctx, d, v) {
                return false;
            }
            tr.push((v, w));
            proof { lemma_tview_push(t0, v, w); }
            true
        }
        StX::Let(d, e) => {
            match eval_x(&p.xs, &st.env, ctx, *e) {
                Some(v) => store_x(&p.xs, &mut st.env, ctx, d, v),
                None => false,
            }
        }
        StX::Assert(e) => {
            match eval_x(&p.xs, &st.env, ctx, *e) {
                Some(v) => v != 0,
                None => false,
            }
        }
        StX::Conf(e) => {
            match eval_x(&p.xs, &st.env, ctx, *e) {
                Some(v) => {
                    st.conf = st.conf && v != 0;
                    true
                }
                None => false,
            }
        }
        StX::If(cc, t, f) => {
            if fuel == 0 {
                return false;
            }
            match eval_x(&p.xs, &st.env, ctx, *cc) {
                Some(v) => dblk_x(p, ctx, r, fuel - 1, if v != 0 { *t } else { *f }, st, tr),
                None => false,
            }
        }
        StX::While(cc, body) => {
            if fuel == 0 {
                return false;
            }
            dwhile_x(p, ctx, r, fuel, *cc, *body, st, tr)
        }
        StX::More(mn, mx, body) => {
            if fuel == 0 || *mn > *mx || *mx > 281474976710656u64 {
                return false;
            }
            let ok = dmore_x(p, ctx, r, fuel, *mn, *mx, *body, st, tr);
            if ok {
                st.sealed = true;
            }
            ok
        }
        StX::Call(blk) => {
            if fuel == 0 {
                return false;
            }
            dblk_x(p, ctx, r, fuel - 1, *blk, st, tr)
        }
        StX::Align => {
            if st.sealed {
                return false;
            }
            align_x(r)
        }
        StX::Pos(d) => {
            if (r.pos as u64) > 281474976710656u64 {
                return false;
            }
            store_x(&p.xs, &mut st.env, ctx, d, r.pos as i64)
        }
        StX::ZAlign => {
            if st.sealed {
                return false;
            }
            zalign_x(r)
        }
    }
}

/// One syntax element, as its descriptor reads it: its value and choice.
pub fn read_desc_x(p: &ProgX, ctx: &Vec<Vec<i64>>, r: &mut Reader, env: &Vec<i64>, ds: &DescX) -> (res: Option<(i64, u64)>)
    requires old(r).wf(),
    ensures
        final(r).wf(), final(r).same(*old(r)),
        match desc_val(p@.xs, iview(env@), cview(ctx@), desc_view(*ds)) {
            Some(dv) => match dparse(dv, old(r).rem()) {
                Some((v, w, k)) => res == Some((v as i64, w as u64)) && final(r).pos == old(r).pos + k,
                None => res is None,
            },
            None => res is None,
        },
{
    match ds {
        DescX::U(w) => {
            match eval_x(&p.xs, env, ctx, *w) {
                Some(n) => {
                    if n < 0 || n > 48 {
                        return None;
                    }
                    match r.read_nbit(n as usize) {
                        Some(x) => {
                            proof {
                                lemma_p2_48();
                                lemma_bits_val_bound(old(r).rem().take(n as int));
                                vbits::prim_read::lemma_p2_mono(n as nat, 48);
                            }
                            Some((x as i64, 0))
                        }
                        None => None,
                    }
                }
                None => None,
            }
        }
        DescX::UE => {
            match r.read_ue() {
                Some(x) => Some((x as i64, 0)),
                None => None,
            }
        }
        DescX::SE => {
            match r.read_se() {
                Some(x) => Some((x, 0)),
                None => None,
            }
        }
        DescX::FF => {
            match r.read_ff() {
                Some(x) => Some((x as i64, 0)),
                None => None,
            }
        }
        DescX::SU(w) => {
            match eval_x(&p.xs, env, ctx, *w) {
                Some(n) => if n < 1 || n > 48 { None } else { read_dv_su(r, n) },
                None => None,
            }
        }
        DescX::NS(w) => {
            match eval_x(&p.xs, env, ctx, *w) {
                Some(n) => if n < 1 || n > 1099511627776i64 { None } else { read_dv_ns(r, n) },
                None => None,
            }
        }
        DescX::LE(w) => {
            match eval_x(&p.xs, env, ctx, *w) {
                Some(n) => if n < 0 || n > 6 { None } else { read_dv_le(r, n) },
                None => None,
            }
        }
        DescX::UVLC => read_dv_uvlc(r),
        DescX::LEB128 => read_dv_leb128(r),
    }
}

pub open spec fn dres(d: DV, s: Seq<bool>, res: Option<(i64, u64)>, p0: usize, p1: usize) -> bool {
    match dparse(d, s) {
        Some((v, w, k)) => res == Some((v as i64, w as u64)) && p1 == p0 + k,
        None => res is None,
    }
}

fn read_dv_su(r: &mut Reader, n: i64) -> (res: Option<(i64, u64)>)
    requires old(r).wf(), 1 <= n <= 48,
    ensures final(r).wf(), final(r).same(*old(r)), dres(DV::SU(n as nat), old(r).rem(), res, old(r).pos, final(r).pos),
{
    match r.read_su(n as usize) {
        Some(x) => Some((x, 0)),
        None => None,
    }
}

fn read_dv_ns(r: &mut Reader, n: i64) -> (res: Option<(i64, u64)>)
    requires old(r).wf(), 1 <= n <= 1099511627776i64,
    ensures final(r).wf(), final(r).same(*old(r)), dres(DV::NS(n as nat), old(r).rem(), res, old(r).pos, final(r).pos),
{
    proof { lemma_ilog2_40(n as nat); }
    match r.read_ns(n as u64) {
        Some(x) => {
            proof { lemma_ns_inv(old(r).rem(), n as nat); }
            Some((x as i64, 0))
        }
        None => None,
    }
}

fn read_dv_le(r: &mut Reader, n: i64) -> (res: Option<(i64, u64)>)
    requires old(r).wf(), 0 <= n <= 6,
    ensures final(r).wf(), final(r).same(*old(r)), dres(DV::LE(n as nat), old(r).rem(), res, old(r).pos, final(r).pos),
{
    match r.read_le(n as usize) {
        Some(x) => {
            proof {
                crate::xir::lemma_p2_48();
                lemma_le_inv(old(r).rem(), n as nat);
                vbits::prim_read::lemma_p2_mono(8 * n as nat, 48);
            }
            Some((x as i64, 0))
        }
        None => None,
    }
}

fn read_dv_uvlc(r: &mut Reader) -> (res: Option<(i64, u64)>)
    requires old(r).wf(),
    ensures final(r).wf(), final(r).same(*old(r)), dres(DV::UVLC, old(r).rem(), res, old(r).pos, final(r).pos),
{
    match r.read_uvlc() {
        Some((x, c)) => {
            proof { lemma_uvlc_inv(old(r).rem()); }
            Some((x as i64, c))
        }
        None => None,
    }
}

fn read_dv_leb128(r: &mut Reader) -> (res: Option<(i64, u64)>)
    requires old(r).wf(),
    ensures final(r).wf(), final(r).same(*old(r)), dres(DV::LEB128, old(r).rem(), res, old(r).pos, final(r).pos),
{
    proof {
        if leb_parse(old(r).rem(), 0) is Some {
            lemma_leb_inv(old(r).rem(), 0);
            let (v, k) = leb_parse(old(r).rem(), 0).unwrap();
            lemma_leb_min(v, k);
        }
    }
    match r.read_leb128() {
        Some((x, c)) => Some((x as i64, c)),
        None => None,
    }
}

/// `byte_alignment( )`: the window holds its code at the position.
pub fn align_x(r: &mut Reader) -> (ok: bool)
    requires old(r).wf(),
    ensures
        final(r).wf(), final(r).same(*old(r)),
        ({
            let c = align_code(old(r).pos as nat);
            let b = old(r).win();
            &&& ok == (old(r).pos + c.len() <= b.len() && b.subrange(old(r).pos as int, (old(r).pos + c.len()) as int) == c)
            &&& ok ==> final(r).pos == old(r).pos + c.len()
        }),
{
    let ghost b = old(r).win();
    let ghost p0 = r.pos;
    let z: usize = (8 - (r.pos + 1) % 8) % 8;
    let ghost code = align_code(r.pos as nat);
    proof { assert(code.len() == 1 + z); }
    if 1 + z > r.end - r.pos {
        return false;
    }
    let ghost rem0 = r.rem();
    proof { assert(b.subrange(p0 as int, (p0 + code.len()) as int) =~= rem0.take(1 + z as int)); }
    let one = match r.read_nbit(1) {
        Some(x) => x,
        None => { return false; }
    };
    proof {
        assert(rem0.take(1) =~= seq![rem0[0]]);
        lemma_bits_val_one(rem0[0]);
        assert(code[0] == true);
    }
    if one != 1 {
        proof { assert(rem0.take(1 + z as int)[0] != code[0]); }
        return false;
    }
    let ghost rem1 = r.rem();
    let zz = match r.read_nbit(z) {
        Some(x) => x,
        None => { return false; }
    };
    proof {
        lemma_zero_val(rem1.take(z as int));
        assert(rem1.take(z as int) =~= rem0.subrange(1, 1 + z as int));
        if zz == 0 {
            assert(rem0.take(1 + z as int) =~= seq![true] + zeros(z as nat));
        } else {
            assert(!(rem1.take(z as int) =~= zeros(z as nat)));
            let j = choose|j: int| 0 <= j < z && rem1.take(z as int)[j] != zeros(z as nat)[j];
            assert(rem0.take(1 + z as int)[1 + j] != code[1 + j]);
        }
    }
    zz == 0
}

/// AV1's `byte_alignment( )`: the window holds its code at the position.
pub fn zalign_x(r: &mut Reader) -> (ok: bool)
    requires old(r).wf(),
    ensures
        final(r).wf(), final(r).same(*old(r)),
        ({
            let c = zalign_code(old(r).pos as nat);
            let b = old(r).win();
            &&& ok == (old(r).pos + c.len() <= b.len() && b.subrange(old(r).pos as int, (old(r).pos + c.len()) as int) == c)
            &&& ok ==> final(r).pos == old(r).pos + c.len()
        }),
{
    let ghost b = old(r).win();
    let ghost p0 = r.pos;
    let z: usize = (8 - r.pos % 8) % 8;
    let ghost code = zalign_code(r.pos as nat);
    proof { assert(code.len() == z); }
    if z > r.end - r.pos {
        return false;
    }
    let ghost rem0 = r.rem();
    proof { assert(b.subrange(p0 as int, (p0 + code.len()) as int) =~= rem0.take(z as int)); }
    let zz = match r.read_nbit(z) {
        Some(x) => x,
        None => { return false; }
    };
    proof {
        lemma_zero_val(rem0.take(z as int));
    }
    zz == 0
}

pub fn dwhile_x(p: &ProgX, ctx: &Vec<Vec<i64>>, r: &mut Reader, fuel: u64, c: usize, body: usize,
                st: &mut DStX, tr: &mut Vec<(i64, u64)>) -> (ok: bool)
    requires old(r).wf(), fuel >= 1,
    ensures
        final(r).wf(), final(r).same(*old(r)),
        ok == (dwhile(p@, cview(ctx@), old(r).win(), fuel as nat, c as nat, body as nat, maxloop(), dview(*old(st), old(r).pos)) is Some),
        ok ==> dview(*final(st), final(r).pos) == dwhile(p@, cview(ctx@), old(r).win(), fuel as nat, c as nat, body as nat, maxloop(), dview(*old(st), old(r).pos)).unwrap().0,
        ok ==> tview(final(tr)@) =~= tview(old(tr)@) + dwhile(p@, cview(ctx@), old(r).win(), fuel as nat, c as nat, body as nat, maxloop(), dview(*old(st), old(r).pos)).unwrap().1,
    decreases fuel, 0nat,
{
    let ghost pp = p@;
    let ghost cc = cview(ctx@);
    let ghost b = old(r).win();
    let ghost d0 = dview(*st, r.pos);
    let ghost t0 = tr@;
    let mut n: u64 = 16777216;
    proof { assert(tview(tr@).skip(t0.len() as int) =~= Seq::<(int, nat)>::empty()); }
    loop
        invariant
            r.wf(), r.same(*old(r)),
            d0 == dview(*old(st), old(r).pos), t0 == old(tr)@,
            b == old(r).win(), pp == p@, cc == cview(ctx@), fuel >= 1,
            tview(tr@).len() >= tview(t0).len(),
            tview(tr@).take(t0.len() as int) =~= tview(t0),
            dwhile(pp, cc, b, fuel as nat, c as nat, body as nat, maxloop(), d0)
                == tcat(dwhile(pp, cc, b, fuel as nat, c as nat, body as nat, n as nat, dview(*st, r.pos)),
                        tview(tr@).skip(t0.len() as int)),
        decreases n,
    {
        let ghost di = dview(*st, r.pos);
        let ghost ti = tr@;
        match eval_x(&p.xs, &st.env, ctx, c) {
            None => {
                assert(eval(pp.xs, di.env, cc, c as nat) is None);
                assert(dwhile(pp, cc, b, fuel as nat, c as nat, body as nat, n as nat, di) is None);
                assert(dwhile(pp, cc, b, fuel as nat, c as nat, body as nat, maxloop(), d0) is None);
                assert(d0 == dview(*old(st), old(r).pos));
                return false;
            }
            Some(v) => {
                if v == 0 {
                    proof {
                        assert(tview(tr@) =~= tview(t0) + tview(tr@).skip(t0.len() as int));
                        assert(tview(tr@).skip(t0.len() as int) + Seq::<(int, nat)>::empty() =~= tview(tr@).skip(t0.len() as int));
                    }
                    return true;
                }
                if n == 0 {
                    return false;
                }
                if !dblk_x(p, ctx, r, fuel - 1, body, st, tr) {
                    return false;
                }
                proof {
                    let (d1, t1) = dblk(pp, cc, b, (fuel - 1) as nat, body as nat, 0, di).unwrap();
                    assert(tview(tr@).skip(t0.len() as int) =~= tview(ti).skip(t0.len() as int) + t1);
                    assert(tview(tr@).take(t0.len() as int) =~= tview(ti).take(t0.len() as int));
                    match dwhile(pp, cc, b, fuel as nat, c as nat, body as nat, (n - 1) as nat, d1) {
                        Some((d2, t2)) => {
                            assert(tview(ti).skip(t0.len() as int) + (t1 + t2)
                                   =~= (tview(ti).skip(t0.len() as int) + t1) + t2);
                        }
                        None => {}
                    }
                }
                n = n - 1;
            }
        }
    }
}

pub fn dmore_x(p: &ProgX, ctx: &Vec<Vec<i64>>, r: &mut Reader, fuel: u64, mn: u64, mx: u64, body: usize,
               st: &mut DStX, tr: &mut Vec<(i64, u64)>) -> (ok: bool)
    requires old(r).wf(), fuel >= 1, mn <= mx, mx <= vb(),
    ensures
        final(r).wf(), final(r).same(*old(r)),
        ok == dmore(p@, cview(ctx@), old(r).win(), fuel as nat, mn as nat, mx as nat, body as nat, 0, dview(*old(st), old(r).pos)) is Some,
        ok ==> ({
            let (d1, n, t) = dmore(p@, cview(ctx@), old(r).win(), fuel as nat, mn as nat, mx as nat, body as nat, 0, dview(*old(st), old(r).pos)).unwrap();
            dview(*final(st), final(r).pos) == d1 && tview(final(tr)@) =~= tview(old(tr)@) + (seq![(n as int, 0nat)] + t)
        }),
    decreases fuel, 0nat,
{
    let ghost pp = p@;
    let ghost cc = cview(ctx@);
    let ghost b = old(r).win();
    let ghost d0 = dview(*st, r.pos);
    let ghost t0 = tr@;
    let idx = tr.len();
    tr.push((0, 0));
    let mut cnt: u64 = 0;
    proof { assert(tview(tr@).skip(idx + 1) =~= Seq::<(int, nat)>::empty()); }
    loop
        invariant
            r.wf(), r.same(*old(r)),
            d0 == dview(*old(st), old(r).pos), t0 == old(tr)@,
            b == old(r).win(), pp == p@, cc == cview(ctx@), fuel >= 1,
            mn <= mx, mx <= vb(), cnt <= mx,
            idx == t0.len(), tr@.len() > idx,
            tview(tr@).take(idx as int) =~= tview(t0),
            dmore(pp, cc, b, fuel as nat, mn as nat, mx as nat, body as nat, 0, d0)
                == tcat3(dmore(pp, cc, b, fuel as nat, mn as nat, mx as nat, body as nat, cnt as nat, dview(*st, r.pos)),
                         tview(tr@).skip(idx + 1)),
        decreases r.end - r.pos,
    {
        let ghost di = dview(*st, r.pos);
        let ghost ti = tr@;
        if cnt >= mn && (cnt >= mx || r.pos == r.end) {
            proof {
                assert(tview(tr@).skip(idx + 1) + Seq::<(int, nat)>::empty() =~= tview(tr@).skip(idx + 1));
            }
            tr.set(idx, (cnt as i64, 0));
            proof {
                assert(tview(tr@) =~= tview(t0) + (seq![(cnt as int, 0nat)] + tview(ti).skip(idx + 1)));
            }
            return true;
        }
        let p0 = r.pos;
        if !dblk_x(p, ctx, r, fuel - 1, body, st, tr) {
            return false;
        }
        if r.pos <= p0 {
            return false;
        }
        proof {
            let (d1, t1) = dblk(pp, cc, b, (fuel - 1) as nat, body as nat, 0, di).unwrap();
            assert(tview(tr@).skip(idx + 1) =~= tview(ti).skip(idx + 1) + t1);
            assert(tview(tr@).take(idx as int) =~= tview(ti).take(idx as int));
            match dmore(pp, cc, b, fuel as nat, mn as nat, mx as nat, body as nat, (cnt + 1) as nat, d1) {
                Some((d2, n2, t2)) => {
                    assert(tview(ti).skip(idx + 1) + (t1 + t2)
                           =~= (tview(ti).skip(idx + 1) + t1) + t2);
                }
                None => {}
            }
        }
        cnt = cnt + 1;
    }
}

// --------------------------------------------------------------- top level

pub fn env0_x(n: usize) -> (env: Vec<i64>)
    ensures iview(env@) =~= Seq::new(n as nat, |i: int| 0int),
{
    let mut env: Vec<i64> = Vec::new();
    while env.len() < n
        invariant env@.len() <= n, forall|i: int| 0 <= i < env@.len() ==> env@[i] == 0,
        decreases n - env@.len(),
    {
        env.push(0);
    }
    env
}

/// What decoding gives: the trace, the choices, the environment, and the
/// conformance flag.
pub struct ParsedX {
    pub trace: Vec<i64>,
    pub ch: Vec<u64>,
    pub env: Vec<i64>,
    pub conf: bool,
}

pub open spec fn pview(x: ParsedX) -> Parsed {
    Parsed { trace: iview(x.trace@), ch: nview(x.ch@), env: iview(x.env@), conf: x.conf }
}

/// A trace's values and choices, apart.
pub fn split_x(t: &Vec<(i64, u64)>) -> (res: (Vec<i64>, Vec<u64>))
    ensures iview(res.0@) =~= vals(tview(t@)), nview(res.1@) =~= chs(tview(t@)),
{
    let mut a: Vec<i64> = Vec::new();
    let mut c: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < t.len()
        invariant
            i <= t@.len(), a@.len() == i, c@.len() == i,
            forall|j: int| 0 <= j < i ==> a@[j] == t@[j].0 && c@[j] == t@[j].1,
        decreases t@.len() - i,
    {
        a.push(t[i].0);
        c.push(t[i].1);
        i = i + 1;
    }
    (a, c)
}

/// Decode the syntax structure that is the first `end` bits of `buf`.
pub fn decode_all(p: &ProgX, ctx: &Vec<Vec<i64>>, buf: &[u8], end: usize) -> (res: Option<ParsedX>)
    requires end <= 8 * buf@.len(), 8 * buf@.len() <= usize::MAX,
    ensures
        match dec_all(p@, cview(ctx@), bits_of(buf@).take(end as int)) {
            Some(pr) => res is Some && pview(res.unwrap()) == pr,
            None => res is None,
        },
{
    let mut r = Reader::new(buf, end);
    let mut st = DStX { env: env0_x(p.nslots), sealed: false, conf: true };
    let mut tr: Vec<(i64, u64)> = Vec::new();
    proof { assert(dview(st, 0) == dst0(p@)); }
    if !dblk_x(p, ctx, &mut r, 64, p.main, &mut st, &mut tr) {
        return None;
    }
    proof { assert(tview(tr@) =~= Seq::<(int, nat)>::empty() + tview(tr@)); }
    if r.pos != end {
        return None;
    }
    let (trace, ch) = split_x(&tr);
    Some(ParsedX { trace, ch, env: st.env, conf: st.conf })
}

/// Decode the syntax structure at the front of the first `end` bits of
/// `buf`, its variables starting as `env`, and say where it ends.
pub fn decode_pre_at(p: &ProgX, ctx: &Vec<Vec<i64>>, env: Vec<i64>, buf: &[u8], end: usize) -> (res: Option<(ParsedX, usize)>)
    requires end <= 8 * buf@.len(), 8 * buf@.len() <= usize::MAX,
    ensures
        match dec_pre_at(p@, cview(ctx@), iview(env@), bits_of(buf@).take(end as int)) {
            Some((pr, k)) => res is Some && pview(res.unwrap().0) == pr && res.unwrap().1 == k,
            None => res is None,
        },
{
    let mut r = Reader::new(buf, end);
    let ghost e0 = iview(env@);
    let mut st = DStX { env, sealed: false, conf: true };
    let mut tr: Vec<(i64, u64)> = Vec::new();
    proof { assert(dview(st, 0) == dst_at(e0)); }
    if !dblk_x(p, ctx, &mut r, 64, p.main, &mut st, &mut tr) {
        return None;
    }
    proof { assert(tview(tr@) =~= Seq::<(int, nat)>::empty() + tview(tr@)); }
    if st.sealed {
        return None;
    }
    let (trace, ch) = split_x(&tr);
    Some((ParsedX { trace, ch, env: st.env, conf: st.conf }, r.pos))
}

/// Decode the syntax structure at the front of the first `end` bits of
/// `buf`, and say where it ends.
pub fn decode_pre(p: &ProgX, ctx: &Vec<Vec<i64>>, buf: &[u8], end: usize) -> (res: Option<(ParsedX, usize)>)
    requires end <= 8 * buf@.len(), 8 * buf@.len() <= usize::MAX,
    ensures
        match dec_pre(p@, cview(ctx@), bits_of(buf@).take(end as int)) {
            Some((pr, k)) => res is Some && pview(res.unwrap().0) == pr && res.unwrap().1 == k,
            None => res is None,
        },
{
    let env = env0_x(p.nslots);
    proof { assert(iview(env@) =~= env0(p@)); }
    decode_pre_at(p, ctx, env, buf, end)
}

} // verus!
