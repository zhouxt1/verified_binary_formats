//! The executable encoder: when it returns `true`, the spec encoder
//! succeeds and the bits written are exactly the spec's. (It returns
//! `false` when the spec fails, or if the output would outgrow memory.)
use vstd::prelude::*;
use vbits::bitspec::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::prim_write::bits_seq;
use crate::eg::*;
use crate::avd::*;
use crate::avx::*;
use crate::ir::*;
use crate::sem::*;
use crate::bits::*;
use crate::xir::*;
use crate::xdec::{env0_x, ParsedX};
#[cfg(verus_keep_ghost)]
use crate::xdec::pview;

verus! {

pub struct EStX {
    pub env: Vec<i64>,
    pub sealed: bool,
    pub conf: bool,
    pub ti: usize,
}

pub open spec fn eview(st: EStX, pos: usize) -> ESt {
    ESt { env: iview(st.env@), pos: pos as nat, sealed: st.sealed, conf: st.conf, ti: st.ti as nat }
}

pub open spec fn ecat(r: Option<(ESt, Seq<bool>)>, acc: Seq<bool>) -> Option<(ESt, Seq<bool>)> {
    match r {
        Some((s, c)) => Some((s, acc + c)),
        None => None,
    }
}

/// One syntax element's code, with the given choice.
pub fn write_desc_x(p: &ProgX, ctx: &Vec<Vec<i64>>, w: &mut Writer, env: &Vec<i64>, ds: &DescX, v: i64, ch: u64) -> (ok: bool)
    requires old(w).wf(),
    ensures
        ok ==> final(w).wf(),
        ok ==> ({
            let dv = desc_val(p@.xs, iview(env@), cview(ctx@), desc_view(*ds));
            &&& dv is Some
            &&& dcode(dv.unwrap(), v as int, ch as nat) is Some
            &&& final(w).written() =~= old(w).written() + dcode(dv.unwrap(), v as int, ch as nat).unwrap()
            &&& final(w).pos == old(w).pos + dcode(dv.unwrap(), v as int, ch as nat).unwrap().len()
        }),
{
    match ds {
        DescX::UVLC => {
            if v < 0 || !((v <= 4294967294 && ch == 0) || v == 4294967295) {
                return false;
            }
            return w.write_uvlc(v as u64, ch);
        }
        DescX::LEB128 => {
            if v < 0 || v > 4294967295 || ch > 8 {
                return false;
            }
            let lm = leb_min_x(v as u64);
            if lm as u64 + ch > 8 {
                return false;
            }
            return w.write_leb128(v as u64, ch);
        }
        _ => {}
    }
    if ch != 0 {
        return false;
    }
    match ds {
        DescX::UVLC | DescX::LEB128 => false,
        DescX::SU(wd) => {
            match eval_x(&p.xs, env, ctx, *wd) {
                Some(n) => {
                    if n < 1 || n > 48 {
                        return false;
                    }
                    let half = pow2_u64((n - 1) as usize);
                    proof {
                        vbits::prim_read::lemma_p2_mono((n - 1) as nat, 48);
                        lemma_p2_48();
                    }
                    if v < -(half as i64) || v >= half as i64 {
                        return false;
                    }
                    w.write_su(n as usize, v)
                }
                None => false,
            }
        }
        DescX::NS(wd) => {
            match eval_x(&p.xs, env, ctx, *wd) {
                Some(n) => {
                    if n < 1 || n > 1099511627776i64 || v < 0 || v >= n {
                        return false;
                    }
                    w.write_ns(n as u64, v as u64)
                }
                None => false,
            }
        }
        DescX::LE(wd) => {
            match eval_x(&p.xs, env, ctx, *wd) {
                Some(n) => {
                    if n < 0 || n > 6 || v < 0 {
                        return false;
                    }
                    let lim = pow2_u64(8 * n as usize);
                    if v as u64 >= lim {
                        return false;
                    }
                    w.write_le(n as usize, v as u64)
                }
                None => false,
            }
        }
        DescX::U(wd) => {
            match eval_x(&p.xs, env, ctx, *wd) {
                Some(n) => {
                    if n < 0 || n > 48 || v < 0 {
                        return false;
                    }
                    let pw: u64 = 1u64 << (n as u64);
                    proof {
                        vbits::prim_read::lemma_p2_eq_pow2(n as nat);
                        vstd::bits::lemma_u64_pow2_no_overflow(n as nat);
                        vstd::bits::lemma_u64_shl_is_mul(1u64, n as u64);
                    }
                    if (v as u64) >= pw {
                        return false;
                    }
                    proof { assert(((v as int) as nat) as u64 == v as u64); }
                    w.write_nbit(n as usize, v as u64)
                }
                None => false,
            }
        }
        DescX::UE => {
            if v < 0 || v > 4294967294 {
                return false;
            }
            w.write_ue(v as u64)
        }
        DescX::SE => {
            if v < -2147483647 || v > 2147483647 {
                return false;
            }
            w.write_se(v)
        }
        DescX::FF => {
            if v < 0 || v > 281474976710656 {
                return false;
            }
            w.write_ff(v as u64)
        }
    }
}

pub fn eblk_x(p: &ProgX, ctx: &Vec<Vec<i64>>, tr: &Vec<(i64, u64)>, w: &mut Writer, fuel: u64, blk: usize,
              st: &mut EStX) -> (ok: bool)
    requires old(w).wf(),
    ensures
        ok ==> final(w).wf(),
        ok ==> eblk(p@, cview(ctx@), tview(tr@), fuel as nat, blk as nat, 0, eview(*old(st), old(w).pos)) is Some,
        ok ==> eview(*final(st), final(w).pos) == eblk(p@, cview(ctx@), tview(tr@), fuel as nat, blk as nat, 0, eview(*old(st), old(w).pos)).unwrap().0,
        ok ==> final(w).written() =~= old(w).written() + eblk(p@, cview(ctx@), tview(tr@), fuel as nat, blk as nat, 0, eview(*old(st), old(w).pos)).unwrap().1,
    decreases fuel, 2nat,
{
    let ghost pp = p@;
    let ghost c = cview(ctx@);
    let ghost t = tview(tr@);
    let ghost e0 = eview(*st, w.pos);
    let ghost w0 = w.written();
    if blk >= p.blocks.len() {
        return false;
    }
    let stmts = &p.blocks[blk];
    proof { assert(pp.blocks[blk as int] == blk_view(stmts@)); }
    let mut i: usize = 0;
    proof { assert(w.written() =~= w0 + Seq::<bool>::empty()); }
    while i < stmts.len()
        invariant
            w.wf(),
            e0 == eview(*old(st), old(w).pos), w0 == old(w).written(),
            pp == p@, c == cview(ctx@), t == tview(tr@),
            stmts == &p.blocks@[blk as int],
            blk < p.blocks@.len(),
            i <= stmts@.len(),
            pp.blocks[blk as int] == blk_view(stmts@),
            w.written().len() >= w0.len(),
            w.written().take(w0.len() as int) =~= w0,
            eblk(pp, c, t, fuel as nat, blk as nat, 0, e0)
                == ecat(eblk(pp, c, t, fuel as nat, blk as nat, i as nat, eview(*st, w.pos)),
                        w.written().skip(w0.len() as int)),
        decreases stmts@.len() - i,
    {
        let ghost ei = eview(*st, w.pos);
        let ghost wi = w.written();
        proof { assert(pp.blocks[blk as int][i as int] == st_view(stmts@[i as int])); }
        if !estmt_x(p, ctx, tr, w, fuel, &stmts[i], st) {
            return false;
        }
        proof {
            let (e1, c1) = estmt(pp, c, t, fuel as nat, st_view(stmts@[i as int]), ei).unwrap();
            assert(w.written().skip(w0.len() as int) =~= wi.skip(w0.len() as int) + c1);
            assert(w.written().take(w0.len() as int) =~= wi.take(w0.len() as int));
            match eblk(pp, c, t, fuel as nat, blk as nat, (i + 1) as nat, e1) {
                Some((e2, c2)) => {
                    assert(wi.skip(w0.len() as int) + (c1 + c2) =~= (wi.skip(w0.len() as int) + c1) + c2);
                }
                None => {}
            }
        }
        i = i + 1;
    }
    proof {
        assert(w.written() =~= w0 + w.written().skip(w0.len() as int));
        assert(w.written().skip(w0.len() as int) + Seq::<bool>::empty() =~= w.written().skip(w0.len() as int));
    }
    true
}

#[verifier::rlimit(60)]
pub fn estmt_x(p: &ProgX, ctx: &Vec<Vec<i64>>, tr: &Vec<(i64, u64)>, w: &mut Writer, fuel: u64, s: &StX,
               st: &mut EStX) -> (ok: bool)
    requires old(w).wf(),
    ensures
        ok ==> final(w).wf(),
        ok ==> estmt(p@, cview(ctx@), tview(tr@), fuel as nat, st_view(*s), eview(*old(st), old(w).pos)) is Some,
        ok ==> eview(*final(st), final(w).pos) == estmt(p@, cview(ctx@), tview(tr@), fuel as nat, st_view(*s), eview(*old(st), old(w).pos)).unwrap().0,
        ok ==> final(w).written() =~= old(w).written() + estmt(p@, cview(ctx@), tview(tr@), fuel as nat, st_view(*s), eview(*old(st), old(w).pos)).unwrap().1,
    decreases fuel, 1nat,
{
    let ghost pp = p@;
    let ghost c = cview(ctx@);
    let ghost t = tview(tr@);
    let ghost e0 = eview(*st, w.pos);
    let ghost w0 = w.written();
    proof { assert(w.written() =~= w0 + Seq::<bool>::empty()); }
    match s {
        StX::Read(d, ds) => {
            if st.sealed || st.ti >= tr.len() {
                return false;
            }
            let (v, ch) = tr[st.ti];
            if !write_desc_x(p, ctx, w, &st.env, ds, v, ch) {
                return false;
            }
            if !store_x(&p.xs, &mut st.env, ctx, d, v) {
                return false;
            }
            st.ti = st.ti + 1;
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
        StX::If(cc, tb, fb) => {
            if fuel == 0 {
                return false;
            }
            match eval_x(&p.xs, &st.env, ctx, *cc) {
                Some(v) => eblk_x(p, ctx, tr, w, fuel - 1, if v != 0 { *tb } else { *fb }, st),
                None => false,
            }
        }
        StX::While(cc, body) => {
            if fuel == 0 {
                return false;
            }
            ewhile_x(p, ctx, tr, w, fuel, *cc, *body, st)
        }
        StX::More(mn, mx, body) => {
            if fuel == 0 || *mn > *mx || *mx > 281474976710656u64 || st.ti >= tr.len() {
                return false;
            }
            let (n, ch) = tr[st.ti];
            if ch != 0 || n < (*mn as i64) || n > (*mx as i64) {
                return false;
            }
            st.ti = st.ti + 1;
            let ok = emore_x(p, ctx, tr, w, fuel, *body, n as u64, st);
            if ok {
                st.sealed = true;
            }
            ok
        }
        StX::Call(blk) => {
            if fuel == 0 {
                return false;
            }
            eblk_x(p, ctx, tr, w, fuel - 1, *blk, st)
        }
        StX::Align => {
            if st.sealed {
                return false;
            }
            w.write_align()
        }
        StX::Pos(d) => {
            if (w.pos as u64) > 281474976710656u64 {
                return false;
            }
            store_x(&p.xs, &mut st.env, ctx, d, w.pos as i64)
        }
        StX::ZAlign => {
            if st.sealed {
                return false;
            }
            w.write_zalign()
        }
    }
}

pub fn ewhile_x(p: &ProgX, ctx: &Vec<Vec<i64>>, tr: &Vec<(i64, u64)>, w: &mut Writer, fuel: u64, c: usize, body: usize,
                st: &mut EStX) -> (ok: bool)
    requires old(w).wf(), fuel >= 1,
    ensures
        ok ==> final(w).wf(),
        ok ==> ewhile(p@, cview(ctx@), tview(tr@), fuel as nat, c as nat, body as nat, maxloop(), eview(*old(st), old(w).pos)) is Some,
        ok ==> eview(*final(st), final(w).pos) == ewhile(p@, cview(ctx@), tview(tr@), fuel as nat, c as nat, body as nat, maxloop(), eview(*old(st), old(w).pos)).unwrap().0,
        ok ==> final(w).written() =~= old(w).written() + ewhile(p@, cview(ctx@), tview(tr@), fuel as nat, c as nat, body as nat, maxloop(), eview(*old(st), old(w).pos)).unwrap().1,
    decreases fuel, 0nat,
{
    let ghost pp = p@;
    let ghost cc = cview(ctx@);
    let ghost t = tview(tr@);
    let ghost e0 = eview(*st, w.pos);
    let ghost w0 = w.written();
    let mut n: u64 = 16777216;
    proof { assert(w.written().skip(w0.len() as int) =~= Seq::<bool>::empty()); }
    loop
        invariant
            w.wf(),
            e0 == eview(*old(st), old(w).pos), w0 == old(w).written(),
            pp == p@, cc == cview(ctx@), t == tview(tr@), fuel >= 1,
            w.written().len() >= w0.len(),
            w.written().take(w0.len() as int) =~= w0,
            ewhile(pp, cc, t, fuel as nat, c as nat, body as nat, maxloop(), e0)
                == ecat(ewhile(pp, cc, t, fuel as nat, c as nat, body as nat, n as nat, eview(*st, w.pos)),
                        w.written().skip(w0.len() as int)),
        decreases n,
    {
        let ghost ei = eview(*st, w.pos);
        let ghost wi = w.written();
        match eval_x(&p.xs, &st.env, ctx, c) {
            None => { return false; }
            Some(v) => {
                if v == 0 {
                    proof {
                        assert(w.written() =~= w0 + w.written().skip(w0.len() as int));
                        assert(w.written().skip(w0.len() as int) + Seq::<bool>::empty() =~= w.written().skip(w0.len() as int));
                    }
                    return true;
                }
                if n == 0 {
                    return false;
                }
                if !eblk_x(p, ctx, tr, w, fuel - 1, body, st) {
                    return false;
                }
                proof {
                    let (e1, c1) = eblk(pp, cc, t, (fuel - 1) as nat, body as nat, 0, ei).unwrap();
                    assert(w.written().skip(w0.len() as int) =~= wi.skip(w0.len() as int) + c1);
                    assert(w.written().take(w0.len() as int) =~= wi.take(w0.len() as int));
                    match ewhile(pp, cc, t, fuel as nat, c as nat, body as nat, (n - 1) as nat, e1) {
                        Some((e2, c2)) => {
                            assert(wi.skip(w0.len() as int) + (c1 + c2) =~= (wi.skip(w0.len() as int) + c1) + c2);
                        }
                        None => {}
                    }
                }
                n = n - 1;
            }
        }
    }
}

pub fn emore_x(p: &ProgX, ctx: &Vec<Vec<i64>>, tr: &Vec<(i64, u64)>, w: &mut Writer, fuel: u64, body: usize, left: u64,
               st: &mut EStX) -> (ok: bool)
    requires old(w).wf(), fuel >= 1,
    ensures
        ok ==> final(w).wf(),
        ok ==> emore(p@, cview(ctx@), tview(tr@), fuel as nat, body as nat, left as nat, eview(*old(st), old(w).pos)) is Some,
        ok ==> eview(*final(st), final(w).pos) == emore(p@, cview(ctx@), tview(tr@), fuel as nat, body as nat, left as nat, eview(*old(st), old(w).pos)).unwrap().0,
        ok ==> final(w).written() =~= old(w).written() + emore(p@, cview(ctx@), tview(tr@), fuel as nat, body as nat, left as nat, eview(*old(st), old(w).pos)).unwrap().1,
    decreases fuel, 0nat,
{
    let ghost pp = p@;
    let ghost cc = cview(ctx@);
    let ghost t = tview(tr@);
    let ghost e0 = eview(*st, w.pos);
    let ghost w0 = w.written();
    let mut n: u64 = left;
    proof { assert(w.written().skip(w0.len() as int) =~= Seq::<bool>::empty()); }
    loop
        invariant
            w.wf(),
            e0 == eview(*old(st), old(w).pos), w0 == old(w).written(),
            pp == p@, cc == cview(ctx@), t == tview(tr@), fuel >= 1,
            w.written().len() >= w0.len(),
            w.written().take(w0.len() as int) =~= w0,
            emore(pp, cc, t, fuel as nat, body as nat, left as nat, e0)
                == ecat(emore(pp, cc, t, fuel as nat, body as nat, n as nat, eview(*st, w.pos)),
                        w.written().skip(w0.len() as int)),
        decreases n,
    {
        let ghost ei = eview(*st, w.pos);
        let ghost wi = w.written();
        if n == 0 {
            proof {
                assert(w.written() =~= w0 + w.written().skip(w0.len() as int));
                assert(w.written().skip(w0.len() as int) + Seq::<bool>::empty() =~= w.written().skip(w0.len() as int));
            }
            return true;
        }
        let p0 = w.pos;
        if !eblk_x(p, ctx, tr, w, fuel - 1, body, st) {
            return false;
        }
        if w.pos <= p0 {
            return false;
        }
        proof {
            let (e1, c1) = eblk(pp, cc, t, (fuel - 1) as nat, body as nat, 0, ei).unwrap();
            assert(w.written().len() == w.pos);
            assert(wi.len() == p0);
            assert(c1.len() > 0);
            assert(w.written().skip(w0.len() as int) =~= wi.skip(w0.len() as int) + c1);
            assert(w.written().take(w0.len() as int) =~= wi.take(w0.len() as int));
            match emore(pp, cc, t, fuel as nat, body as nat, (n - 1) as nat, e1) {
                Some((e2, c2)) => {
                    assert(wi.skip(w0.len() as int) + (c1 + c2) =~= (wi.skip(w0.len() as int) + c1) + c2);
                }
                None => {}
            }
        }
        n = n - 1;
    }
}

// --------------------------------------------------------------- top level

/// A trace's values with its choices.
pub fn zip_x(tr: &Vec<i64>, ch: &Vec<u64>) -> (res: Vec<(i64, u64)>)
    requires tr@.len() == ch@.len(),
    ensures tview(res@) =~= zip(iview(tr@), nview(ch@)),
{
    let mut z: Vec<(i64, u64)> = Vec::new();
    let mut i: usize = 0;
    while i < tr.len()
        invariant
            i <= tr@.len(), tr@.len() == ch@.len(), z@.len() == i,
            forall|j: int| 0 <= j < i ==> z@[j] == (tr@[j], ch@[j]),
        decreases tr@.len() - i,
    {
        z.push((tr[i], ch[i]));
        i = i + 1;
    }
    z
}

pub fn zeros_x(n: usize) -> (res: Vec<u64>)
    ensures nview(res@) =~= canon_ch(n as nat),
{
    let mut z: Vec<u64> = Vec::new();
    while z.len() < n
        invariant z@.len() <= n, forall|j: int| 0 <= j < z@.len() ==> z@[j] == 0,
        decreases n - z@.len(),
    {
        z.push(0);
    }
    z
}

/// Encode a trace, with the given choices, as a syntax structure that is
/// all of its data: the bytes, how many bits of them are the encoding (the
/// rest are zero), and the environment.
pub fn encode_ch(p: &ProgX, ctx: &Vec<Vec<i64>>, tr: &Vec<i64>, ch: &Vec<u64>) -> (res: Option<(Writer, ParsedX)>)
    ensures
        res is Some ==> ({
            let (w, px) = res.unwrap();
            &&& w.wf()
            &&& enc_ch(p@, cview(ctx@), iview(tr@), nview(ch@)) == Some((w.written(), pview(px)))
        }),
{
    if tr.len() != ch.len() {
        return None;
    }
    let z = zip_x(tr, ch);
    let mut w = Writer::new();
    let mut st = EStX { env: env0_x(p.nslots), sealed: false, conf: true, ti: 0 };
    proof { assert(eview(st, 0) == est0(p@)); }
    if !eblk_x(p, ctx, &z, &mut w, 64, p.main, &mut st) {
        return None;
    }
    proof { assert(w.written() =~= Seq::<bool>::empty() + w.written()); }
    if st.ti != tr.len() {
        return None;
    }
    let trc = copy_vec(tr);
    let chc = copy_vec_u(ch);
    Some((w, ParsedX { trace: trc, ch: chc, env: st.env, conf: st.conf }))
}

/// The canonical encoding of a trace (every choice 0).
pub fn encode_all(p: &ProgX, ctx: &Vec<Vec<i64>>, tr: &Vec<i64>) -> (res: Option<(Writer, ParsedX)>)
    ensures
        res is Some ==> ({
            let (w, px) = res.unwrap();
            &&& w.wf()
            &&& enc_all(p@, cview(ctx@), iview(tr@)) == Some((w.written(), pview(px)))
        }),
{
    let ch = zeros_x(tr.len());
    encode_ch(p, ctx, tr, &ch)
}

/// Encode a trace, with the given choices, as a syntax structure at the
/// front of its data, its variables starting as `env`.
pub fn encode_pre_ch_at(p: &ProgX, ctx: &Vec<Vec<i64>>, env: Vec<i64>, tr: &Vec<i64>, ch: &Vec<u64>) -> (res: Option<(Writer, ParsedX)>)
    ensures
        res is Some ==> ({
            let (w, px) = res.unwrap();
            &&& w.wf()
            &&& enc_pre_ch_at(p@, cview(ctx@), iview(env@), iview(tr@), nview(ch@)) == Some((w.written(), pview(px)))
        }),
{
    if tr.len() != ch.len() {
        return None;
    }
    let z = zip_x(tr, ch);
    let mut w = Writer::new();
    let ghost e0 = iview(env@);
    let mut st = EStX { env, sealed: false, conf: true, ti: 0 };
    proof { assert(eview(st, 0) == est_at(e0)); }
    if !eblk_x(p, ctx, &z, &mut w, 64, p.main, &mut st) {
        return None;
    }
    proof { assert(w.written() =~= Seq::<bool>::empty() + w.written()); }
    if st.ti != tr.len() || st.sealed {
        return None;
    }
    let trc = copy_vec(tr);
    let chc = copy_vec_u(ch);
    Some((w, ParsedX { trace: trc, ch: chc, env: st.env, conf: st.conf }))
}

/// Encode a trace, with the given choices, as a syntax structure at the
/// front of its data.
pub fn encode_pre_ch(p: &ProgX, ctx: &Vec<Vec<i64>>, tr: &Vec<i64>, ch: &Vec<u64>) -> (res: Option<(Writer, ParsedX)>)
    ensures
        res is Some ==> ({
            let (w, px) = res.unwrap();
            &&& w.wf()
            &&& enc_pre_ch(p@, cview(ctx@), iview(tr@), nview(ch@)) == Some((w.written(), pview(px)))
        }),
{
    let env = env0_x(p.nslots);
    proof { assert(iview(env@) =~= env0(p@)); }
    encode_pre_ch_at(p, ctx, env, tr, ch)
}

/// The canonical encoding of a trace, at the front of its data.
pub fn encode_pre(p: &ProgX, ctx: &Vec<Vec<i64>>, tr: &Vec<i64>) -> (res: Option<(Writer, ParsedX)>)
    ensures
        res is Some ==> ({
            let (w, px) = res.unwrap();
            &&& w.wf()
            &&& enc_pre(p@, cview(ctx@), iview(tr@)) == Some((w.written(), pview(px)))
        }),
{
    let ch = zeros_x(tr.len());
    encode_pre_ch(p, ctx, tr, &ch)
}

pub fn copy_vec(v: &Vec<i64>) -> (r: Vec<i64>)
    ensures r@ == v@,
{
    let mut r: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ =~= v@.take(i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        proof { assert(v@.take(i as int + 1) =~= v@.take(i as int).push(v@[i as int])); }
        i = i + 1;
    }
    proof { assert(v@.take(v@.len() as int) =~= v@); }
    r
}

pub fn copy_vec_u(v: &Vec<u64>) -> (r: Vec<u64>)
    ensures r@ == v@,
{
    let mut r: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ =~= v@.take(i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        proof { assert(v@.take(i as int + 1) =~= v@.take(i as int).push(v@[i as int])); }
        i = i + 1;
    }
    proof { assert(v@.take(v@.len() as int) =~= v@); }
    r
}

} // verus!
