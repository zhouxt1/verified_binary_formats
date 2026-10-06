//! The theorem, for every program: the decoder and the encoder of `sem`
//! are inverse.
//!
//! * `theorem_enc_dec`: a well-formed trace's encoding decodes back to it
//!   (round trip, and completeness: every conforming syntax structure is
//!   the encoding of its own trace, since the syntax tables are
//!   deterministic).
//! * `theorem_dec_enc`: whatever decodes is a well-formed trace's encoding,
//!   bit for bit (non-malleability, and soundness of the output).
//!
//! and the same two for a structure at the front of its data
//! (`theorem_pre_enc_dec`, `theorem_pre_dec_enc`), whatever follows it.
use vstd::prelude::*;
use crate::eg::*;
use crate::ir::*;
use crate::sem::*;

verus! {

pub open spec fn dof(e: ESt) -> DSt {
    DSt { env: e.env, pos: e.pos, sealed: e.sealed, conf: e.conf }
}

pub open spec fn eof(d: DSt, ti: nat) -> ESt {
    ESt { env: d.env, pos: d.pos, sealed: d.sealed, conf: d.conf, ti }
}

/// The bits written are in the window at the position, and if the
/// encoding ended in a `more_rbsp_data( )` loop, the window ends with them.
pub open spec fn fits(b: Seq<bool>, pos: nat, c: Seq<bool>, sealed: bool) -> bool {
    &&& pos + c.len() <= b.len()
    &&& b.subrange(pos as int, (pos + c.len()) as int) == c
    &&& sealed ==> pos + c.len() == b.len()
}

pub open spec fn einv(tr: Tr, es: ESt, es2: ESt, c: Seq<bool>) -> bool {
    &&& es2.pos == es.pos + c.len()
    &&& es.ti <= es2.ti
    &&& es.ti <= tr.len() ==> es2.ti <= tr.len()
    &&& es.sealed ==> es2.sealed && c.len() == 0
}

// ------------------------------------------------- encoder invariants

pub proof fn lemma_einv_blk(p: Prog, ctx: Ctx, tr: Tr, fuel: nat, blk: nat, i: nat, es: ESt)
    requires eblk(p, ctx, tr, fuel, blk, i, es) is Some,
    ensures einv(tr, es, eblk(p, ctx, tr, fuel, blk, i, es).unwrap().0, eblk(p, ctx, tr, fuel, blk, i, es).unwrap().1),
    decreases fuel, 2nat, blen(p, blk) - i,
{
    if blk < p.blocks.len() && i < p.blocks[blk as int].len() {
        let s = p.blocks[blk as int][i as int];
        lemma_einv_stmt(p, ctx, tr, fuel, s, es);
        let (es1, c1) = estmt(p, ctx, tr, fuel, s, es).unwrap();
        lemma_einv_blk(p, ctx, tr, fuel, blk, i + 1, es1);
    }
}

pub proof fn lemma_einv_stmt(p: Prog, ctx: Ctx, tr: Tr, fuel: nat, s: St, es: ESt)
    requires estmt(p, ctx, tr, fuel, s, es) is Some,
    ensures einv(tr, es, estmt(p, ctx, tr, fuel, s, es).unwrap().0, estmt(p, ctx, tr, fuel, s, es).unwrap().1),
    decreases fuel, 1nat, 0nat,
{
    match s {
        St::If(c, t, f) => {
            let v = eval(p.xs, es.env, ctx, c).unwrap();
            lemma_einv_blk(p, ctx, tr, (fuel - 1) as nat, if v != 0 { t } else { f }, 0, es);
        }
        St::While(c, body) => {
            lemma_einv_while(p, ctx, tr, fuel, c, body, maxloop(), es);
        }
        St::More(mn, mx, body) => {
            let n = tr[es.ti as int].0;
            lemma_einv_more(p, ctx, tr, fuel, body, n as nat, ESt { ti: es.ti + 1, ..es });
        }
        St::Call(blk) => {
            lemma_einv_blk(p, ctx, tr, (fuel - 1) as nat, blk, 0, es);
        }
        _ => {}
    }
}

pub proof fn lemma_einv_while(p: Prog, ctx: Ctx, tr: Tr, fuel: nat, c: nat, body: nat, n: nat, es: ESt)
    requires ewhile(p, ctx, tr, fuel, c, body, n, es) is Some,
    ensures einv(tr, es, ewhile(p, ctx, tr, fuel, c, body, n, es).unwrap().0, ewhile(p, ctx, tr, fuel, c, body, n, es).unwrap().1),
    decreases fuel, 0nat, n,
{
    let v = eval(p.xs, es.env, ctx, c).unwrap();
    if v != 0 {
        lemma_einv_blk(p, ctx, tr, (fuel - 1) as nat, body, 0, es);
        let (es1, c1) = eblk(p, ctx, tr, (fuel - 1) as nat, body, 0, es).unwrap();
        lemma_einv_while(p, ctx, tr, fuel, c, body, (n - 1) as nat, es1);
    }
}

pub proof fn lemma_einv_more(p: Prog, ctx: Ctx, tr: Tr, fuel: nat, body: nat, left: nat, es: ESt)
    requires emore(p, ctx, tr, fuel, body, left, es) is Some,
    ensures
        einv(tr, es, emore(p, ctx, tr, fuel, body, left, es).unwrap().0, emore(p, ctx, tr, fuel, body, left, es).unwrap().1),
        es.sealed ==> left == 0,
    decreases fuel, 0nat, left,
{
    if left > 0 {
        lemma_einv_blk(p, ctx, tr, (fuel - 1) as nat, body, 0, es);
        let (es1, c1) = eblk(p, ctx, tr, (fuel - 1) as nat, body, 0, es).unwrap();
        lemma_einv_more(p, ctx, tr, fuel, body, (left - 1) as nat, es1);
    }
}

// ------------------------------------------------ encode, then decode

pub proof fn lemma_a_blk(p: Prog, ctx: Ctx, tr: Tr, b: Seq<bool>, fuel: nat, blk: nat, i: nat, es: ESt)
    requires
        es.ti <= tr.len(),
        eblk(p, ctx, tr, fuel, blk, i, es) is Some,
        fits(b, es.pos, eblk(p, ctx, tr, fuel, blk, i, es).unwrap().1, eblk(p, ctx, tr, fuel, blk, i, es).unwrap().0.sealed),
    ensures
        dblk(p, ctx, b, fuel, blk, i, dof(es))
            == Some((dof(eblk(p, ctx, tr, fuel, blk, i, es).unwrap().0),
                     tr.subrange(es.ti as int, eblk(p, ctx, tr, fuel, blk, i, es).unwrap().0.ti as int))),
    decreases fuel, 2nat, blen(p, blk) - i,
{
    lemma_einv_blk(p, ctx, tr, fuel, blk, i, es);
    if blk < p.blocks.len() {
        if i >= p.blocks[blk as int].len() {
            assert(tr.subrange(es.ti as int, es.ti as int) =~= Seq::<(int, nat)>::empty());
        } else {
            let s = p.blocks[blk as int][i as int];
            let (es1, c1) = estmt(p, ctx, tr, fuel, s, es).unwrap();
            let (es2, c2) = eblk(p, ctx, tr, fuel, blk, i + 1, es1).unwrap();
            lemma_einv_stmt(p, ctx, tr, fuel, s, es);
            lemma_einv_blk(p, ctx, tr, fuel, blk, i + 1, es1);
            let c = c1 + c2;
            assert(b.subrange(es.pos as int, (es.pos + c1.len()) as int)
                   =~= b.subrange(es.pos as int, (es.pos + c.len()) as int).subrange(0, c1.len() as int));
            assert(c.subrange(0, c1.len() as int) =~= c1);
            assert(b.subrange(es1.pos as int, (es1.pos + c2.len()) as int)
                   =~= b.subrange(es.pos as int, (es.pos + c.len()) as int).subrange(c1.len() as int, c.len() as int));
            assert(c.subrange(c1.len() as int, c.len() as int) =~= c2);
            lemma_a_stmt(p, ctx, tr, b, fuel, s, es);
            lemma_a_blk(p, ctx, tr, b, fuel, blk, i + 1, es1);
            assert(tr.subrange(es.ti as int, es1.ti as int) + tr.subrange(es1.ti as int, es2.ti as int)
                   =~= tr.subrange(es.ti as int, es2.ti as int));
        }
    }
}

pub proof fn lemma_a_stmt(p: Prog, ctx: Ctx, tr: Tr, b: Seq<bool>, fuel: nat, s: St, es: ESt)
    requires
        es.ti <= tr.len(),
        estmt(p, ctx, tr, fuel, s, es) is Some,
        fits(b, es.pos, estmt(p, ctx, tr, fuel, s, es).unwrap().1, estmt(p, ctx, tr, fuel, s, es).unwrap().0.sealed),
    ensures
        dstmt(p, ctx, b, fuel, s, dof(es))
            == Some((dof(estmt(p, ctx, tr, fuel, s, es).unwrap().0),
                     tr.subrange(es.ti as int, estmt(p, ctx, tr, fuel, s, es).unwrap().0.ti as int))),
    decreases fuel, 1nat, 0nat,
{
    lemma_einv_stmt(p, ctx, tr, fuel, s, es);
    let (es2, c) = estmt(p, ctx, tr, fuel, s, es).unwrap();
    match s {
        St::Read(dst, d) => {
            let (v, w) = tr[es.ti as int];
            let dv = desc_val(p.xs, es.env, ctx, d).unwrap();
            lemma_desc_val_ok(p.xs, es.env, ctx, d);
            let rest = b.skip((es.pos + c.len()) as int);
            assert(b.skip(es.pos as int) =~= c + rest);
            lemma_desc_rt(dv, v, w, c, rest);
            assert(tr.subrange(es.ti as int, es.ti + 1int) =~= seq![(v, w)]);
        }
        St::Let(dst, e) => {
            assert(tr.subrange(es.ti as int, es.ti as int) =~= Seq::<(int, nat)>::empty());
        }
        St::Assert(e) => {
            assert(tr.subrange(es.ti as int, es.ti as int) =~= Seq::<(int, nat)>::empty());
        }
        St::Conf(e) => {
            assert(tr.subrange(es.ti as int, es.ti as int) =~= Seq::<(int, nat)>::empty());
        }
        St::If(cc, t, f) => {
            let v = eval(p.xs, es.env, ctx, cc).unwrap();
            lemma_a_blk(p, ctx, tr, b, (fuel - 1) as nat, if v != 0 { t } else { f }, 0, es);
        }
        St::While(cc, body) => {
            lemma_a_while(p, ctx, tr, b, fuel, cc, body, maxloop(), es);
        }
        St::More(mn, mx, body) => {
            let n = tr[es.ti as int].0;
            let es0 = ESt { ti: es.ti + 1, ..es };
            let (es1, c1) = emore(p, ctx, tr, fuel, body, n as nat, es0).unwrap();
            lemma_einv_more(p, ctx, tr, fuel, body, n as nat, es0);
            assert(dof(es0) == dof(es));
            lemma_a_more(p, ctx, tr, b, fuel, mn, mx, body, n as nat, 0, es0);
            assert((n as nat) as int == n);
            assert(tr[es.ti as int] == (n, 0nat));
            assert(seq![((n as nat) as int, 0nat)] + tr.subrange(es0.ti as int, es1.ti as int)
                   =~= tr.subrange(es.ti as int, es1.ti as int));
        }
        St::Call(blk) => {
            lemma_a_blk(p, ctx, tr, b, (fuel - 1) as nat, blk, 0, es);
        }
        St::Align | St::Pos(_) | St::ZAlign => {
            assert(tr.subrange(es.ti as int, es.ti as int) =~= Seq::<(int, nat)>::empty());
        }
    }
}

pub proof fn lemma_a_while(p: Prog, ctx: Ctx, tr: Tr, b: Seq<bool>, fuel: nat, c: nat, body: nat, n: nat, es: ESt)
    requires
        es.ti <= tr.len(),
        ewhile(p, ctx, tr, fuel, c, body, n, es) is Some,
        fits(b, es.pos, ewhile(p, ctx, tr, fuel, c, body, n, es).unwrap().1, ewhile(p, ctx, tr, fuel, c, body, n, es).unwrap().0.sealed),
    ensures
        dwhile(p, ctx, b, fuel, c, body, n, dof(es))
            == Some((dof(ewhile(p, ctx, tr, fuel, c, body, n, es).unwrap().0),
                     tr.subrange(es.ti as int, ewhile(p, ctx, tr, fuel, c, body, n, es).unwrap().0.ti as int))),
    decreases fuel, 0nat, n,
{
    lemma_einv_while(p, ctx, tr, fuel, c, body, n, es);
    let v = eval(p.xs, es.env, ctx, c).unwrap();
    if v == 0 {
        assert(tr.subrange(es.ti as int, es.ti as int) =~= Seq::<(int, nat)>::empty());
    } else {
        let (es1, c1) = eblk(p, ctx, tr, (fuel - 1) as nat, body, 0, es).unwrap();
        let (es2, c2) = ewhile(p, ctx, tr, fuel, c, body, (n - 1) as nat, es1).unwrap();
        lemma_einv_blk(p, ctx, tr, (fuel - 1) as nat, body, 0, es);
        lemma_einv_while(p, ctx, tr, fuel, c, body, (n - 1) as nat, es1);
        let cc = c1 + c2;
        assert(b.subrange(es.pos as int, (es.pos + c1.len()) as int)
               =~= b.subrange(es.pos as int, (es.pos + cc.len()) as int).subrange(0, c1.len() as int));
        assert(cc.subrange(0, c1.len() as int) =~= c1);
        assert(b.subrange(es1.pos as int, (es1.pos + c2.len()) as int)
               =~= b.subrange(es.pos as int, (es.pos + cc.len()) as int).subrange(c1.len() as int, cc.len() as int));
        assert(cc.subrange(c1.len() as int, cc.len() as int) =~= c2);
        lemma_a_blk(p, ctx, tr, b, (fuel - 1) as nat, body, 0, es);
        lemma_a_while(p, ctx, tr, b, fuel, c, body, (n - 1) as nat, es1);
        assert(tr.subrange(es.ti as int, es1.ti as int) + tr.subrange(es1.ti as int, es2.ti as int)
               =~= tr.subrange(es.ti as int, es2.ti as int));
    }
}

pub proof fn lemma_a_more(p: Prog, ctx: Ctx, tr: Tr, b: Seq<bool>, fuel: nat, mn: nat, mx: nat, body: nat,
                          n: nat, done: nat, es: ESt)
    requires
        es.ti <= tr.len(),
        done <= n, mn <= n <= mx,
        emore(p, ctx, tr, fuel, body, (n - done) as nat, es) is Some,
        fits(b, es.pos, emore(p, ctx, tr, fuel, body, (n - done) as nat, es).unwrap().1, true),
    ensures
        dmore(p, ctx, b, fuel, mn, mx, body, done, dof(es))
            == Some((dof(emore(p, ctx, tr, fuel, body, (n - done) as nat, es).unwrap().0), n,
                     tr.subrange(es.ti as int, emore(p, ctx, tr, fuel, body, (n - done) as nat, es).unwrap().0.ti as int))),
    decreases fuel, 0nat, n - done,
{
    let left = (n - done) as nat;
    lemma_einv_more(p, ctx, tr, fuel, body, left, es);
    if left == 0 {
        assert(tr.subrange(es.ti as int, es.ti as int) =~= Seq::<(int, nat)>::empty());
    } else {
        let (es1, c1) = eblk(p, ctx, tr, (fuel - 1) as nat, body, 0, es).unwrap();
        let (es2, c2) = emore(p, ctx, tr, fuel, body, (left - 1) as nat, es1).unwrap();
        lemma_einv_blk(p, ctx, tr, (fuel - 1) as nat, body, 0, es);
        lemma_einv_more(p, ctx, tr, fuel, body, (left - 1) as nat, es1);
        let cc = c1 + c2;
        assert(b.subrange(es.pos as int, (es.pos + c1.len()) as int)
               =~= b.subrange(es.pos as int, (es.pos + cc.len()) as int).subrange(0, c1.len() as int));
        assert(cc.subrange(0, c1.len() as int) =~= c1);
        assert(b.subrange(es1.pos as int, (es1.pos + c2.len()) as int)
               =~= b.subrange(es.pos as int, (es.pos + cc.len()) as int).subrange(c1.len() as int, cc.len() as int));
        assert(cc.subrange(c1.len() as int, cc.len() as int) =~= c2);
        lemma_a_blk(p, ctx, tr, b, (fuel - 1) as nat, body, 0, es);
        assert((n - (done + 1)) as nat == (left - 1) as nat);
        lemma_a_more(p, ctx, tr, b, fuel, mn, mx, body, n, done + 1, es1);
        assert(tr.subrange(es.ti as int, es1.ti as int) + tr.subrange(es1.ti as int, es2.ti as int)
               =~= tr.subrange(es.ti as int, es2.ti as int));
    }
}

// ------------------------------------------------ decode, then encode

pub open spec fn tin(tr: Tr, ti: nat, t: Tr) -> bool {
    ti + t.len() <= tr.len() && tr.subrange(ti as int, (ti + t.len()) as int) == t
}

pub proof fn lemma_tin_split(tr: Tr, ti: nat, t1: Tr, t2: Tr)
    requires tin(tr, ti, t1 + t2),
    ensures tin(tr, ti, t1), tin(tr, ti + t1.len(), t2),
{
    let t = t1 + t2;
    assert(tr.subrange(ti as int, (ti + t1.len()) as int) =~= t.subrange(0, t1.len() as int));
    assert(t.subrange(0, t1.len() as int) =~= t1);
    assert(tr.subrange((ti + t1.len()) as int, (ti + t1.len() + t2.len()) as int)
           =~= t.subrange(t1.len() as int, t.len() as int));
    assert(t.subrange(t1.len() as int, t.len() as int) =~= t2);
}

pub proof fn lemma_b_blk(p: Prog, ctx: Ctx, b: Seq<bool>, tr: Tr, fuel: nat, blk: nat, i: nat, ds: DSt, ti: nat)
    requires
        dblk(p, ctx, b, fuel, blk, i, ds) is Some,
        ds.pos <= b.len(),
        tin(tr, ti, dblk(p, ctx, b, fuel, blk, i, ds).unwrap().1),
    ensures ({
        let (ds2, t) = dblk(p, ctx, b, fuel, blk, i, ds).unwrap();
        &&& ds.pos <= ds2.pos <= b.len()
        &&& eblk(p, ctx, tr, fuel, blk, i, eof(ds, ti))
                == Some((eof(ds2, ti + t.len()), b.subrange(ds.pos as int, ds2.pos as int)))
    }),
    decreases fuel, 2nat, blen(p, blk) - i,
{
    if blk < p.blocks.len() {
        if i >= p.blocks[blk as int].len() {
            assert(b.subrange(ds.pos as int, ds.pos as int) =~= Seq::<bool>::empty());
        } else {
            let s = p.blocks[blk as int][i as int];
            let (ds1, t1) = dstmt(p, ctx, b, fuel, s, ds).unwrap();
            let (ds2, t2) = dblk(p, ctx, b, fuel, blk, i + 1, ds1).unwrap();
            lemma_tin_split(tr, ti, t1, t2);
            lemma_b_stmt(p, ctx, b, tr, fuel, s, ds, ti);
            lemma_b_blk(p, ctx, b, tr, fuel, blk, i + 1, ds1, ti + t1.len());
            assert(b.subrange(ds.pos as int, ds1.pos as int) + b.subrange(ds1.pos as int, ds2.pos as int)
                   =~= b.subrange(ds.pos as int, ds2.pos as int));
            assert(ti + t1.len() + t2.len() == ti + (t1 + t2).len());
        }
    }
}

pub proof fn lemma_b_stmt(p: Prog, ctx: Ctx, b: Seq<bool>, tr: Tr, fuel: nat, s: St, ds: DSt, ti: nat)
    requires
        dstmt(p, ctx, b, fuel, s, ds) is Some,
        ds.pos <= b.len(),
        tin(tr, ti, dstmt(p, ctx, b, fuel, s, ds).unwrap().1),
    ensures ({
        let (ds2, t) = dstmt(p, ctx, b, fuel, s, ds).unwrap();
        &&& ds.pos <= ds2.pos <= b.len()
        &&& estmt(p, ctx, tr, fuel, s, eof(ds, ti))
                == Some((eof(ds2, ti + t.len()), b.subrange(ds.pos as int, ds2.pos as int)))
    }),
    decreases fuel, 1nat, 0nat,
{
    let (ds2, t) = dstmt(p, ctx, b, fuel, s, ds).unwrap();
    match s {
        St::Read(dst, d) => {
            let dv = desc_val(p.xs, ds.env, ctx, d).unwrap();
            lemma_desc_val_ok(p.xs, ds.env, ctx, d);
            let sfx = b.skip(ds.pos as int);
            lemma_desc_inv(dv, sfx);
            let (v, w, k) = dparse(dv, sfx).unwrap();
            assert(sfx.take(k as int) =~= b.subrange(ds.pos as int, (ds.pos + k) as int));
            assert(tr.subrange(ti as int, ti + 1int) =~= seq![(v, w)]);
            assert(tr[ti as int] == seq![(v, w)][0]);
        }
        St::Let(dst, e) => {
            assert(b.subrange(ds.pos as int, ds.pos as int) =~= Seq::<bool>::empty());
        }
        St::Assert(e) => {
            assert(b.subrange(ds.pos as int, ds.pos as int) =~= Seq::<bool>::empty());
        }
        St::Conf(e) => {
            assert(b.subrange(ds.pos as int, ds.pos as int) =~= Seq::<bool>::empty());
        }
        St::If(c, tb, fb) => {
            let v = eval(p.xs, ds.env, ctx, c).unwrap();
            lemma_b_blk(p, ctx, b, tr, (fuel - 1) as nat, if v != 0 { tb } else { fb }, 0, ds, ti);
        }
        St::While(c, body) => {
            lemma_b_while(p, ctx, b, tr, fuel, c, body, maxloop(), ds, ti);
        }
        St::More(mn, mx, body) => {
            let (ds1, n, t1) = dmore(p, ctx, b, fuel, mn, mx, body, 0, ds).unwrap();
            assert(t =~= seq![(n as int, 0nat)] + t1);
            lemma_tin_split(tr, ti, seq![(n as int, 0nat)], t1);
            assert(tr.subrange(ti as int, ti + 1int) =~= seq![(n as int, 0nat)]);
            assert(tr[ti as int] == seq![(n as int, 0nat)][0]);
            lemma_b_more(p, ctx, b, tr, fuel, mn, mx, body, 0, ds, ti + 1);
            assert(eof(ds, ti + 1) == ESt { ti: ti + 1, ..eof(ds, ti) });
            assert((n as int) as nat == n);
        }
        St::Call(blk) => {
            lemma_b_blk(p, ctx, b, tr, (fuel - 1) as nat, blk, 0, ds, ti);
        }
        St::Align | St::ZAlign => {}
        St::Pos(_) => {
            assert(b.subrange(ds.pos as int, ds.pos as int) =~= Seq::<bool>::empty());
        }
    }
}

pub proof fn lemma_b_while(p: Prog, ctx: Ctx, b: Seq<bool>, tr: Tr, fuel: nat, c: nat, body: nat, n: nat, ds: DSt, ti: nat)
    requires
        dwhile(p, ctx, b, fuel, c, body, n, ds) is Some,
        ds.pos <= b.len(),
        tin(tr, ti, dwhile(p, ctx, b, fuel, c, body, n, ds).unwrap().1),
    ensures ({
        let (ds2, t) = dwhile(p, ctx, b, fuel, c, body, n, ds).unwrap();
        &&& ds.pos <= ds2.pos <= b.len()
        &&& ewhile(p, ctx, tr, fuel, c, body, n, eof(ds, ti))
                == Some((eof(ds2, ti + t.len()), b.subrange(ds.pos as int, ds2.pos as int)))
    }),
    decreases fuel, 0nat, n,
{
    let v = eval(p.xs, ds.env, ctx, c).unwrap();
    if v == 0 {
        assert(b.subrange(ds.pos as int, ds.pos as int) =~= Seq::<bool>::empty());
    } else {
        let (ds1, t1) = dblk(p, ctx, b, (fuel - 1) as nat, body, 0, ds).unwrap();
        let (ds2, t2) = dwhile(p, ctx, b, fuel, c, body, (n - 1) as nat, ds1).unwrap();
        lemma_tin_split(tr, ti, t1, t2);
        lemma_b_blk(p, ctx, b, tr, (fuel - 1) as nat, body, 0, ds, ti);
        lemma_b_while(p, ctx, b, tr, fuel, c, body, (n - 1) as nat, ds1, ti + t1.len());
        assert(b.subrange(ds.pos as int, ds1.pos as int) + b.subrange(ds1.pos as int, ds2.pos as int)
               =~= b.subrange(ds.pos as int, ds2.pos as int));
        assert(ti + t1.len() + t2.len() == ti + (t1 + t2).len());
    }
}

pub proof fn lemma_b_more(p: Prog, ctx: Ctx, b: Seq<bool>, tr: Tr, fuel: nat, mn: nat, mx: nat, body: nat,
                          cnt: nat, ds: DSt, ti: nat)
    requires
        dmore(p, ctx, b, fuel, mn, mx, body, cnt, ds) is Some,
        mn <= mx, cnt <= mx,
        ds.pos <= b.len(),
        tin(tr, ti, dmore(p, ctx, b, fuel, mn, mx, body, cnt, ds).unwrap().2),
    ensures ({
        let (ds2, n, t) = dmore(p, ctx, b, fuel, mn, mx, body, cnt, ds).unwrap();
        &&& cnt <= n && mn <= n <= mx
        &&& ds.pos <= ds2.pos <= b.len()
        &&& emore(p, ctx, tr, fuel, body, (n - cnt) as nat, eof(ds, ti))
                == Some((eof(ds2, ti + t.len()), b.subrange(ds.pos as int, ds2.pos as int)))
    }),
    decreases fuel, 0nat, if ds.pos <= b.len() { (b.len() - ds.pos) as nat } else { 0nat },
{
    if cnt >= mn && (cnt >= mx || ds.pos == b.len()) {
        assert(b.subrange(ds.pos as int, ds.pos as int) =~= Seq::<bool>::empty());
    } else {
        let (ds1, t1) = dblk(p, ctx, b, (fuel - 1) as nat, body, 0, ds).unwrap();
        let (ds2, n, t2) = dmore(p, ctx, b, fuel, mn, mx, body, cnt + 1, ds1).unwrap();
        lemma_tin_split(tr, ti, t1, t2);
        lemma_b_blk(p, ctx, b, tr, (fuel - 1) as nat, body, 0, ds, ti);
        lemma_b_more(p, ctx, b, tr, fuel, mn, mx, body, cnt + 1, ds1, ti + t1.len());
        assert((n - cnt - 1) as nat == ((n - cnt) as nat - 1) as nat);
        assert(b.subrange(ds.pos as int, ds1.pos as int).len() > 0);
        assert(b.subrange(ds.pos as int, ds1.pos as int) + b.subrange(ds1.pos as int, ds2.pos as int)
               =~= b.subrange(ds.pos as int, ds2.pos as int));
        assert(ti + t1.len() + t2.len() == ti + (t1 + t2).len());
    }
}

// ------------------------------------------------------------ theorems

pub proof fn lemma_vals_chs_zip(tr: Seq<int>, ch: Seq<nat>)
    requires tr.len() == ch.len(),
    ensures vals(zip(tr, ch)) =~= tr, chs(zip(tr, ch)) =~= ch,
{
}

pub proof fn lemma_zip_vals_chs(t: Tr)
    ensures zip(vals(t), chs(t)) =~= t,
{
    assert forall|i: int| 0 <= i < t.len() implies zip(vals(t), chs(t))[i] == t[i] by {
        let (a, b) = t[i];
    }
}

/// A trace's encoding, with any choices it allows, decodes back to it and
/// its choices, with the same environment and conformance (round trip).
pub proof fn theorem_enc_dec(p: Prog, ctx: Ctx, tr: Seq<int>, ch: Seq<nat>)
    requires enc_ch(p, ctx, tr, ch) is Some,
    ensures dec_all(p, ctx, enc_ch(p, ctx, tr, ch).unwrap().0) == Some(enc_ch(p, ctx, tr, ch).unwrap().1),
{
    let z = zip(tr, ch);
    let (es2, c) = eblk(p, ctx, z, fuel0(), p.main, 0, est0(p)).unwrap();
    lemma_einv_blk(p, ctx, z, fuel0(), p.main, 0, est0(p));
    assert(c.subrange(0, c.len() as int) =~= c);
    lemma_a_blk(p, ctx, z, c, fuel0(), p.main, 0, est0(p));
    assert(dof(est0(p)) == dst0(p));
    assert(z.subrange(0, z.len() as int) =~= z);
    lemma_vals_chs_zip(tr, ch);
}

/// Whatever decodes is the encoding of its trace with the choices it read,
/// bit for bit: two encodings of one value differ only in their choices.
pub proof fn theorem_dec_enc(p: Prog, ctx: Ctx, b: Seq<bool>)
    requires dec_all(p, ctx, b) is Some,
    ensures ({
        let pr = dec_all(p, ctx, b).unwrap();
        enc_ch(p, ctx, pr.trace, pr.ch) == Some((b, pr))
    }),
{
    let (ds2, t) = dblk(p, ctx, b, fuel0(), p.main, 0, dst0(p)).unwrap();
    assert(t.subrange(0, t.len() as int) =~= t);
    lemma_b_blk(p, ctx, b, t, fuel0(), p.main, 0, dst0(p), 0);
    assert(eof(dst0(p), 0) == est0(p));
    assert(b.subrange(0, b.len() as int) =~= b);
    lemma_zip_vals_chs(t);
}

/// The canonical encoder's image is exactly what decodes with every choice
/// 0: the decoder's choices say whether the bits are the canonical encoding
/// of the value they carry.
pub proof fn theorem_canon(p: Prog, ctx: Ctx, b: Seq<bool>)
    requires dec_all(p, ctx, b) is Some,
    ensures ({
        let pr = dec_all(p, ctx, b).unwrap();
        (enc_all(p, ctx, pr.trace) == Some((b, pr))) == (pr.ch =~= canon_ch(pr.trace.len()))
    }),
{
    let pr = dec_all(p, ctx, b).unwrap();
    theorem_dec_enc(p, ctx, b);
    if enc_all(p, ctx, pr.trace) == Some((b, pr)) {
        assert(pr.ch == canon_ch(pr.trace.len()));
    }
    if pr.ch =~= canon_ch(pr.trace.len()) {
        assert(enc_all(p, ctx, pr.trace) == enc_ch(p, ctx, pr.trace, pr.ch));
    }
}

/// A trace's encoding, followed by anything, decodes to it, and the
/// decoder stops where the encoding stops; from any starting environment.
pub proof fn theorem_pre_enc_dec_at(p: Prog, ctx: Ctx, e: Seq<int>, tr: Seq<int>, ch: Seq<nat>, rest: Seq<bool>)
    requires enc_pre_ch_at(p, ctx, e, tr, ch) is Some,
    ensures dec_pre_at(p, ctx, e, enc_pre_ch_at(p, ctx, e, tr, ch).unwrap().0 + rest)
        == Some((enc_pre_ch_at(p, ctx, e, tr, ch).unwrap().1, enc_pre_ch_at(p, ctx, e, tr, ch).unwrap().0.len())),
{
    let z = zip(tr, ch);
    let (es2, c) = eblk(p, ctx, z, fuel0(), p.main, 0, est_at(e)).unwrap();
    lemma_einv_blk(p, ctx, z, fuel0(), p.main, 0, est_at(e));
    let b = c + rest;
    assert(b.subrange(0, c.len() as int) =~= c);
    lemma_a_blk(p, ctx, z, b, fuel0(), p.main, 0, est_at(e));
    assert(dof(est_at(e)) == dst_at(e));
    assert(z.subrange(0, z.len() as int) =~= z);
    lemma_vals_chs_zip(tr, ch);
}

/// Whatever decodes at the front of `b` is the encoding of its trace with
/// its choices.
pub proof fn theorem_pre_dec_enc_at(p: Prog, ctx: Ctx, e: Seq<int>, b: Seq<bool>)
    requires dec_pre_at(p, ctx, e, b) is Some,
    ensures ({
        let (r, k) = dec_pre_at(p, ctx, e, b).unwrap();
        &&& k <= b.len()
        &&& enc_pre_ch_at(p, ctx, e, r.trace, r.ch) == Some((b.take(k as int), r))
    }),
{
    let (ds2, t) = dblk(p, ctx, b, fuel0(), p.main, 0, dst_at(e)).unwrap();
    assert(t.subrange(0, t.len() as int) =~= t);
    lemma_b_blk(p, ctx, b, t, fuel0(), p.main, 0, dst_at(e), 0);
    assert(eof(dst_at(e), 0) == est_at(e));
    assert(b.subrange(0, ds2.pos as int) =~= b.take(ds2.pos as int));
    lemma_zip_vals_chs(t);
}

pub proof fn theorem_pre_canon_at(p: Prog, ctx: Ctx, e: Seq<int>, b: Seq<bool>)
    requires dec_pre_at(p, ctx, e, b) is Some,
    ensures ({
        let (r, k) = dec_pre_at(p, ctx, e, b).unwrap();
        (enc_pre_ch_at(p, ctx, e, r.trace, canon_ch(r.trace.len())) == Some((b.take(k as int), r)))
            == (r.ch =~= canon_ch(r.trace.len()))
    }),
{
    let (r, k) = dec_pre_at(p, ctx, e, b).unwrap();
    theorem_pre_dec_enc_at(p, ctx, e, b);
    if enc_pre_ch_at(p, ctx, e, r.trace, canon_ch(r.trace.len())) == Some((b.take(k as int), r)) {
        assert(r.ch == canon_ch(r.trace.len()));
    }
}

pub proof fn theorem_pre_enc_dec(p: Prog, ctx: Ctx, tr: Seq<int>, ch: Seq<nat>, rest: Seq<bool>)
    requires enc_pre_ch(p, ctx, tr, ch) is Some,
    ensures dec_pre(p, ctx, enc_pre_ch(p, ctx, tr, ch).unwrap().0 + rest)
        == Some((enc_pre_ch(p, ctx, tr, ch).unwrap().1, enc_pre_ch(p, ctx, tr, ch).unwrap().0.len())),
{
    theorem_pre_enc_dec_at(p, ctx, env0(p), tr, ch, rest);
}

pub proof fn theorem_pre_dec_enc(p: Prog, ctx: Ctx, b: Seq<bool>)
    requires dec_pre(p, ctx, b) is Some,
    ensures ({
        let (r, k) = dec_pre(p, ctx, b).unwrap();
        &&& k <= b.len()
        &&& enc_pre_ch(p, ctx, r.trace, r.ch) == Some((b.take(k as int), r))
    }),
{
    theorem_pre_dec_enc_at(p, ctx, env0(p), b);
}

pub proof fn theorem_pre_canon(p: Prog, ctx: Ctx, b: Seq<bool>)
    requires dec_pre(p, ctx, b) is Some,
    ensures ({
        let (r, k) = dec_pre(p, ctx, b).unwrap();
        (enc_pre(p, ctx, r.trace) == Some((b.take(k as int), r))) == (r.ch =~= canon_ch(r.trace.len()))
    }),
{
    theorem_pre_canon_at(p, ctx, env0(p), b);
}

// ------------------------------------------------------------ rigidity

pub open spec fn no_ch(t: Tr) -> bool { forall|i: int| 0 <= i < t.len() ==> (#[trigger] t[i]).1 == 0 }

proof fn lemma_no_ch_cat(a: Tr, b: Tr)
    requires no_ch(a), no_ch(b),
    ensures no_ch(a + b),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies (#[trigger] (a + b)[i]).1 == 0 by {
        if i < a.len() { assert((a + b)[i] == a[i]); } else { assert((a + b)[i] == b[i - a.len()]); }
    }
}

pub proof fn lemma_rigid_blk(p: Prog, ctx: Ctx, b: Seq<bool>, fuel: nat, blk: nat, i: nat, st: DSt)
    requires prog_rigid(p), dblk(p, ctx, b, fuel, blk, i, st) is Some,
    ensures no_ch(dblk(p, ctx, b, fuel, blk, i, st).unwrap().1),
    decreases fuel, 2nat, blen(p, blk) - i,
{
    if blk < p.blocks.len() && i < p.blocks[blk as int].len() {
        let s = p.blocks[blk as int][i as int];
        assert(s is Read ==> desc_rigid(s->Read_1));
        lemma_rigid_stmt(p, ctx, b, fuel, s, st);
        let (st1, t1) = dstmt(p, ctx, b, fuel, s, st).unwrap();
        lemma_rigid_blk(p, ctx, b, fuel, blk, i + 1, st1);
        lemma_no_ch_cat(t1, dblk(p, ctx, b, fuel, blk, i + 1, st1).unwrap().1);
    }
}

pub proof fn lemma_rigid_stmt(p: Prog, ctx: Ctx, b: Seq<bool>, fuel: nat, s: St, st: DSt)
    requires prog_rigid(p), dstmt(p, ctx, b, fuel, s, st) is Some, s is Read ==> desc_rigid(s->Read_1),
    ensures no_ch(dstmt(p, ctx, b, fuel, s, st).unwrap().1),
    decreases fuel, 1nat, 0nat,
{
    match s {
        St::Read(dst, d) => {
            lemma_desc_val_rigid(p.xs, st.env, ctx, d);
            let dv = desc_val(p.xs, st.env, ctx, d).unwrap();
            lemma_desc_val_ok(p.xs, st.env, ctx, d);
            lemma_desc_inv(dv, b.skip(st.pos as int));
            let (v, w, k) = dparse(dv, b.skip(st.pos as int)).unwrap();
            assert(seq![(v, w)][0] == (v, w));
        }
        St::If(c, t, f) => {
            let v = eval(p.xs, st.env, ctx, c).unwrap();
            lemma_rigid_blk(p, ctx, b, (fuel - 1) as nat, if v != 0 { t } else { f }, 0, st);
        }
        St::While(c, body) => {
            lemma_rigid_while(p, ctx, b, fuel, c, body, maxloop(), st);
        }
        St::More(mn, mx, body) => {
            lemma_rigid_more(p, ctx, b, fuel, mn, mx, body, 0, st);
            let (st1, n, t) = dmore(p, ctx, b, fuel, mn, mx, body, 0, st).unwrap();
            assert(no_ch(seq![(n as int, 0nat)]));
            lemma_no_ch_cat(seq![(n as int, 0nat)], t);
        }
        St::Call(blk) => {
            lemma_rigid_blk(p, ctx, b, (fuel - 1) as nat, blk, 0, st);
        }
        _ => {}
    }
}

pub proof fn lemma_rigid_while(p: Prog, ctx: Ctx, b: Seq<bool>, fuel: nat, c: nat, body: nat, n: nat, st: DSt)
    requires prog_rigid(p), dwhile(p, ctx, b, fuel, c, body, n, st) is Some,
    ensures no_ch(dwhile(p, ctx, b, fuel, c, body, n, st).unwrap().1),
    decreases fuel, 0nat, n,
{
    let v = eval(p.xs, st.env, ctx, c).unwrap();
    if v != 0 {
        lemma_rigid_blk(p, ctx, b, (fuel - 1) as nat, body, 0, st);
        let (st1, t1) = dblk(p, ctx, b, (fuel - 1) as nat, body, 0, st).unwrap();
        lemma_rigid_while(p, ctx, b, fuel, c, body, (n - 1) as nat, st1);
        lemma_no_ch_cat(t1, dwhile(p, ctx, b, fuel, c, body, (n - 1) as nat, st1).unwrap().1);
    }
}

pub proof fn lemma_rigid_more(p: Prog, ctx: Ctx, b: Seq<bool>, fuel: nat, mn: nat, mx: nat, body: nat, cnt: nat, st: DSt)
    requires prog_rigid(p), dmore(p, ctx, b, fuel, mn, mx, body, cnt, st) is Some,
    ensures no_ch(dmore(p, ctx, b, fuel, mn, mx, body, cnt, st).unwrap().2),
    decreases fuel, 0nat, if st.pos <= b.len() { (b.len() - st.pos) as nat } else { 0nat },
{
    if !(cnt >= mn && (cnt >= mx || st.pos == b.len())) {
        lemma_rigid_blk(p, ctx, b, (fuel - 1) as nat, body, 0, st);
        let (st1, t1) = dblk(p, ctx, b, (fuel - 1) as nat, body, 0, st).unwrap();
        lemma_rigid_more(p, ctx, b, fuel, mn, mx, body, cnt + 1, st1);
        lemma_no_ch_cat(t1, dmore(p, ctx, b, fuel, mn, mx, body, cnt + 1, st1).unwrap().2);
    }
}

/// A program with no choices is non-malleable outright: whatever decodes
/// is the canonical encoding of its trace.
pub proof fn theorem_rigid(p: Prog, ctx: Ctx, b: Seq<bool>)
    requires prog_rigid(p), dec_all(p, ctx, b) is Some,
    ensures ({
        let pr = dec_all(p, ctx, b).unwrap();
        &&& pr.ch =~= canon_ch(pr.trace.len())
        &&& enc_all(p, ctx, pr.trace) == Some((b, pr))
    }),
{
    lemma_rigid_blk(p, ctx, b, fuel0(), p.main, 0, dst0(p));
    theorem_canon(p, ctx, b);
}

pub proof fn theorem_pre_rigid_at(p: Prog, ctx: Ctx, e: Seq<int>, b: Seq<bool>)
    requires prog_rigid(p), dec_pre_at(p, ctx, e, b) is Some,
    ensures ({
        let (r, k) = dec_pre_at(p, ctx, e, b).unwrap();
        &&& r.ch =~= canon_ch(r.trace.len())
        &&& enc_pre_ch_at(p, ctx, e, r.trace, canon_ch(r.trace.len())) == Some((b.take(k as int), r))
    }),
{
    lemma_rigid_blk(p, ctx, b, fuel0(), p.main, 0, dst_at(e));
    theorem_pre_canon_at(p, ctx, e, b);
}

pub proof fn theorem_pre_rigid(p: Prog, ctx: Ctx, b: Seq<bool>)
    requires prog_rigid(p), dec_pre(p, ctx, b) is Some,
    ensures ({
        let (r, k) = dec_pre(p, ctx, b).unwrap();
        &&& r.ch =~= canon_ch(r.trace.len())
        &&& enc_pre(p, ctx, r.trace) == Some((b.take(k as int), r))
    }),
{
    theorem_pre_rigid_at(p, ctx, env0(p), b);
}

} // verus!
