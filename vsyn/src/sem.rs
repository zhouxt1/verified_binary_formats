//! What a program means: a spec-level decoder, from the bits of a syntax
//! structure to its trace, and a spec-level encoder, from a trace to bits.
//!
//! The value of a syntax structure is its *trace*: the values of its syntax
//! elements in the order the syntax table reads them, and, for each
//! `more_rbsp_data( )` loop, how many times it ran. The environment (every
//! variable, derived ones included) is a function of the trace, computed
//! the same way in both directions.
//!
//! Each entry of the trace also carries a *choice*: what the encoding
//! picked that the value does not determine (how many bytes a `leb128()`
//! spent). The decoder returns the choices it read, and the encoder writes
//! the ones it is given; with every choice 0 it is the canonical encoder.
//!
//! Both directions take a fuel that bounds how deeply blocks nest (syntax
//! structures calling syntax structures), and a `while` loop runs at most
//! `maxloop` times. Running out is a failure on both sides.
//!
//! The decoder reads from a window `b`, the whole syntax structure: for a
//! parameter set, its RBSP without the trailing bits (its SODB), so that
//! `more_rbsp_data( )` is "the position is before the end of `b`".
use vstd::prelude::*;
use crate::eg::*;
use crate::ir::*;

verus! {

pub open spec fn maxloop() -> nat { 16777216 }

/// A trace as the interpreter keeps it: each value with its choice.
pub type Tr = Seq<(int, nat)>;

pub struct DSt {
    pub env: Seq<int>,
    pub pos: nat,
    /// A `more_rbsp_data( )` loop has run: the data is at its end.
    pub sealed: bool,
    /// Every `Conf` so far held.
    pub conf: bool,
}

pub struct ESt {
    pub env: Seq<int>,
    pub pos: nat,
    pub sealed: bool,
    pub conf: bool,
    /// How much of the trace has been written.
    pub ti: nat,
}

pub open spec fn blen(p: Prog, blk: nat) -> nat {
    if blk < p.blocks.len() { p.blocks[blk as int].len() } else { 0 }
}

// ------------------------------------------------------------------ decoder

pub open spec fn dblk(p: Prog, ctx: Ctx, b: Seq<bool>, fuel: nat, blk: nat, i: nat, st: DSt)
    -> Option<(DSt, Tr)>
    decreases fuel, 2nat, blen(p, blk) - i,
{
    if blk >= p.blocks.len() {
        None
    } else if i >= p.blocks[blk as int].len() {
        Some((st, Seq::empty()))
    } else {
        match dstmt(p, ctx, b, fuel, p.blocks[blk as int][i as int], st) {
            Some((st1, t1)) => match dblk(p, ctx, b, fuel, blk, i + 1, st1) {
                Some((st2, t2)) => Some((st2, t1 + t2)),
                None => None,
            },
            None => None,
        }
    }
}

pub open spec fn dstmt(p: Prog, ctx: Ctx, b: Seq<bool>, fuel: nat, s: St, st: DSt)
    -> Option<(DSt, Tr)>
    decreases fuel, 1nat, 0nat,
{
    match s {
        St::Read(dst, d) => if st.sealed || st.pos > b.len() {
            None
        } else {
            match desc_val(p.xs, st.env, ctx, d) {
                Some(dv) => match dparse(dv, b.skip(st.pos as int)) {
                    Some((v, w, k)) => match store(p.xs, st.env, ctx, dst, v) {
                        Some(env1) => Some((DSt { env: env1, pos: st.pos + k, ..st }, seq![(v, w)])),
                        None => None,
                    },
                    None => None,
                },
                None => None,
            }
        },
        St::Let(dst, e) => match eval(p.xs, st.env, ctx, e) {
            Some(v) => match store(p.xs, st.env, ctx, dst, v) {
                Some(env1) => Some((DSt { env: env1, ..st }, Seq::empty())),
                None => None,
            },
            None => None,
        },
        St::Assert(e) => match eval(p.xs, st.env, ctx, e) {
            Some(v) => if v != 0 { Some((st, Seq::empty())) } else { None },
            None => None,
        },
        St::Conf(e) => match eval(p.xs, st.env, ctx, e) {
            Some(v) => Some((DSt { conf: st.conf && v != 0, ..st }, Seq::empty())),
            None => None,
        },
        St::If(c, t, f) => if fuel == 0 {
            None
        } else {
            match eval(p.xs, st.env, ctx, c) {
                Some(v) => dblk(p, ctx, b, (fuel - 1) as nat, if v != 0 { t } else { f }, 0, st),
                None => None,
            }
        },
        St::While(c, body) => if fuel == 0 {
            None
        } else {
            dwhile(p, ctx, b, fuel, c, body, maxloop(), st)
        },
        St::More(mn, mx, body) => if fuel == 0 || mn > mx || mx > vb() {
            None
        } else {
            match dmore(p, ctx, b, fuel, mn, mx, body, 0, st) {
                Some((st1, n, t)) => Some((DSt { sealed: true, ..st1 }, seq![(n as int, 0nat)] + t)),
                None => None,
            }
        },
        St::Call(blk) => if fuel == 0 {
            None
        } else {
            dblk(p, ctx, b, (fuel - 1) as nat, blk, 0, st)
        },
        St::Align => {
            let c = align_code(st.pos);
            if !st.sealed && st.pos + c.len() <= b.len()
                && b.subrange(st.pos as int, (st.pos + c.len()) as int) == c {
                Some((DSt { pos: st.pos + c.len(), ..st }, Seq::empty()))
            } else {
                None
            }
        },
        St::Pos(dst) => if st.pos <= vb() {
            match store(p.xs, st.env, ctx, dst, st.pos as int) {
                Some(env1) => Some((DSt { env: env1, ..st }, Seq::empty())),
                None => None,
            }
        } else {
            None
        },
        St::ZAlign => {
            let c = zalign_code(st.pos);
            if !st.sealed && st.pos + c.len() <= b.len()
                && b.subrange(st.pos as int, (st.pos + c.len()) as int) == c {
                Some((DSt { pos: st.pos + c.len(), ..st }, Seq::empty()))
            } else {
                None
            }
        },
    }
}

pub open spec fn dwhile(p: Prog, ctx: Ctx, b: Seq<bool>, fuel: nat, c: nat, body: nat, n: nat, st: DSt)
    -> Option<(DSt, Tr)>
    decreases fuel, 0nat, n,
{
    if fuel == 0 {
        None
    } else {
        match eval(p.xs, st.env, ctx, c) {
            Some(v) => if v == 0 {
                Some((st, Seq::empty()))
            } else if n == 0 {
                None
            } else {
                match dblk(p, ctx, b, (fuel - 1) as nat, body, 0, st) {
                    Some((st1, t1)) => match dwhile(p, ctx, b, fuel, c, body, (n - 1) as nat, st1) {
                        Some((st2, t2)) => Some((st2, t1 + t2)),
                        None => None,
                    },
                    None => None,
                }
            },
            None => None,
        }
    }
}

/// The iterations of a `more_rbsp_data( )` loop from the `cnt`-th on: the
/// state after, how many there were in all, and their trace.
pub open spec fn dmore(p: Prog, ctx: Ctx, b: Seq<bool>, fuel: nat, mn: nat, mx: nat, body: nat,
                       cnt: nat, st: DSt) -> Option<(DSt, nat, Tr)>
    decreases fuel, 0nat, if st.pos <= b.len() { (b.len() - st.pos) as nat } else { 0nat },
{
    if fuel == 0 || st.pos > b.len() {
        None
    } else if cnt >= mn && (cnt >= mx || st.pos == b.len()) {
        Some((st, cnt, Seq::empty()))
    } else {
        match dblk(p, ctx, b, (fuel - 1) as nat, body, 0, st) {
            Some((st1, t1)) => if st1.pos > st.pos && st1.pos <= b.len() {
                match dmore(p, ctx, b, fuel, mn, mx, body, cnt + 1, st1) {
                    Some((st2, n, t2)) => Some((st2, n, t1 + t2)),
                    None => None,
                }
            } else {
                None
            },
            None => None,
        }
    }
}

// ------------------------------------------------------------------ encoder

pub open spec fn eblk(p: Prog, ctx: Ctx, tr: Tr, fuel: nat, blk: nat, i: nat, st: ESt)
    -> Option<(ESt, Seq<bool>)>
    decreases fuel, 2nat, blen(p, blk) - i,
{
    if blk >= p.blocks.len() {
        None
    } else if i >= p.blocks[blk as int].len() {
        Some((st, Seq::empty()))
    } else {
        match estmt(p, ctx, tr, fuel, p.blocks[blk as int][i as int], st) {
            Some((st1, c1)) => match eblk(p, ctx, tr, fuel, blk, i + 1, st1) {
                Some((st2, c2)) => Some((st2, c1 + c2)),
                None => None,
            },
            None => None,
        }
    }
}

pub open spec fn estmt(p: Prog, ctx: Ctx, tr: Tr, fuel: nat, s: St, st: ESt)
    -> Option<(ESt, Seq<bool>)>
    decreases fuel, 1nat, 0nat,
{
    match s {
        St::Read(dst, d) => if st.sealed || st.ti >= tr.len() {
            None
        } else {
            let (v, w) = tr[st.ti as int];
            match desc_val(p.xs, st.env, ctx, d) {
                Some(dv) => match dcode(dv, v, w) {
                    Some(c) => match store(p.xs, st.env, ctx, dst, v) {
                        Some(env1) => Some((ESt { env: env1, pos: st.pos + c.len(), ti: st.ti + 1, ..st }, c)),
                        None => None,
                    },
                    None => None,
                },
                None => None,
            }
        },
        St::Let(dst, e) => match eval(p.xs, st.env, ctx, e) {
            Some(v) => match store(p.xs, st.env, ctx, dst, v) {
                Some(env1) => Some((ESt { env: env1, ..st }, Seq::empty())),
                None => None,
            },
            None => None,
        },
        St::Assert(e) => match eval(p.xs, st.env, ctx, e) {
            Some(v) => if v != 0 { Some((st, Seq::empty())) } else { None },
            None => None,
        },
        St::Conf(e) => match eval(p.xs, st.env, ctx, e) {
            Some(v) => Some((ESt { conf: st.conf && v != 0, ..st }, Seq::empty())),
            None => None,
        },
        St::If(c, t, f) => if fuel == 0 {
            None
        } else {
            match eval(p.xs, st.env, ctx, c) {
                Some(v) => eblk(p, ctx, tr, (fuel - 1) as nat, if v != 0 { t } else { f }, 0, st),
                None => None,
            }
        },
        St::While(c, body) => if fuel == 0 {
            None
        } else {
            ewhile(p, ctx, tr, fuel, c, body, maxloop(), st)
        },
        St::More(mn, mx, body) => if fuel == 0 || mn > mx || mx > vb() || st.ti >= tr.len() {
            None
        } else {
            let (n, w) = tr[st.ti as int];
            if w == 0 && mn <= n <= mx {
                match emore(p, ctx, tr, fuel, body, n as nat, ESt { ti: st.ti + 1, ..st }) {
                    Some((st1, c)) => Some((ESt { sealed: true, ..st1 }, c)),
                    None => None,
                }
            } else {
                None
            }
        },
        St::Call(blk) => if fuel == 0 {
            None
        } else {
            eblk(p, ctx, tr, (fuel - 1) as nat, blk, 0, st)
        },
        St::Align => if st.sealed {
            None
        } else {
            let c = align_code(st.pos);
            Some((ESt { pos: st.pos + c.len(), ..st }, c))
        },
        St::Pos(dst) => if st.pos <= vb() {
            match store(p.xs, st.env, ctx, dst, st.pos as int) {
                Some(env1) => Some((ESt { env: env1, ..st }, Seq::empty())),
                None => None,
            }
        } else {
            None
        },
        St::ZAlign => if st.sealed {
            None
        } else {
            let c = zalign_code(st.pos);
            Some((ESt { pos: st.pos + c.len(), ..st }, c))
        },
    }
}

pub open spec fn ewhile(p: Prog, ctx: Ctx, tr: Tr, fuel: nat, c: nat, body: nat, n: nat, st: ESt)
    -> Option<(ESt, Seq<bool>)>
    decreases fuel, 0nat, n,
{
    if fuel == 0 {
        None
    } else {
        match eval(p.xs, st.env, ctx, c) {
            Some(v) => if v == 0 {
                Some((st, Seq::empty()))
            } else if n == 0 {
                None
            } else {
                match eblk(p, ctx, tr, (fuel - 1) as nat, body, 0, st) {
                    Some((st1, c1)) => match ewhile(p, ctx, tr, fuel, c, body, (n - 1) as nat, st1) {
                        Some((st2, c2)) => Some((st2, c1 + c2)),
                        None => None,
                    },
                    None => None,
                }
            },
            None => None,
        }
    }
}

/// `left` more iterations of a `more_rbsp_data( )` loop, each of which
/// must write something (or the decoder could not tell it was there).
pub open spec fn emore(p: Prog, ctx: Ctx, tr: Tr, fuel: nat, body: nat, left: nat, st: ESt)
    -> Option<(ESt, Seq<bool>)>
    decreases fuel, 0nat, left,
{
    if fuel == 0 {
        None
    } else if left == 0 {
        Some((st, Seq::empty()))
    } else {
        match eblk(p, ctx, tr, (fuel - 1) as nat, body, 0, st) {
            Some((st1, c1)) => if c1.len() > 0 {
                match emore(p, ctx, tr, fuel, body, (left - 1) as nat, st1) {
                    Some((st2, c2)) => Some((st2, c1 + c2)),
                    None => None,
                }
            } else {
                None
            },
            None => None,
        }
    }
}

// --------------------------------------------------------------- top level

pub open spec fn fuel0() -> nat { 64 }

pub open spec fn env0(p: Prog) -> Seq<int> { Seq::new(p.nslots, |i: int| 0int) }

pub open spec fn dst0(p: Prog) -> DSt { dst_at(env0(p)) }

pub open spec fn est0(p: Prog) -> ESt { est_at(env0(p)) }

/// Starting from environment `e` rather than all zeros: a format whose
/// variables keep their values from one syntax structure to the next (AV1's
/// are global, §4.10), run one structure at a time.
pub open spec fn dst_at(e: Seq<int>) -> DSt { DSt { env: e, pos: 0, sealed: false, conf: true } }

pub open spec fn est_at(e: Seq<int>) -> ESt { ESt { env: e, pos: 0, sealed: false, conf: true, ti: 0 } }

/// The values of a trace, and its choices.
pub open spec fn vals(t: Tr) -> Seq<int> { Seq::new(t.len(), |i: int| t[i].0) }

pub open spec fn chs(t: Tr) -> Seq<nat> { Seq::new(t.len(), |i: int| t[i].1) }

pub open spec fn zip(tr: Seq<int>, ch: Seq<nat>) -> Tr { Seq::new(tr.len(), |i: int| (tr[i], ch[i])) }

/// The canonical choices: all 0.
pub open spec fn canon_ch(n: nat) -> Seq<nat> { Seq::new(n, |i: int| 0nat) }

/// What decoding a syntax structure gives: its trace, the choices its
/// encoding made, the environment, and whether it conforms to this version.
pub struct Parsed {
    pub trace: Seq<int>,
    pub ch: Seq<nat>,
    pub env: Seq<int>,
    pub conf: bool,
}

/// A syntax structure that is the whole of `b`.
pub open spec fn dec_all(p: Prog, ctx: Ctx, b: Seq<bool>) -> Option<Parsed> {
    match dblk(p, ctx, b, fuel0(), p.main, 0, dst0(p)) {
        Some((st, t)) => if st.pos == b.len() {
            Some(Parsed { trace: vals(t), ch: chs(t), env: st.env, conf: st.conf })
        } else {
            None
        },
        None => None,
    }
}

/// The encoding of a trace with the given choices.
pub open spec fn enc_ch(p: Prog, ctx: Ctx, tr: Seq<int>, ch: Seq<nat>) -> Option<(Seq<bool>, Parsed)> {
    if tr.len() != ch.len() {
        None
    } else {
        match eblk(p, ctx, zip(tr, ch), fuel0(), p.main, 0, est0(p)) {
            Some((st, c)) => if st.ti == tr.len() {
                Some((c, Parsed { trace: tr, ch: ch, env: st.env, conf: st.conf }))
            } else {
                None
            },
            None => None,
        }
    }
}

/// The canonical encoding of a trace.
pub open spec fn enc_all(p: Prog, ctx: Ctx, tr: Seq<int>) -> Option<(Seq<bool>, Parsed)> {
    enc_ch(p, ctx, tr, canon_ch(tr.len()))
}

/// A syntax structure at the front of `b` (a slice header, before the
/// slice data), its variables starting as `e`: what it is, and how many
/// bits it took.
pub open spec fn dec_pre_at(p: Prog, ctx: Ctx, e: Seq<int>, b: Seq<bool>) -> Option<(Parsed, nat)> {
    match dblk(p, ctx, b, fuel0(), p.main, 0, dst_at(e)) {
        Some((st, t)) => if !st.sealed {
            Some((Parsed { trace: vals(t), ch: chs(t), env: st.env, conf: st.conf }, st.pos))
        } else {
            None
        },
        None => None,
    }
}

pub open spec fn enc_pre_ch_at(p: Prog, ctx: Ctx, e: Seq<int>, tr: Seq<int>, ch: Seq<nat>) -> Option<(Seq<bool>, Parsed)> {
    if tr.len() != ch.len() {
        None
    } else {
        match eblk(p, ctx, zip(tr, ch), fuel0(), p.main, 0, est_at(e)) {
            Some((st, c)) => if st.ti == tr.len() && !st.sealed {
                Some((c, Parsed { trace: tr, ch: ch, env: st.env, conf: st.conf }))
            } else {
                None
            },
            None => None,
        }
    }
}

pub open spec fn dec_pre(p: Prog, ctx: Ctx, b: Seq<bool>) -> Option<(Parsed, nat)> {
    dec_pre_at(p, ctx, env0(p), b)
}

pub open spec fn enc_pre_ch(p: Prog, ctx: Ctx, tr: Seq<int>, ch: Seq<nat>) -> Option<(Seq<bool>, Parsed)> {
    enc_pre_ch_at(p, ctx, env0(p), tr, ch)
}

pub open spec fn enc_pre(p: Prog, ctx: Ctx, tr: Seq<int>) -> Option<(Seq<bool>, Parsed)> {
    enc_pre_ch(p, ctx, tr, canon_ch(tr.len()))
}

/// A trace is well formed when the encoder writes it: every syntax
/// element is in its descriptor's domain, every `Assert` holds, and the
/// trace is exactly as long as the program reads.
pub open spec fn wf_all(p: Prog, ctx: Ctx, tr: Seq<int>) -> bool {
    enc_all(p, ctx, tr) is Some
}

/// No syntax element of the program has a choice: each value has one code.
pub open spec fn prog_rigid(p: Prog) -> bool {
    forall|i: int, j: int| 0 <= i < p.blocks.len() && 0 <= j < p.blocks[i].len()
        ==> (#[trigger] p.blocks[i][j] is Read ==> desc_rigid(p.blocks[i][j]->Read_1))
}

} // verus!
