//! The spec from the middle of a stream: what decoding the rest of a
//! stream `f` gives from each point where the streaming decoder can stop
//! (a meta-block's start, a command's start, a command's literals, ...),
//! the lemmas that one step from each point leads to the next, and that the
//! output only grows (each result's output starts with the output so far).
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::{getbits, lz_copy};
use crate::spec::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::tables::*;

verus! {

/// `b` starts with `a`.
pub open spec fn ext(a: Seq<u8>, b: Seq<u8>) -> bool { a.len() <= b.len() && b.take(a.len() as int) == a }

pub proof fn lemma_ext_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires ext(a, b), ext(b, c),
    ensures ext(a, c),
{
    assert(c.take(a.len() as int) =~= c.take(b.len() as int).take(a.len() as int));
}

pub proof fn lemma_ext_append(a: Seq<u8>, w: Seq<u8>)
    ensures ext(a, a + w),
{
    assert((a + w).take(a.len() as int) =~= a);
}

/// A stream's result, from the state and position its meta-blocks end at.
pub open spec fn fin(r: Option<(St, int)>) -> Option<(Seq<u8>, nat, bool)> {
    match r { None => None, Some((st, q)) => Some((st.out, q as nat, st.google)) }
}

/// What follows a meta-block that started at `mbp` and ended at `q` with
/// the state `st` (`metablocks` after its `metablock`).
pub open spec fn mb_rest(dict: Seq<u8>, window: nat, f: Seq<bool>, mbp: int, q: int, st: St, last: bool)
    -> Option<(St, int)>
{
    if last {
        if zero_fill(f, q) { Some((st, align8(q))) } else { None }
    } else if q <= mbp || q > f.len() {
        None
    } else {
        metablocks(dict, window, f, q, st)
    }
}

pub proof fn lemma_metablocks_unfold(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St)
    ensures metablocks(dict, window, f, p, st) == (match metablock(dict, window, f, p, st) {
        None => None,
        Some((st2, q, last)) => mb_rest(dict, window, f, p, q, st2, last),
    }),
{
}

/// The commands from `p` to the meta-block's end, and what follows it.
pub open spec fn cmds_rest(dict: Seq<u8>, window: nat, h: Hdr, f: Seq<bool>, p: int, end: nat, st: St,
                           bl: Blk, bi: Blk, bd: Blk, mbp: int, last: bool) -> Option<(St, int)> {
    match commands(dict, window, h, f, p, end, st, bl, bi, bd) {
        None => None,
        Some((st2, q)) => mb_rest(dict, window, f, mbp, q, st2, last),
    }
}

/// A command after its literals (which end at `q4`, the state `st`): its
/// distance and copy, the commands after it, and what follows. `n0`, `p0`
/// and `left0` are the output's length, the position and the commands left
/// in the block where the command started (for `commands`' measure).
pub struct Cmd0 {
    pub c: nat,
    pub clen: nat,
    pub n0: nat,
    pub p0: int,
    pub left0: nat,
    pub bi2: Blk,
}

pub open spec fn tail_rest(dict: Seq<u8>, window: nat, h: Hdr, f: Seq<bool>, q4: int, end: nat, st: St,
                           bl2: Blk, bd: Blk, k: Cmd0, mbp: int, last: bool) -> Option<(St, int)> {
    if st.out.len() >= end {
        mb_rest(dict, window, f, mbp, q4, st, last)
    } else {
        match cmd_tail(dict, window, h, f, q4, end, st, k.c, k.clen, bd) {
            None => None,
            Some((st2, bd2, q5)) =>
                if st2.out.len() >= end {
                    mb_rest(dict, window, f, mbp, q5, st2, last)
                } else if !((st2.out.len() > k.n0) || (st2.out.len() == k.n0 && k.p0 < q5 <= f.len())
                            || (st2.out.len() == k.n0 && q5 == k.p0 && k.bi2.left < k.left0)) {
                    None
                } else {
                    cmds_rest(dict, window, h, f, q5, end, st2, bl2, k.bi2, bd2, mbp, last)
                },
        }
    }
}

/// A command's literals, `n` of them left from `p`, then the rest.
pub open spec fn lits_rest(dict: Seq<u8>, window: nat, h: Hdr, f: Seq<bool>, p: int, n: nat, end: nat, st: St,
                           bl: Blk, bd: Blk, k: Cmd0, mbp: int, last: bool) -> Option<(St, int)> {
    match lits(h, f, p, n, st.out, bl) {
        None => None,
        Some((out2, bl2, q4)) =>
            tail_rest(dict, window, h, f, q4, end, St { out: out2, ring: st.ring, google: st.google }, bl2, bd, k, mbp, last),
    }
}

/// The start of a command: its head, then its literals.
pub proof fn lemma_cmds_unfold(dict: Seq<u8>, window: nat, h: Hdr, f: Seq<bool>, p: int, end: nat, st: St,
                               bl: Blk, bi: Blk, bd: Blk, mbp: int, last: bool)
    ensures cmds_rest(dict, window, h, f, p, end, st, bl, bi, bd, mbp, last) == (match cmd_head(h, f, p, bi) {
        None => None,
        Some((bi2, c, ilen, clen, q3)) =>
            if st.out.len() + ilen > end {
                None
            } else {
                lits_rest(dict, window, h, f, q3, ilen, end, st, bl, bd,
                          Cmd0 { c, clen, n0: st.out.len(), p0: p, left0: bi.left, bi2 }, mbp, last)
            },
    }),
{
    reveal_with_fuel(commands, 2);
}

/// One literal of `n` from `p`.
pub proof fn lemma_lits_step(h: Hdr, f: Seq<bool>, p: int, n: nat, out: Seq<u8>, bl: Blk)
    requires n > 0,
    ensures lits(h, f, p, n, out, bl) == (match next_blk(h.cl, bl, f, p) {
        None => None,
        Some((bl2, q)) => {
            let ctx = lit_ctx(h.modes[bl2.t as int], p1(out), p2b(out));
            match dsym(h.lit[h.cmapl[(64 * bl2.t + ctx) as int] as int], f, q) {
                None => None,
                Some((s, r)) => lits(h, f, r, (n - 1) as nat, out.push(s as u8), bl2),
            }
        },
    }),
{
}

/// `a + b` literals are `a` literals, then `b`.
pub proof fn lemma_lits_split(h: Hdr, f: Seq<bool>, p: int, a: nat, b: nat, out: Seq<u8>, bl: Blk)
    ensures lits(h, f, p, a + b, out, bl) == (match lits(h, f, p, a, out, bl) {
        None => None,
        Some((o, k, q)) => lits(h, f, q, b, o, k),
    }),
    decreases a,
{
    if a > 0 {
        if let Some((bl2, q)) = next_blk(h.cl, bl, f, p) {
            let ctx = lit_ctx(h.modes[bl2.t as int], p1(out), p2b(out));
            if let Some((s, r)) = dsym(h.lit[h.cmapl[(64 * bl2.t + ctx) as int] as int], f, q) {
                assert((a + b - 1) as nat == ((a - 1) as nat) + b);
                lemma_lits_split(h, f, r, (a - 1) as nat, b, out.push(s as u8), bl2);
            }
        }
    }
}

// ----------------------------------------------------- the output grows

pub proof fn lemma_lits_ext(h: Hdr, f: Seq<bool>, p: int, n: nat, out: Seq<u8>, bl: Blk)
    ensures lits(h, f, p, n, out, bl) matches Some((o, k, q)) ==> ext(out, o) && o.len() == out.len() + n,
    decreases n,
{
    assert(out.take(out.len() as int) =~= out);
    if n > 0 {
        if let Some((bl2, q)) = next_blk(h.cl, bl, f, p) {
            let ctx = lit_ctx(h.modes[bl2.t as int], p1(out), p2b(out));
            if let Some((s, r)) = dsym(h.lit[h.cmapl[(64 * bl2.t + ctx) as int] as int], f, q) {
                lemma_lits_ext(h, f, r, (n - 1) as nat, out.push(s as u8), bl2);
                lemma_ext_append(out, seq![s as u8]);
                assert(out.push(s as u8) =~= out + seq![s as u8]);
                if let Some((o, k, q2)) = lits(h, f, r, (n - 1) as nat, out.push(s as u8), bl2) {
                    lemma_ext_trans(out, out.push(s as u8), o);
                }
            }
        }
    }
}

/// A copy only appends.
pub proof fn lemma_lz_copy_ext(out: Seq<u8>, d: nat, len: nat)
    ensures ext(out, lz_copy(out, d, len)),
    decreases len,
{
    assert(out.take(out.len() as int) =~= out);
    if len > 0 {
        let o1 = out.push(out[out.len() - d]);
        lemma_lz_copy_ext(o1, d, (len - 1) as nat);
        assert(o1.take(out.len() as int) =~= out);
        lemma_ext_trans(out, o1, lz_copy(o1, d, (len - 1) as nat));
    }
}

pub proof fn lemma_do_copy_ext(dict: Seq<u8>, window: nat, st: St, d: int, explicit: bool, clen: nat, end: nat)
    ensures do_copy(dict, window, st, d, explicit, clen, end) matches Some(st2) ==> ext(st.out, st2.out),
{
    let maxd: int = if st.out.len() < window { st.out.len() as int } else { window as int };
    if d > maxd {
        if let Some(st2) = dict_ref(dict, maxd, st, d, clen, end) {
            let wid = (d - maxd - 1) as nat;
            let nw = p2(ndbits()[clen as int] as nat);
            lemma_ext_append(st.out, transform(wid / nw, dict_word(dict, clen, wid % nw)));
        }
    } else {
        lemma_lz_copy_ext(st.out, d as nat, clen);
    }
}

pub proof fn lemma_cmd_tail_ext(dict: Seq<u8>, window: nat, h: Hdr, f: Seq<bool>, p: int, end: nat, st: St,
                                c: nat, clen: nat, bd: Blk)
    ensures cmd_tail(dict, window, h, f, p, end, st, c, clen, bd) matches Some((st2, k, q)) ==> ext(st.out, st2.out),
{
    if let Some((d, e, bd2, q)) = read_dist(h, st.ring, c, clen, f, p, bd) {
        lemma_do_copy_ext(dict, window, st, d, e, clen, end);
    }
}

/// A distance is at least 1, when the ring's distances are.
pub proof fn lemma_d_pos(h: Hdr, ring: Seq<int>, c: nat, clen: nat, f: Seq<bool>, p: int, bd: Blk)
    ensures read_dist(h, ring, c, clen, f, p, bd) matches Some((d, e, k, q)) ==>
        (d >= 1 || (c < 128 && d == ring[0])),
{
}

pub proof fn lemma_commands_ext(dict: Seq<u8>, window: nat, h: Hdr, f: Seq<bool>, p: int, end: nat, st: St,
                                bl: Blk, bi: Blk, bd: Blk)
    ensures commands(dict, window, h, f, p, end, st, bl, bi, bd) matches Some((st2, q)) ==> ext(st.out, st2.out),
    decreases end - st.out.len(), f.len() - p, bi.left,
{
    if let Some((bi2, c, ilen, clen, q3)) = cmd_head(h, f, p, bi) {
        if st.out.len() + ilen <= end {
            lemma_lits_ext(h, f, q3, ilen, st.out, bl);
            if let Some((out2, bl2, q4)) = lits(h, f, q3, ilen, st.out, bl) {
                let s1 = St { out: out2, ring: st.ring, google: st.google };
                if out2.len() < end {
                    lemma_cmd_tail_ext(dict, window, h, f, q4, end, s1, c, clen, bd);
                    if let Some((st2, bd2, q5)) = cmd_tail(dict, window, h, f, q4, end, s1, c, clen, bd) {
                        lemma_ext_trans(st.out, out2, st2.out);
                        if st2.out.len() < end && ((st2.out.len() > st.out.len())
                            || (st2.out.len() == st.out.len() && p < q5 <= f.len())
                            || (st2.out.len() == st.out.len() && q5 == p && bi2.left < bi.left)) {
                            lemma_commands_ext(dict, window, h, f, q5, end, st2, bl2, bi2, bd2);
                            if let Some((st3, q6)) = commands(dict, window, h, f, q5, end, st2, bl2, bi2, bd2) {
                                lemma_ext_trans(st.out, st2.out, st3.out);
                            }
                        }
                    }
                }
            }
        }
    }
}

pub proof fn lemma_data_ext(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St, mlen: nat, last: bool)
    ensures data(dict, window, f, p, st, mlen, last) matches Some((st2, q, l)) ==> ext(st.out, st2.out),
{
    let r = if last { p } else { p + 1 };
    lemma_ext_append(st.out, bytes_at(f, align8(r), mlen));
    if let Some((h, r2)) = read_hdr(f, r) {
        lemma_commands_ext(dict, window, h, f, r2, st.out.len() + mlen, st, blk0(h.cl), blk0(h.ci), blk0(h.cd));
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_metablock_ext(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St)
    ensures metablock(dict, window, f, p, st) matches Some((st2, q, last)) ==> ext(st.out, st2.out),
{
    hide(data);
    assert(ext(st.out, st.out)) by { assert(st.out.take(st.out.len() as int) =~= st.out); }
    if let Some(islast) = getbits(f, p, 1) {
        let q = if islast == 1 { p + 2 } else { p + 1 };
        if let Some(m) = getbits(f, q, 2) {
            if m != 3 {
                let nib = m + 4;
                if let Some(v) = getbits(f, q + 2, 4 * nib) {
                    lemma_data_ext(dict, window, f, q + 2 + 4 * nib, st, v + 1, islast == 1);
                }
            }
        }
    }
}

pub proof fn lemma_metablocks_ext(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St)
    ensures metablocks(dict, window, f, p, st) matches Some((st2, q)) ==> ext(st.out, st2.out),
    decreases f.len() - p,
{
    lemma_metablock_ext(dict, window, f, p, st);
    if let Some((st2, q, last)) = metablock(dict, window, f, p, st) {
        if !last && !(q <= p || q > f.len()) {
            lemma_metablocks_ext(dict, window, f, q, st2);
            if let Some((st3, q3)) = metablocks(dict, window, f, q, st2) {
                lemma_ext_trans(st.out, st2.out, st3.out);
            }
        }
    }
}

pub proof fn lemma_mb_rest_ext(dict: Seq<u8>, window: nat, f: Seq<bool>, mbp: int, q: int, st: St, last: bool)
    ensures mb_rest(dict, window, f, mbp, q, st, last) matches Some((st2, q2)) ==> ext(st.out, st2.out),
{
    assert(ext(st.out, st.out)) by { assert(st.out.take(st.out.len() as int) =~= st.out); }
    if !last && !(q <= mbp || q > f.len()) {
        lemma_metablocks_ext(dict, window, f, q, st);
    }
}

pub proof fn lemma_cmds_rest_ext(dict: Seq<u8>, window: nat, h: Hdr, f: Seq<bool>, p: int, end: nat, st: St,
                                 bl: Blk, bi: Blk, bd: Blk, mbp: int, last: bool)
    ensures cmds_rest(dict, window, h, f, p, end, st, bl, bi, bd, mbp, last) matches Some((st2, q)) ==> ext(st.out, st2.out),
{
    lemma_commands_ext(dict, window, h, f, p, end, st, bl, bi, bd);
    if let Some((st2, q)) = commands(dict, window, h, f, p, end, st, bl, bi, bd) {
        lemma_mb_rest_ext(dict, window, f, mbp, q, st2, last);
        if let Some((st3, q3)) = mb_rest(dict, window, f, mbp, q, st2, last) {
            lemma_ext_trans(st.out, st2.out, st3.out);
        }
    }
}

pub proof fn lemma_tail_rest_ext(dict: Seq<u8>, window: nat, h: Hdr, f: Seq<bool>, q4: int, end: nat, st: St,
                                 bl2: Blk, bd: Blk, k: Cmd0, mbp: int, last: bool)
    ensures tail_rest(dict, window, h, f, q4, end, st, bl2, bd, k, mbp, last) matches Some((st2, q)) ==> ext(st.out, st2.out),
{
    if st.out.len() >= end {
        lemma_mb_rest_ext(dict, window, f, mbp, q4, st, last);
    } else {
        lemma_cmd_tail_ext(dict, window, h, f, q4, end, st, k.c, k.clen, bd);
        if let Some((st2, bd2, q5)) = cmd_tail(dict, window, h, f, q4, end, st, k.c, k.clen, bd) {
            lemma_mb_rest_ext(dict, window, f, mbp, q5, st2, last);
            lemma_cmds_rest_ext(dict, window, h, f, q5, end, st2, bl2, k.bi2, bd2, mbp, last);
            if let Some((st3, q6)) = tail_rest(dict, window, h, f, q4, end, st, bl2, bd, k, mbp, last) {
                lemma_ext_trans(st.out, st2.out, st3.out);
            }
        }
    }
}

pub proof fn lemma_lits_rest_ext(dict: Seq<u8>, window: nat, h: Hdr, f: Seq<bool>, p: int, n: nat, end: nat, st: St,
                                 bl: Blk, bd: Blk, k: Cmd0, mbp: int, last: bool)
    ensures lits_rest(dict, window, h, f, p, n, end, st, bl, bd, k, mbp, last) matches Some((st2, q)) ==> ext(st.out, st2.out),
{
    lemma_lits_ext(h, f, p, n, st.out, bl);
    if let Some((out2, bl2, q4)) = lits(h, f, p, n, st.out, bl) {
        let s1 = St { out: out2, ring: st.ring, google: st.google };
        lemma_tail_rest_ext(dict, window, h, f, q4, end, s1, bl2, bd, k, mbp, last);
        if let Some((st3, q6)) = tail_rest(dict, window, h, f, q4, end, s1, bl2, bd, k, mbp, last) {
            lemma_ext_trans(st.out, out2, st3.out);
        }
    }
}

// ------------------------------------------------ a meta-block's header

/// A meta-block's header (9.2), up to its body: the last and empty
/// meta-block; metadata, `n` bytes from the byte boundary `a`; uncompressed
/// data, `mlen` bytes from `a`; or compressed data whose header starts at `r`.
pub enum Mh {
    LastEmpty,
    Meta { a: int, n: nat, last: bool },
    Raw { a: int, mlen: nat },
    Comp { r: int, mlen: nat, last: bool },
}

/// A metadata meta-block's header, from its reserved bit at `pm`.
pub open spec fn mb_meta(f: Seq<bool>, pm: int, last: bool) -> Option<Mh> {
    match (getbits(f, pm, 1), getbits(f, pm + 1, 2)) {
        (Some(reserved), Some(nbytes)) => {
            let len = if nbytes == 0 { Some(0nat) } else {
                match getbits(f, pm + 3, 8 * nbytes) {
                    None => None,
                    Some(v) => if nbytes > 1 && v / p2(8 * (nbytes - 1) as nat) == 0 { None } else { Some(v + 1) },
                }
            };
            let r = pm + 3 + 8 * nbytes;
            match len {
                None => None,
                Some(n) => if reserved != 0 || !zero_fill(f, r) { None } else { Some(Mh::Meta { a: align8(r), n, last }) },
            }
        }
        _ => None,
    }
}

/// A data meta-block's header, from its MNIBBLES `m` (read at `q`).
pub open spec fn mb_data(f: Seq<bool>, q: int, m: nat, last: bool) -> Option<Mh> {
    let nib = m + 4;
    match getbits(f, q + 2, 4 * nib) {
        None => None,
        Some(v) =>
            if nib > 4 && v / p2(4 * (nib - 1) as nat) == 0 {
                None
            } else {
                let pd = q + 2 + 4 * nib;
                let unc = if last { Some(0nat) } else { getbits(f, pd, 1) };
                let r = if last { pd } else { pd + 1 };
                match unc {
                    None => None,
                    Some(u) =>
                        if u == 1 {
                            if !zero_fill(f, r) { None } else { Some(Mh::Raw { a: align8(r), mlen: v + 1 }) }
                        } else {
                            Some(Mh::Comp { r, mlen: v + 1, last })
                        },
                }
            },
    }
}

pub open spec fn mb_head(f: Seq<bool>, p: int) -> Option<Mh> {
    match getbits(f, p, 1) {
        None => None,
        Some(islast) => {
            let empty = if islast == 1 { getbits(f, p + 1, 1) } else { Some(0nat) };
            match empty {
                None => None,
                Some(e) =>
                    if e == 1 {
                        Some(Mh::LastEmpty)
                    } else {
                        let q = if islast == 1 { p + 2 } else { p + 1 };
                        match getbits(f, q, 2) {
                            None => None,
                            Some(m) => if m == 3 { mb_meta(f, q + 2, islast == 1) } else { mb_data(f, q, m, islast == 1) },
                        }
                    },
            }
        },
    }
}

/// Where a header's fields end.
pub open spec fn mh_end(m: Mh, p: int) -> int {
    match m { Mh::LastEmpty => p + 2, Mh::Meta { a, n, last } => a, Mh::Raw { a, mlen } => a, Mh::Comp { r, mlen, last } => r }
}

/// A header's positions moved by `d`.
pub open spec fn mh_mv(m: Mh, d: int) -> Mh {
    match m {
        Mh::LastEmpty => Mh::LastEmpty,
        Mh::Meta { a, n, last } => Mh::Meta { a: a + d, n, last },
        Mh::Raw { a, mlen } => Mh::Raw { a: a + d, mlen },
        Mh::Comp { r, mlen, last } => Mh::Comp { r: r + d, mlen, last },
    }
}

/// A meta-block is its header, then its body.
#[verifier::spinoff_prover]
pub proof fn lemma_metablock_head(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St)
    ensures metablock(dict, window, f, p, st) == (match mb_head(f, p) {
        None => None,
        Some(Mh::LastEmpty) => Some((st, p + 2, true)),
        Some(Mh::Meta { a, n, last }) => if a + 8 * n > f.len() { None } else { Some((st, a + 8 * n, last)) },
        Some(Mh::Raw { a, mlen }) =>
            if a + 8 * mlen > f.len() { None }
            else { Some((St { out: st.out + bytes_at(f, a, mlen), ring: st.ring, google: st.google }, a + 8 * mlen, false)) },
        Some(Mh::Comp { r, mlen, last }) => match read_hdr(f, r) {
            None => None,
            Some((h, r2)) => match commands(dict, window, h, f, r2, st.out.len() + mlen, st, blk0(h.cl), blk0(h.ci), blk0(h.cd)) {
                None => None,
                Some((st2, r3)) => Some((st2, r3, last)),
            },
        },
    }),
{
    hide(read_hdr);
    hide(commands);
}

pub proof fn lemma_mb_head_pos(f: Seq<bool>, p: int)
    ensures mb_head(f, p) matches Some(m) ==> p + 2 <= mh_end(m, p) <= p + 40 && mh_end(m, p) <= f.len()
        && (!(m is LastEmpty) ==> p + 3 <= mh_end(m, p))
        && (m matches Mh::Meta { a, n, last } ==> a % 8 == 0)
        && (m matches Mh::Raw { a, mlen } ==> a % 8 == 0 && 1 <= mlen <= 0x100_0000)
        && (m matches Mh::Comp { r, mlen, last } ==> 1 <= mlen <= 0x100_0000)
        && (m matches Mh::Meta { a, n, last } ==> n <= 0x100_0000),
{
    reveal_with_fuel(p2, 3);
    if let Some(islast) = getbits(f, p, 1) {
        let q = if islast == 1 { p + 2 } else { p + 1 };
        if let Some(m) = getbits(f, q, 2) {
            crate::moves::lemma_getbits_bound_(f, q, 2);
            if m == 3 {
                if let Some(nbytes) = getbits(f, q + 3, 2) {
                    crate::moves::lemma_getbits_bound_(f, q + 3, 2);
                    if nbytes > 0 {
                        if let Some(v) = getbits(f, q + 5, 8 * nbytes) {
                            crate::moves::lemma_getbits_bound_(f, q + 5, 8 * nbytes);
                            vbits::prim_read::lemma_p2_mono(8 * nbytes, 24);
                            assert(p2(24) == 0x100_0000) by { reveal_with_fuel(p2, 25); }
                        }
                    }
                    let r = q + 5 + 8 * nbytes;
                    assert(align8(r) <= r + 7);
                }
            } else {
                let nib = m + 4;
                if let Some(v) = getbits(f, q + 2, 4 * nib) {
                    crate::moves::lemma_getbits_bound_(f, q + 2, 4 * nib);
                    vbits::prim_read::lemma_p2_mono(4 * nib, 24);
                    assert(p2(24) == 0x100_0000) by { reveal_with_fuel(p2, 25); }
                }
            }
        }
    }
}

pub open spec fn pos_mh(r: Option<Mh>, p: int) -> int { match r { Some(m) => mh_end(m, p), None => 0 } }

#[verifier::spinoff_prover]
pub proof fn lemma_mb_meta_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int, last: bool)
    requires mb_meta(b1, pa, last) is Some, pos_mh(mb_meta(b1, pa, last), pa) - pa <= nn, crate::moves::same(b1, pa, b2, pb, nn),
    ensures mb_meta(b2, pb, last) == Some(mh_mv(mb_meta(b1, pa, last).unwrap(), pb - pa)),
{
    use crate::moves::*;
    reveal_with_fuel(p2, 3);
    lemma_getbits_mv(b1, pa, b2, pb, nn, 1);
    lemma_same_sub(b1, pa, b2, pb, nn, 1, nn - 1);
    lemma_getbits_mv(b1, pa + 1, b2, pb + 1, nn - 1, 2);
    let nbytes = getbits(b1, pa + 1, 2).unwrap();
    lemma_getbits_bound_(b1, pa + 1, 2);
    let r = pa + 3 + 8 * nbytes;
    assert(align8(r) >= r);
    if nbytes > 0 {
        lemma_same_sub(b1, pa, b2, pb, nn, 3, nn - 3);
        lemma_getbits_mv(b1, pa + 3, b2, pb + 3, nn - 3, 8 * nbytes);
    }
    lemma_same_sub(b1, pa, b2, pb, nn, r - pa, nn - (r - pa));
    lemma_zero_fill_mv(b1, r, b2, mv(r, pa, pb), nn - (r - pa));
}

#[verifier::spinoff_prover]
pub proof fn lemma_mb_data_mv(b1: Seq<bool>, qa: int, b2: Seq<bool>, qb: int, nn: int, m: nat, last: bool)
    requires m < 3, mb_data(b1, qa, m, last) is Some, pos_mh(mb_data(b1, qa, m, last), qa) - qa <= nn,
        crate::moves::same(b1, qa, b2, qb, nn),
    ensures mb_data(b2, qb, m, last) == Some(mh_mv(mb_data(b1, qa, m, last).unwrap(), qb - qa)),
{
    use crate::moves::*;
    let nib = m + 4;
    let pd = qa + 2 + 4 * nib;
    assert(pos_mh(mb_data(b1, qa, m, last), qa) >= pd) by {
        if !last && getbits(b1, pd, 1).unwrap() == 1 { assert(align8(pd + 1) >= pd + 1); }
    }
    lemma_same_sub(b1, qa, b2, qb, nn, 2, nn - 2);
    lemma_getbits_mv(b1, qa + 2, b2, qb + 2, nn - 2, 4 * nib);
    if !last {
        lemma_same_sub(b1, qa, b2, qb, nn, pd - qa, nn - (pd - qa));
        lemma_getbits_mv(b1, pd, b2, mv(pd, qa, qb), nn - (pd - qa), 1);
        if getbits(b1, pd, 1).unwrap() == 1 {
            assert(align8(pd + 1) >= pd + 1);
            lemma_same_sub(b1, qa, b2, qb, nn, pd + 1 - qa, nn - (pd + 1 - qa));
            lemma_zero_fill_mv(b1, pd + 1, b2, mv(pd + 1, qa, qb), nn - (pd + 1 - qa));
        }
    }
}

pub proof fn lemma_mb_meta_ge(f: Seq<bool>, pm: int, last: bool)
    ensures mb_meta(f, pm, last) matches Some(m) ==> mh_end(m, pm) >= pm + 3,
{
    if let (Some(reserved), Some(nbytes)) = (getbits(f, pm, 1), getbits(f, pm + 1, 2)) {
        assert(align8(pm + 3 + 8 * nbytes) >= pm + 3 + 8 * nbytes);
    }
}

pub proof fn lemma_mb_data_ge(f: Seq<bool>, q: int, m: nat, last: bool)
    ensures mb_data(f, q, m, last) matches Some(x) ==> mh_end(x, q) >= q + 18,
{
    let pd = q + 2 + 4 * (m + 4);
    assert(align8(pd + 1) >= pd + 1);
}

#[verifier::spinoff_prover]
pub proof fn lemma_mb_head_mv(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, nn: int)
    requires mb_head(b1, pa) matches Some(m) && mh_end(m, pa) - pa <= nn, crate::moves::same(b1, pa, b2, pb, nn),
    ensures mb_head(b2, pb) == Some(mh_mv(mb_head(b1, pa).unwrap(), pb - pa)),
{
    use crate::moves::*;
    hide(mb_meta);
    hide(mb_data);
    reveal_with_fuel(p2, 3);
    let islast = getbits(b1, pa, 1).unwrap();
    let q0 = if islast == 1 { pa + 2 } else { pa + 1 };
    lemma_mb_meta_ge(b1, q0 + 2, islast == 1);
    lemma_mb_data_ge(b1, q0, getbits(b1, q0, 2).unwrap_or(0), islast == 1);
    lemma_getbits_mv(b1, pa, b2, pb, nn, 1);
    if islast == 1 {
        lemma_same_sub(b1, pa, b2, pb, nn, 1, nn - 1);
        lemma_getbits_mv(b1, pa + 1, b2, pb + 1, nn - 1, 1);
    }
    let e = if islast == 1 { getbits(b1, pa + 1, 1).unwrap() } else { 0 };
    if e != 1 {
        let q = if islast == 1 { pa + 2 } else { pa + 1 };
        let d = q - pa;
        lemma_mb_head_pos(b1, pa);
        lemma_same_sub(b1, pa, b2, pb, nn, d, nn - d);
        lemma_getbits_mv(b1, q, b2, pb + d, nn - d, 2);
        let m = getbits(b1, q, 2).unwrap();
        lemma_getbits_bound_(b1, q, 2);
        if m == 3 {
            lemma_same_sub(b1, pa, b2, pb, nn, d + 2, nn - (d + 2));
            lemma_mb_meta_mv(b1, q + 2, b2, pb + d + 2, nn - (d + 2), islast == 1);
        } else {
            lemma_mb_data_mv(b1, q, b2, pb + d, nn - d, m, islast == 1);
        }
    }
}

// ----------------------------------------------------------- the phases

/// Where the streaming decoder is: before WBITS; at a meta-block's start;
/// skipping metadata to `q_end`; copying uncompressed data to `q_end`;
/// before a compressed meta-block's header; at a command's start; in a
/// command's literals (`n` left); before the fill bits after the last
/// meta-block; done. `end` is where the meta-block's output ends; `mbp`
/// where the meta-block started.
pub enum Ph {
    Start,
    Mb,
    Skip { q_end: int, last: bool, mbp: int },
    Raw { q_end: int, mbp: int },
    Hdr { end: nat, last: bool, mbp: int },
    Cmd { h: Hdr, end: nat, last: bool, mbp: int, bl: Blk, bi: Blk, bd: Blk },
    Lits { h: Hdr, end: nat, last: bool, mbp: int, n: nat, bl: Blk, bd: Blk, k: Cmd0 },
    Fill,
    Done { bits: nat },
}

/// What the stream `f` decodes to, from the phase `ph` at position `p`
/// with the state `st`.
pub open spec fn cont(dict: Seq<u8>, window: nat, ph: Ph, f: Seq<bool>, p: int, st: St)
    -> Option<(Seq<u8>, nat, bool)>
{
    match ph {
        Ph::Start => brotli(dict, f),
        Ph::Mb => fin(metablocks(dict, window, f, p, st)),
        Ph::Skip { q_end, last, mbp } =>
            if q_end > f.len() { None } else { fin(mb_rest(dict, window, f, mbp, q_end, st, last)) },
        Ph::Raw { q_end, mbp } =>
            if q_end > f.len() { None } else {
                fin(mb_rest(dict, window, f, mbp, q_end,
                            St { out: st.out + bytes_at(f, p, ((q_end - p) / 8) as nat), ring: st.ring, google: st.google },
                            false))
            },
        Ph::Hdr { end, last, mbp } => match read_hdr(f, p) {
            None => None,
            Some((h, r2)) => fin(cmds_rest(dict, window, h, f, r2, end, st, blk0(h.cl), blk0(h.ci), blk0(h.cd), mbp, last)),
        },
        Ph::Cmd { h, end, last, mbp, bl, bi, bd } => fin(cmds_rest(dict, window, h, f, p, end, st, bl, bi, bd, mbp, last)),
        Ph::Lits { h, end, last, mbp, n, bl, bd, k } => fin(lits_rest(dict, window, h, f, p, n, end, st, bl, bd, k, mbp, last)),
        Ph::Fill => if zero_fill(f, p) { Some((st.out, align8(p) as nat, st.google)) } else { None },
        Ph::Done { bits } => Some((st.out, bits, st.google)),
    }
}

// ------------------------------------------- the continuation, by phase

pub proof fn lemma_cont_mb(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St)
    ensures cont(dict, window, Ph::Mb, f, p, st) == fin(metablocks(dict, window, f, p, st)),
{
    hide(metablocks); hide(read_hdr); hide(cmds_rest); hide(lits_rest); hide(mb_rest); hide(brotli);
}

pub proof fn lemma_cont_skip(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St, q_end: int, last: bool, mbp: int)
    ensures cont(dict, window, Ph::Skip { q_end, last, mbp }, f, p, st)
        == (if q_end > f.len() { None } else { fin(mb_rest(dict, window, f, mbp, q_end, st, last)) }),
{
    hide(metablocks); hide(read_hdr); hide(cmds_rest); hide(lits_rest); hide(mb_rest); hide(brotli);
}

pub proof fn lemma_cont_raw(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St, q_end: int, mbp: int)
    ensures cont(dict, window, Ph::Raw { q_end, mbp }, f, p, st)
        == (if q_end > f.len() { None } else {
                fin(mb_rest(dict, window, f, mbp, q_end,
                            St { out: st.out + bytes_at(f, p, ((q_end - p) / 8) as nat), ring: st.ring, google: st.google },
                            false))
            }),
{
    hide(metablocks); hide(read_hdr); hide(cmds_rest); hide(lits_rest); hide(mb_rest); hide(brotli);
}

pub proof fn lemma_cont_hdr(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St, end: nat, last: bool, mbp: int)
    ensures cont(dict, window, Ph::Hdr { end, last, mbp }, f, p, st) == (match read_hdr(f, p) {
            None => None,
            Some((h, r2)) => fin(cmds_rest(dict, window, h, f, r2, end, st, blk0(h.cl), blk0(h.ci), blk0(h.cd), mbp, last)),
        }),
{
    hide(metablocks); hide(read_hdr); hide(cmds_rest); hide(lits_rest); hide(mb_rest); hide(brotli);
}

pub proof fn lemma_cont_cmd(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St, h: Hdr, end: nat, last: bool,
                            mbp: int, bl: Blk, bi: Blk, bd: Blk)
    ensures cont(dict, window, Ph::Cmd { h, end, last, mbp, bl, bi, bd }, f, p, st)
        == fin(cmds_rest(dict, window, h, f, p, end, st, bl, bi, bd, mbp, last)),
{
    hide(metablocks); hide(read_hdr); hide(cmds_rest); hide(lits_rest); hide(mb_rest); hide(brotli);
}

pub proof fn lemma_cont_lits(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St, h: Hdr, end: nat, last: bool,
                             mbp: int, n: nat, bl: Blk, bd: Blk, k: Cmd0)
    ensures cont(dict, window, Ph::Lits { h, end, last, mbp, n, bl, bd, k }, f, p, st)
        == fin(lits_rest(dict, window, h, f, p, n, end, st, bl, bd, k, mbp, last)),
{
    hide(metablocks); hide(read_hdr); hide(cmds_rest); hide(lits_rest); hide(mb_rest); hide(brotli);
}

pub proof fn lemma_cont_fill(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St)
    ensures cont(dict, window, Ph::Fill, f, p, st)
        == (if zero_fill(f, p) { Some((st.out, align8(p) as nat, st.google)) } else { None }),
{
    hide(metablocks); hide(read_hdr); hide(cmds_rest); hide(lits_rest); hide(mb_rest); hide(brotli);
}

pub proof fn lemma_cont_done(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St, bits: nat)
    ensures cont(dict, window, Ph::Done { bits }, f, p, st) == Some((st.out, bits, st.google)),
{
    hide(metablocks); hide(read_hdr); hide(cmds_rest); hide(lits_rest); hide(mb_rest); hide(brotli);
}

pub proof fn lemma_cont_start(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St)
    ensures cont(dict, window, Ph::Start, f, p, st) == brotli(dict, f),
{
    hide(metablocks); hide(read_hdr); hide(cmds_rest); hide(lits_rest); hide(mb_rest); hide(brotli);
}

// --------------------------------------------- after a meta-block header

/// The continuation after a meta-block's header `m` (positions in `f`),
/// the meta-block having started at `p`.
pub open spec fn mb_next(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St, m: Mh) -> Option<(Seq<u8>, nat, bool)> {
    match m {
        Mh::LastEmpty => cont(dict, window, Ph::Fill, f, p + 2, st),
        Mh::Meta { a, n, last } => cont(dict, window, Ph::Skip { q_end: a + 8 * n, last, mbp: p }, f, a, st),
        Mh::Raw { a, mlen } => cont(dict, window, Ph::Raw { q_end: a + 8 * mlen, mbp: p }, f, a, st),
        Mh::Comp { r, mlen, last } => cont(dict, window, Ph::Hdr { end: st.out.len() + mlen, last, mbp: p }, f, r, st),
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_mb_next(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St)
    requires mb_head(f, p) is Some,
    ensures cont(dict, window, Ph::Mb, f, p, st) == mb_next(dict, window, f, p, st, mb_head(f, p).unwrap()),
{
    hide(cont); hide(mb_rest); hide(read_hdr); hide(commands); hide(cmds_rest); hide(metablocks); hide(metablock);
    hide(mb_head);
    lemma_cont_mb(dict, window, f, p, st);
    lemma_metablocks_unfold(dict, window, f, p, st);
    lemma_metablock_head(dict, window, f, p, st);
    let m = mb_head(f, p).unwrap();
    match m {
        Mh::LastEmpty => { lemma_cont_fill(dict, window, f, p + 2, st); reveal(mb_rest); }
        Mh::Meta { a, n, last } => { lemma_cont_skip(dict, window, f, a, st, a + 8 * n, last, p); }
        Mh::Raw { a, mlen } => {
            lemma_cont_raw(dict, window, f, a, st, a + 8 * mlen, p);
            assert(((a + 8 * mlen - a) / 8) as nat == mlen);
        }
        Mh::Comp { r, mlen, last } => {
            lemma_cont_hdr(dict, window, f, r, st, st.out.len() + mlen, last, p);
            reveal(cmds_rest);
        }
    }
}

/// A meta-block with data outputs at least its MLEN bytes more.
#[verifier::spinoff_prover]
pub proof fn lemma_mb_grows(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St)
    requires mb_head(f, p) matches Some(m) && (m is Raw || m is Comp),
    ensures cont(dict, window, Ph::Mb, f, p, st) matches Some((o, q, g)) ==> o.len() >= st.out.len() + match mb_head(f, p).unwrap() {
        Mh::Raw { a, mlen } => mlen, Mh::Comp { r, mlen, last } => mlen, _ => 0nat },
{
    hide(cont); hide(mb_rest); hide(read_hdr); hide(commands); hide(metablocks); hide(metablock); hide(mb_head);
    lemma_cont_mb(dict, window, f, p, st);
    lemma_metablocks_unfold(dict, window, f, p, st);
    lemma_metablock_head(dict, window, f, p, st);
    match mb_head(f, p).unwrap() {
        Mh::Raw { a, mlen } => {
            let s2 = St { out: st.out + bytes_at(f, a, mlen), ring: st.ring, google: st.google };
            lemma_mb_rest_ext(dict, window, f, p, a + 8 * mlen, s2, false);
        }
        Mh::Comp { r, mlen, last } => {
            if let Some((h, r2)) = read_hdr(f, r) {
                crate::dec::lemma_commands_ge(dict, window, h, f, r2, st.out.len() + mlen, st, blk0(h.cl), blk0(h.ci), blk0(h.cd));
                if let Some((st2, r3)) = commands(dict, window, h, f, r2, st.out.len() + mlen, st, blk0(h.cl), blk0(h.ci), blk0(h.cd)) {
                    lemma_mb_rest_ext(dict, window, f, p, r3, st2, last);
                }
            }
        }
        _ => {}
    }
}

/// No header, no meta-block.
pub proof fn lemma_mb_bad(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St)
    requires mb_head(f, p) is None,
    ensures cont(dict, window, Ph::Mb, f, p, st) is None,
{
    hide(cont); hide(mb_rest); hide(read_hdr); hide(commands); hide(metablocks); hide(metablock); hide(mb_head);
    lemma_cont_mb(dict, window, f, p, st);
    lemma_metablocks_unfold(dict, window, f, p, st);
    lemma_metablock_head(dict, window, f, p, st);
}

/// The phase and position after a meta-block's header `m` (positions in
/// the stream), the meta-block having started at `p`.
pub open spec fn mh_ph(m: Mh, p: int, st: St) -> (Ph, int) {
    match m {
        Mh::LastEmpty => (Ph::Fill, p + 2),
        Mh::Meta { a, n, last } => (Ph::Skip { q_end: a + 8 * n, last, mbp: p }, a),
        Mh::Raw { a, mlen } => (Ph::Raw { q_end: a + 8 * mlen, mbp: p }, a),
        Mh::Comp { r, mlen, last } => (Ph::Hdr { end: st.out.len() + mlen, last, mbp: p }, r),
    }
}

pub proof fn lemma_mb_next_ph(dict: Seq<u8>, window: nat, f: Seq<bool>, p: int, st: St, m: Mh)
    ensures mb_next(dict, window, f, p, st, m) == cont(dict, window, mh_ph(m, p, st).0, f, mh_ph(m, p, st).1, st),
{
    hide(cont);
}

/// Bytes split at a byte boundary.
pub proof fn lemma_bytes_split(b: Seq<bool>, q: int, a: nat, c: nat)
    ensures bytes_at(b, q, a + c) == bytes_at(b, q, a) + bytes_at(b, q + 8 * a, c),
{
    assert(bytes_at(b, q, a + c) =~= bytes_at(b, q, a) + bytes_at(b, q + 8 * a, c)) by {
        assert forall|j: int| a <= j < a + c implies
            #[trigger] bytes_at(b, q, a + c)[j] == bytes_at(b, q + 8 * a, c)[j - a] by {
            assert(q + 8 * j == (q + 8 * a) + 8 * (j - a));
        }
    }
}

/// A command's literals, `a` of them then `b`.
pub proof fn lemma_lits_rest_split(dict: Seq<u8>, window: nat, h: Hdr, f: Seq<bool>, p: int, a: nat, b: nat, end: nat,
                                   st: St, bl: Blk, bd: Blk, k: Cmd0, mbp: int, last: bool)
    ensures lits_rest(dict, window, h, f, p, a + b, end, st, bl, bd, k, mbp, last) == (match lits(h, f, p, a, st.out, bl) {
        None => None,
        Some((o, bl2, q)) => lits_rest(dict, window, h, f, q, b, end, St { out: o, ring: st.ring, google: st.google },
                                       bl2, bd, k, mbp, last),
    }),
{
    hide(tail_rest);
    lemma_lits_split(h, f, p, a, b, st.out, bl);
}

/// After a meta-block that ends at `q`: the fill bits, or the next one.
pub proof fn lemma_mb_rest_next(dict: Seq<u8>, window: nat, f: Seq<bool>, mbp: int, q: int, st: St, last: bool)
    requires mbp < q <= f.len(),
    ensures fin(mb_rest(dict, window, f, mbp, q, st, last))
        == (if last { cont(dict, window, Ph::Fill, f, q, st) } else { cont(dict, window, Ph::Mb, f, q, st) }),
{
    hide(cont); hide(metablocks);
    lemma_cont_fill(dict, window, f, q, st);
    lemma_cont_mb(dict, window, f, q, st);
}

/// A command whose literals are done: its tail.
pub proof fn lemma_lits_rest_zero(dict: Seq<u8>, window: nat, h: Hdr, f: Seq<bool>, p: int, end: nat, st: St,
                                  bl: Blk, bd: Blk, k: Cmd0, mbp: int, last: bool)
    ensures lits_rest(dict, window, h, f, p, 0, end, st, bl, bd, k, mbp, last)
        == tail_rest(dict, window, h, f, p, end, st, bl, bd, k, mbp, last),
{
    hide(tail_rest);
    assert(St { out: st.out, ring: st.ring, google: st.google } == st);
}

/// From every phase, the output only grows.
#[verifier::spinoff_prover]
pub proof fn lemma_cont_ext(dict: Seq<u8>, window: nat, ph: Ph, f: Seq<bool>, p: int, st: St)
    requires !(ph is Start) || st.out.len() == 0,
    ensures cont(dict, window, ph, f, p, st) matches Some((o, q, g)) ==> ext(st.out, o),
{
    hide(cont); hide(metablocks); hide(mb_rest); hide(read_hdr); hide(cmds_rest); hide(lits_rest); hide(brotli);
    assert(ext(st.out, st.out)) by { assert(st.out.take(st.out.len() as int) =~= st.out); }
    match ph {
        Ph::Start => {
            lemma_cont_start(dict, window, f, p, st);
            if let Some((o, q, g)) = brotli(dict, f) { assert(o.take(0) =~= Seq::<u8>::empty()); assert(st.out =~= Seq::<u8>::empty()); }
        }
        Ph::Mb => { lemma_cont_mb(dict, window, f, p, st); lemma_metablocks_ext(dict, window, f, p, st); }
        Ph::Skip { q_end, last, mbp } => {
            lemma_cont_skip(dict, window, f, p, st, q_end, last, mbp);
            lemma_mb_rest_ext(dict, window, f, mbp, q_end, st, last);
        }
        Ph::Raw { q_end, mbp } => {
            lemma_cont_raw(dict, window, f, p, st, q_end, mbp);
            let s2 = St { out: st.out + bytes_at(f, p, ((q_end - p) / 8) as nat), ring: st.ring, google: st.google };
            lemma_mb_rest_ext(dict, window, f, mbp, q_end, s2, false);
            lemma_ext_append(st.out, bytes_at(f, p, ((q_end - p) / 8) as nat));
            if let Some((s3, q3)) = mb_rest(dict, window, f, mbp, q_end, s2, false) { lemma_ext_trans(st.out, s2.out, s3.out); }
        }
        Ph::Hdr { end, last, mbp } => {
            lemma_cont_hdr(dict, window, f, p, st, end, last, mbp);
            if let Some((h, r2)) = read_hdr(f, p) {
                lemma_cmds_rest_ext(dict, window, h, f, r2, end, st, blk0(h.cl), blk0(h.ci), blk0(h.cd), mbp, last);
            }
        }
        Ph::Cmd { h, end, last, mbp, bl, bi, bd } => {
            lemma_cont_cmd(dict, window, f, p, st, h, end, last, mbp, bl, bi, bd);
            lemma_cmds_rest_ext(dict, window, h, f, p, end, st, bl, bi, bd, mbp, last);
        }
        Ph::Lits { h, end, last, mbp, n, bl, bd, k } => {
            lemma_cont_lits(dict, window, f, p, st, h, end, last, mbp, n, bl, bd, k);
            lemma_lits_rest_ext(dict, window, h, f, p, n, end, st, bl, bd, k, mbp, last);
        }
        Ph::Fill => { lemma_cont_fill(dict, window, f, p, st); }
        Ph::Done { bits } => { lemma_cont_done(dict, window, f, p, st, bits); }
    }
}

} // verus!
