//! Decoding depends only on the bits it reads: a stream that has the same
//! bits as another up to where the other's decoding ends decodes the same.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::spec::*;
use crate::step::*;
#[cfg(verus_keep_ghost)]
use crate::inflate::lemma_syms_pos;

verus! {

pub proof fn lemma_syms_agree(ll: Seq<u8>, dl: Seq<u8>, b1: Seq<bool>, b2: Seq<bool>, p: int, out: Seq<u8>)
    requires 0 <= p, inflate_syms(ll, dl, b2, p, out) is Some, agree(b1, b2, p, inflate_syms(ll, dl, b2, p, out).unwrap().1),
    ensures inflate_syms(ll, dl, b1, p, out) == inflate_syms(ll, dl, b2, p, out),
    decreases b2.len() - p,
{
    let q = inflate_syms(ll, dl, b2, p, out).unwrap().1;
    lemma_syms_unfold(ll, dl, b1, p, out);
    lemma_syms_unfold(ll, dl, b2, p, out);
    let stp = sym_step(ll, dl, b2, p).unwrap();
    let e = step_end(stp);
    match stp {
        Step::Lit(x, p1) => { lemma_syms_pos(ll, dl, b2, p1, out.push(x)); }
        Step::End(p1) => {}
        Step::Copy(len, d, p4) => { lemma_syms_pos(ll, dl, b2, p4, lz_copy(out, d, len)); }
    }
    lemma_agree_sub(b1, b2, p, q, p, e);
    lemma_sym_step_agree(ll, dl, b1, b2, p);
    match stp {
        Step::Lit(x, p1) => {
            lemma_agree_sub(b1, b2, p, q, p1, q);
            lemma_syms_agree(ll, dl, b1, b2, p1, out.push(x));
        }
        Step::End(p1) => {}
        Step::Copy(len, d, p4) => {
            if d <= out.len() {
                lemma_agree_sub(b1, b2, p, q, p4, q);
                lemma_syms_agree(ll, dl, b1, b2, p4, lz_copy(out, d, len));
            }
        }
    }
}

pub proof fn lemma_block_pos(b: Seq<bool>, p: int, btype: nat, out: Seq<u8>)
    requires 0 <= p, block(b, p, btype, out) is Some,
    ensures p < block(b, p, btype, out).unwrap().1 <= b.len(),
{
    if btype == 0 {
        lemma_stored_unfold(b, p);
        lemma_stored_hdr_bound(b, p);
    } else if btype == 1 {
        lemma_syms_pos(fixed_lit(), fixed_dist(), b, p, out);
    } else {
        let (lit, dist, qh, strict) = dyn_header(b, p).unwrap();
        lemma_dyn_header_pos(b, p);
        lemma_syms_pos(lit, dist, b, qh, out);
    }
}

pub proof fn lemma_block_agree(b1: Seq<bool>, b2: Seq<bool>, p: int, btype: nat, out: Seq<u8>)
    requires 0 <= p, block(b2, p, btype, out) is Some, agree(b1, b2, p, block(b2, p, btype, out).unwrap().1),
    ensures block(b1, p, btype, out) == block(b2, p, btype, out),
{
    let q = block(b2, p, btype, out).unwrap().1;
    if btype == 0 {
        lemma_stored_unfold(b1, p);
        lemma_stored_unfold(b2, p);
        let (len, q0) = stored_hdr(b2, p).unwrap();
        lemma_stored_hdr_bound(b2, p);
        lemma_agree_sub(b1, b2, p, q, p, q0);
        lemma_stored_hdr_agree(b1, b2, p);
        lemma_agree_sub(b1, b2, p, q, q0, q);
        lemma_bytes_agree(b1, b2, q0, len);
    } else if btype == 1 {
        lemma_syms_agree(fixed_lit(), fixed_dist(), b1, b2, p, out);
    } else {
        let (lit, dist, qh, strict) = dyn_header(b2, p).unwrap();
        lemma_dyn_header_pos(b2, p);
        lemma_syms_pos(lit, dist, b2, qh, out);
        lemma_agree_sub(b1, b2, p, q, p, qh);
        lemma_dyn_header_agree(b1, b2, p);
        lemma_agree_sub(b1, b2, p, q, qh, q);
        lemma_syms_agree(lit, dist, b1, b2, qh, out);
    }
}

pub proof fn lemma_blocks_pos(b: Seq<bool>, p: int, out: Seq<u8>, st: bool)
    requires 0 <= p, inflate_blocks(b, p, out, st) is Some,
    ensures p < inflate_blocks(b, p, out, st).unwrap().1 <= b.len(),
    decreases b.len() - p,
{
    let bfinal = getbits(b, p, 1).unwrap();
    let btype = getbits(b, p + 1, 2).unwrap();
    let (o, qb, s) = block(b, p + 3, btype, out).unwrap();
    lemma_block_pos(b, p + 3, btype, out);
    if bfinal != 1 { lemma_blocks_pos(b, qb, o, st && s); }
}

pub proof fn lemma_blocks_agree(b1: Seq<bool>, b2: Seq<bool>, p: int, out: Seq<u8>, st: bool)
    requires 0 <= p, inflate_blocks(b2, p, out, st) is Some, agree(b1, b2, p, inflate_blocks(b2, p, out, st).unwrap().1),
    ensures inflate_blocks(b1, p, out, st) == inflate_blocks(b2, p, out, st),
    decreases b2.len() - p,
{
    let qf = inflate_blocks(b2, p, out, st).unwrap().1;
    let bfinal = getbits(b2, p, 1).unwrap();
    let btype = getbits(b2, p + 1, 2).unwrap();
    let (o, qb, s) = block(b2, p + 3, btype, out).unwrap();
    lemma_block_pos(b2, p + 3, btype, out);
    if bfinal != 1 { lemma_blocks_pos(b2, qb, o, st && s); }
    lemma_agree_sub(b1, b2, p, qf, p, p + 1);
    lemma_getbits_agree(b1, b2, p, 1);
    lemma_agree_sub(b1, b2, p, qf, p + 1, p + 3);
    lemma_getbits_agree(b1, b2, p + 1, 2);
    lemma_agree_sub(b1, b2, p, qf, p + 3, qb);
    lemma_block_agree(b1, b2, p + 3, btype, out);
    if bfinal != 1 {
        lemma_agree_sub(b1, b2, p, qf, qb, qf);
        lemma_blocks_agree(b1, b2, qb, o, st && s);
    }
}

// ------------------------------------------------ DEFLATE as a format

/// The relation of the format model (`vexi/src/format.rs`): the bits `c` are,
/// exactly, a DEFLATE stream of `a`.
pub open spec fn deflate_rel(a: Seq<u8>, c: Seq<bool>) -> bool {
    inflate(c) matches Some((o, q, _)) && o == a && q == c.len()
}

/// Decoder soundness: what `inflate` returns, the bits it consumed are a
/// stream of.
pub proof fn lemma_inflate_sound(b: Seq<bool>)
    requires inflate(b) is Some,
    ensures ({
        let (a, q, _) = inflate(b).unwrap();
        q <= b.len() && deflate_rel(a, b.take(q as int))
    }),
{
    let (a, q, st) = inflate(b).unwrap();
    lemma_blocks_pos(b, 0, Seq::empty(), true);
    let c = b.take(q as int);
    assert(agree(c, b, 0, q as int));
    lemma_blocks_agree(c, b, 0, Seq::empty(), true);
}

/// Decoder completeness: a stream decodes, to what it is a stream of,
/// whatever follows it.
pub proof fn lemma_inflate_complete(a: Seq<u8>, c: Seq<bool>, b: Seq<bool>)
    requires deflate_rel(a, c), is_prefix(c, b),
    ensures inflate(b) matches Some((o, q, _)) && o == a && q == c.len(),
{
    lemma_blocks_pos(c, 0, Seq::empty(), true);
    assert(inflate_blocks(c, 0, Seq::empty(), true).unwrap().1 == c.len());
    lemma_prefix_agree(c, b, 0, c.len() as int);
    lemma_blocks_agree(b, c, 0, Seq::empty(), true);
}

} // verus!
