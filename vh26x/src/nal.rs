//! A NAL unit, whole: its bytes, the RBSP they carry, and the syntax
//! structure the RBSP holds.
//!
//! * `theorem_nal_rt` / `theorem_nal_inv`: a NAL unit is its header and the
//!   escaping of its RBSP, one to one, over the NAL units §7.4.1 allows.
//! * `theorem_rbsp_enc_dec` / `theorem_rbsp_dec_enc`: an RBSP that ends in
//!   `rbsp_trailing_bits( )` holds a syntax structure exactly when it is
//!   that structure's encoding and the trailing bits.
//!
//! With `rt`'s theorems these compose: the bytes of a parameter set NAL
//! unit decode to a trace exactly when they are the header, the escaping,
//! and the trailing bits of that trace's encoding.
use vstd::prelude::*;
use vbits::bitspec::*;
use crate::ir::*;
use crate::sem::*;
use crate::rt::*;
use crate::esc::*;
use crate::rbsp::*;
use crate::bits::*;
use crate::xir::*;
use crate::xdec::*;
use crate::xenc::*;

verus! {

/// The RBSP of NAL unit bytes `n` with an `hl`-byte header.
pub open spec fn nal_rbsp(n: Seq<u8>, hl: nat) -> Option<Seq<u8>> {
    if nal_ok(n) && hl <= n.len() { Some(unesc(n.skip(hl as int))) } else { None }
}

/// The NAL unit with header `h` and RBSP `r`, if §7.4.1 allows it.
pub open spec fn nal_of(h: Seq<u8>, r: Seq<u8>) -> Option<Seq<u8>> {
    let n = h + esc(r, 0);
    if nal_ok(n) { Some(n) } else { None }
}

pub proof fn theorem_nal_rt(h: Seq<u8>, r: Seq<u8>)
    requires nal_of(h, r) is Some,
    ensures
        nal_rbsp(nal_of(h, r).unwrap(), h.len()) == Some(r),
        nal_of(h, r).unwrap().take(h.len() as int) == h,
{
    let n = h + esc(r, 0);
    assert(n.skip(h.len() as int) =~= esc(r, 0));
    assert(n.take(h.len() as int) =~= h);
    theorem_esc_rt(r);
}

pub proof fn theorem_nal_inv(n: Seq<u8>, hl: nat)
    requires nal_rbsp(n, hl) is Some,
    ensures nal_of(n.take(hl as int), nal_rbsp(n, hl).unwrap()) == Some(n),
{
    theorem_esc_inv(n, hl);
    assert(n.take(hl as int) + n.skip(hl as int) =~= n);
}

/// The syntax structure an RBSP holds, when the RBSP ends in trailing bits.
pub open spec fn dec_rbsp(p: Prog, ctx: Ctx, r: Seq<u8>) -> Option<Parsed> {
    match sodb_len(r) {
        Some(k) => dec_all(p, ctx, bits_of(r).take(k as int)),
        None => None,
    }
}

pub proof fn theorem_rbsp_enc_dec(p: Prog, ctx: Ctx, tr: Seq<int>, r: Seq<u8>)
    requires
        enc_all(p, ctx, tr) is Some,
        bits_of(r) =~= rbsp_of(enc_all(p, ctx, tr).unwrap().0),
    ensures dec_rbsp(p, ctx, r) == Some(enc_all(p, ctx, tr).unwrap().1),
{
    let c = enc_all(p, ctx, tr).unwrap().0;
    theorem_rbsp_rt(c, r);
    assert(bits_of(r).take(c.len() as int) =~= c);
    theorem_enc_dec(p, ctx, tr, canon_ch(tr.len()));
}

/// For a program with no choices (every H.264 and H.265 table: no
/// descriptor of theirs has two codes for a value), the decoded trace's
/// canonical encoding is the RBSP, bit for bit.
pub proof fn theorem_rbsp_dec_enc(p: Prog, ctx: Ctx, r: Seq<u8>)
    requires prog_rigid(p), dec_rbsp(p, ctx, r) is Some,
    ensures ({
        let pr = dec_rbsp(p, ctx, r).unwrap();
        &&& enc_all(p, ctx, pr.trace) is Some
        &&& enc_all(p, ctx, pr.trace).unwrap().1 == pr
        &&& bits_of(r) =~= rbsp_of(enc_all(p, ctx, pr.trace).unwrap().0)
    }),
{
    let k = sodb_len(r).unwrap();
    theorem_rbsp_inv(r);
    theorem_rigid(p, ctx, bits_of(r).take(k as int));
}

// ------------------------------------------------------------------- exec

pub fn decode_nal_x(n: &[u8], hl: usize) -> (res: Option<Vec<u8>>)
    ensures
        match nal_rbsp(n@, hl as nat) {
            Some(r) => res is Some && res.unwrap()@ == r,
            None => res is None,
        },
{
    if hl > n.len() || !nal_ok_x(n) {
        return None;
    }
    Some(unescape_x(n, hl))
}

pub fn encode_nal_x(h: &[u8], r: &[u8]) -> (res: Option<Vec<u8>>)
    ensures
        match nal_of(h@, r@) {
            Some(n) => res is Some && res.unwrap()@ == n,
            None => res is None,
        },
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < h.len()
        invariant i <= h@.len(), out@ =~= h@.take(i as int),
        decreases h@.len() - i,
    {
        out.push(h[i]);
        proof { assert(h@.take(i as int + 1) =~= h@.take(i as int).push(h@[i as int])); }
        i = i + 1;
    }
    proof { assert(h@.take(h@.len() as int) =~= h@); }
    escape_x(r, &mut out);
    if nal_ok_x(&out) { Some(out) } else { None }
}

/// Decode the syntax structure an RBSP holds.
pub fn decode_rbsp_x(p: &ProgX, ctx: &Vec<Vec<i64>>, r: &[u8]) -> (res: Option<ParsedX>)
    requires 8 * r@.len() <= usize::MAX,
    ensures
        match dec_rbsp(p@, cview(ctx@), r@) {
            Some(pr) => res is Some && pview(res.unwrap()) == pr,
            None => res is None,
        },
{
    match sodb_len_x(r) {
        Some(k) => {
            proof { theorem_rbsp_inv(r@); }
            decode_all(p, ctx, r, k)
        }
        None => None,
    }
}

/// Encode a trace as an RBSP: the structure's bits, then trailing bits.
pub fn encode_rbsp_x(p: &ProgX, ctx: &Vec<Vec<i64>>, tr: &Vec<i64>) -> (res: Option<(Vec<u8>, ParsedX)>)
    ensures
        res is Some ==> ({
            let (r, px) = res.unwrap();
            &&& enc_all(p@, cview(ctx@), iview(tr@)) is Some
            &&& enc_all(p@, cview(ctx@), iview(tr@)).unwrap().1 == pview(px)
            &&& bits_of(r@) =~= rbsp_of(enc_all(p@, cview(ctx@), iview(tr@)).unwrap().0)
        }),
{
    let (mut w, px) = match encode_all(p, ctx, tr) {
        Some(x) => x,
        None => { return None; }
    };
    let ghost c = w.written();
    if !w.write_align() {
        return None;
    }
    proof {
        let a = align_code(c.len());
        assert((c.len() + a.len()) % 8 == 0);
        assert(w.pos == c.len() + a.len());
        assert(8 * w.buf@.len() == w.pos) by (nonlinear_arith)
            requires w.pos <= 8 * w.buf@.len(), 8 * w.buf@.len() < w.pos + 8, w.pos % 8 == 0;
        assert(bits_of(w.buf@).take(w.pos as int) =~= bits_of(w.buf@));
    }
    Some((w.buf, px))
}

} // verus!
