//! The stream (RFC 7932 9.1, 9.2): WBITS, meta-blocks (metadata,
//! uncompressed, compressed) and the whole stream, proved to compute
//! `spec::brotli`.
//!
//! A decode ends in one of three ways. `Ok` is exactly the spec's result.
//! `Err(Bad)` means the spec has no result: the input is not a Brotli
//! stream. `Err(TooBig)` means the output would pass the caller's limit: the
//! spec has no result or one longer than the limit. The limit is checked
//! before each meta-block, against its MLEN, so the output buffer never
//! grows past it.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
use vbits::lsb::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::getbits;
use crate::spec::*;
use crate::code::*;
use crate::hdr::*;
use crate::cmd::*;

verus! {

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Error {
    /// Not a Brotli stream.
    Bad,
    /// The output would be longer than the limit.
    TooBig,
}

// ------------------------------------------------------ output only grows

pub proof fn lemma_commands_ge(dict: Seq<u8>, window: nat, h: Hdr, b: Seq<bool>, p: int, end: nat, st: St,
                           bl: Blk, bi: Blk, bd: Blk)
    ensures commands(dict, window, h, b, p, end, st, bl, bi, bd) matches Some((st2, _)) ==> st2.out.len() >= end,
    decreases end - st.out.len(), b.len() - p, bi.left,
{
    if let Some(Step::Next(st2, bl2, bi2, bd2, q)) = cmd_step(dict, window, h, b, p, end, st, bl, bi, bd) {
        if (st2.out.len() > st.out.len())
            || (st2.out.len() == st.out.len() && p < q <= b.len())
            || (st2.out.len() == st.out.len() && q == p && bi2.left < bi.left) {
            lemma_commands_ge(dict, window, h, b, q, end, st2, bl2, bi2, bd2);
        }
    }
}

/// A meta-block with data outputs at least its MLEN bytes.
pub proof fn lemma_data_ge(dict: Seq<u8>, window: nat, b: Seq<bool>, p: int, st: St, mlen: nat, last: bool)
    ensures data(dict, window, b, p, st, mlen, last) matches Some((st2, _, _)) ==> st2.out.len() >= st.out.len() + mlen,
{
    let r = if last { p } else { p + 1 };
    match read_hdr(b, r) {
        None => {}
        Some((h, r2)) => {
            lemma_commands_ge(dict, window, h, b, r2, st.out.len() + mlen, st, blk0(h.cl), blk0(h.ci), blk0(h.cd));
        }
    }
}

pub proof fn lemma_metablock_ge(dict: Seq<u8>, window: nat, b: Seq<bool>, p: int, st: St)
    ensures metablock(dict, window, b, p, st) matches Some((st2, _, _)) ==> st2.out.len() >= st.out.len(),
{
    if let Some(islast) = getbits(b, p, 1) {
        let q = if islast == 1 { p + 2 } else { p + 1 };
        if let Some(m) = getbits(b, q, 2) {
            if m != 3 {
                if let Some(v) = getbits(b, q + 2, 4 * (m + 4)) {
                    lemma_data_ge(dict, window, b, q + 2 + 4 * (m + 4), st, v + 1, islast == 1);
                }
            }
        }
    }
}

pub proof fn lemma_metablocks_ge(dict: Seq<u8>, window: nat, b: Seq<bool>, p: int, st: St)
    ensures metablocks(dict, window, b, p, st) matches Some((st2, _)) ==> st2.out.len() >= st.out.len(),
    decreases b.len() - p,
{
    lemma_metablock_ge(dict, window, b, p, st);
    match metablock(dict, window, b, p, st) {
        None => {}
        Some((st2, q, last)) => {
            if !last && !(q <= p || q > b.len()) {
                lemma_metablocks_ge(dict, window, b, q, st2);
            }
        }
    }
}

// ----------------------------------------------------------- meta-blocks

/// A metadata meta-block from its reserved bit: the position after it.
pub fn metadata_x(buf: &[u8], p: usize, Ghost(st): Ghost<St>, last: bool) -> (r: Option<usize>)
    requires buf_ok(buf@), p <= 8 * buf.len(),
    ensures
        match r {
            Some(q) => metadata(lbits(buf@), p as int, st, last) == Some((st, q as int, last)) && q <= 8 * buf.len(),
            None => metadata(lbits(buf@), p as int, st, last) is None,
        },
{
    let reserved = match getbits_x(buf, p, 1) { None => return None, Some(x) => x };
    let nbytes = match getbits_x(buf, p + 1, 2) { None => return None, Some(x) => x };
    proof { reveal_with_fuel(p2, 3); }
    let n: u64 = if nbytes == 0 {
        0
    } else {
        let v = match getbits_x(buf, p + 3, 8 * nbytes) { None => return None, Some(x) => x };
        proof {
            vbits::prim_read::lemma_p2_eq_pow2((8 * (nbytes - 1)) as nat);
            vstd::bits::lemma_u64_pow2_no_overflow((8 * (nbytes - 1)) as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, (8 * (nbytes - 1)) as u64);
            vbits::prim_read::lemma_p2_mono((8 * nbytes) as nat, 24);
            assert(p2(24) == 0x100_0000) by { reveal_with_fuel(p2, 25); }
        }
        if nbytes > 1 && v / (1u64 << (8 * (nbytes - 1))) == 0 {
            return None;
        }
        v + 1
    };
    let r = p + 3 + 8 * nbytes as usize;
    if reserved != 0 || r > 8 * buf.len() || !zero_fill_x(buf, r) {
        return None;
    }
    let a = align8_x(r);
    if n as usize > (8 * buf.len() - a) / 8 {
        return None;
    }
    Some(a + 8 * n as usize)
}

/// The state of the stream as the spec's `St`.
pub open spec fn st_of(out: Seq<u8>, ring: [u64; 4], google: bool) -> St {
    St { out, ring: rseq(ring), google }
}

/// A meta-block with data, from just after MLEN, written after
/// `out@.take(n)`, which then ends at `n + mlen`.
#[verifier::spinoff_prover]
fn data_x(dict: &[u8], window: u64, buf: &[u8], p: usize, out: &mut Vec<u8>, n: usize, ring: [u64; 4], google: bool,
          mlen: u64, last: bool) -> (r: Option<(usize, [u64; 4], bool)>)
    requires
        dict_ok(dict@), window < 0x100_0000, buf_ok(buf@), p <= 8 * buf.len(), ring_ok(ring),
        1 <= mlen <= 0x100_0000, n <= old(out)@.len(), n + mlen < 0x0800_0000_0000_0000,
    ensures
        final(out)@.len() >= n + mlen,
        match r {
            Some((q, ring2, g2)) => data(dict@, window as nat, lbits(buf@), p as int,
                                         st_of(old(out)@.take(n as int), ring, google), mlen as nat, last)
                    == Some((st_of(final(out)@.take(n + mlen), ring2, g2), q as int, last))
                && ring_ok(ring2) && q <= 8 * buf.len(),
            None => data(dict@, window as nat, lbits(buf@), p as int, st_of(old(out)@.take(n as int), ring, google),
                         mlen as nat, last) is None,
        },
{
    hide(read_hdr);
    hide(commands);
    let end = n + mlen as usize;
    if out.len() == 0 {
        // a first buffer from the allocator's zeroed memory (fresh pages are
        // not filled again)
        *out = vec![0u8; end + 16];
        proof { assert(out@.take(n as int) =~= old(out)@.take(n as int)); }
    } else {
        vdeflate::inflate::grow(out, n, end + 16);
    }
    let u = if last { 0 } else { match getbits_x(buf, p, 1) { None => return None, Some(x) => x } };
    let r = if last { p } else { p + 1 };
    if u == 1 {
        if !zero_fill_x(buf, r) {
            return None;
        }
        let a = align8_x(r);
        if mlen as usize > (8 * buf.len() - a) / 8 {
            return None;
        }
        bytes_at_x(buf, a, mlen as usize, out, n);
        return Some((a + 8 * mlen as usize, ring, google));
    }
    let (h, r2) = match read_hdr_x(buf, r) { None => return None, Some(x) => x };
    let ghost sh = read_hdr(lbits(buf@), r as int).unwrap().0;
    let bl = blk0_x(&h.cl, Ghost(sh.cl));
    let bi = blk0_x(&h.ci, Ghost(sh.ci));
    let bd = blk0_x(&h.cd, Ghost(sh.cd));
    let r = commands_x(dict, window, &h, Ghost(sh), buf, r2, end, out, n, ring, google, bl, bi, bd,
                       Ghost(Seq::empty()), 0);
    proof {
        assert(ov(Seq::empty(), old(out)@, n as int) =~= old(out)@.take(n as int));
        assert(ov(Seq::empty(), out@, end as int) =~= out@.take(end as int));
    }
    r
}

/// MLEN - 1 in `nib` nibbles (4..6), with the check of 9.2 on its last.
pub fn read_mlen_x(buf: &[u8], pos: usize, nib: u64) -> (r: Option<u64>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), 4 <= nib <= 6,
    ensures
        match r {
            Some(mlen) => getbits(lbits(buf@), pos as int, 4 * nib as nat) == Some((mlen - 1) as nat)
                && !(nib > 4 && (mlen - 1) as nat / p2(4 * (nib - 1) as nat) == 0)
                && 1 <= mlen <= 0x100_0000 && pos + 4 * nib <= 8 * buf.len(),
            None => match getbits(lbits(buf@), pos as int, 4 * nib as nat) {
                None => true,
                Some(v) => nib > 4 && v / p2(4 * (nib - 1) as nat) == 0,
            },
        },
{
    let v = match getbits_x(buf, pos, 4 * nib) { None => return None, Some(x) => x };
    proof {
        vbits::prim_read::lemma_p2_eq_pow2((4 * (nib - 1)) as nat);
        vstd::bits::lemma_u64_pow2_no_overflow((4 * (nib - 1)) as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, (4 * (nib - 1)) as u64);
        vbits::prim_read::lemma_p2_mono((4 * nib) as nat, 24);
        assert(p2(24) == 0x100_0000) by { reveal_with_fuel(p2, 25); }
    }
    if nib > 4 && v / (1u64 << (4 * (nib - 1))) == 0 {
        return None;
    }
    Some(v + 1)
}

/// One meta-block, after the output `out@.take(n)`: the position after
/// it, the ring, the flag, whether it is the last, and the output's length.
#[verifier::spinoff_prover]
fn metablock_x(dict: &[u8], window: u64, buf: &[u8], p: usize, out: &mut Vec<u8>, n: usize, ring: [u64; 4],
               google: bool, max_out: usize) -> (r: Result<(usize, [u64; 4], bool, bool, usize), Error>)
    requires
        dict_ok(dict@), window < 0x100_0000, buf_ok(buf@), p <= 8 * buf.len(), ring_ok(ring),
        n <= old(out)@.len(), n <= max_out, max_out < 0x0800_0000_0000_0000,
    ensures
        match r {
            Ok((q, ring2, g2, last, n2)) => metablock(dict@, window as nat, lbits(buf@), p as int,
                                                      st_of(old(out)@.take(n as int), ring, google))
                    == Some((st_of(final(out)@.take(n2 as int), ring2, g2), q as int, last))
                && ring_ok(ring2) && q <= 8 * buf.len() && n2 <= max_out && n2 <= final(out)@.len(),
            Err(Error::Bad) => metablock(dict@, window as nat, lbits(buf@), p as int,
                                         st_of(old(out)@.take(n as int), ring, google)) is None,
            Err(Error::TooBig) => metablock(dict@, window as nat, lbits(buf@), p as int,
                                            st_of(old(out)@.take(n as int), ring, google))
                matches Some((st2, _, _)) ==> st2.out.len() > max_out,
        },
{
    hide(data);
    hide(metadata);
    let ghost st = st_of(out@.take(n as int), ring, google);
    let islast = match getbits_x(buf, p, 1) { None => return Err(Error::Bad), Some(x) => x };
    let e = if islast == 1 { match getbits_x(buf, p + 1, 1) { None => return Err(Error::Bad), Some(x) => x } } else { 0 };
    if e == 1 {
        return Ok((p + 2, ring, google, true, n));
    }
    let q = if islast == 1 { p + 2 } else { p + 1 };
    let m = match getbits_x(buf, q, 2) { None => return Err(Error::Bad), Some(x) => x };
    proof { reveal_with_fuel(p2, 3); }
    if m == 3 {
        return match metadata_x(buf, q + 2, Ghost(st), islast == 1) {
            None => Err(Error::Bad),
            Some(q2) => Ok((q2, ring, google, islast == 1, n)),
        };
    }
    let nib = m + 4;
    let mlen = match read_mlen_x(buf, q + 2, nib) { None => return Err(Error::Bad), Some(x) => x };
    let q2 = q + 2 + 4 * nib as usize;
    proof { assert(metablock(dict@, window as nat, lbits(buf@), p as int, st)
                   == data(dict@, window as nat, lbits(buf@), q2 as int, st, mlen as nat, islast == 1)); }
    if mlen as usize > max_out - n {
        proof { lemma_data_ge(dict@, window as nat, lbits(buf@), q2 as int, st, mlen as nat, islast == 1); }
        return Err(Error::TooBig);
    }
    match data_x(dict, window, buf, q2, out, n, ring, google, mlen, islast == 1) {
        None => Err(Error::Bad),
        Some((q3, ring2, g2)) => Ok((q3, ring2, g2, islast == 1, n + mlen as usize)),
    }
}

/// The meta-blocks from `p` to the last, and the fill bits after it: the
/// position after the stream, the flag, and the output's length.
fn metablocks_x(dict: &[u8], window: u64, buf: &[u8], pos: usize, out: &mut Vec<u8>, ring0: [u64; 4], google0: bool,
                max_out: usize) -> (r: Result<(usize, bool, usize), Error>)
    requires
        dict_ok(dict@), window < 0x100_0000, buf_ok(buf@), pos <= 8 * buf.len(), ring_ok(ring0),
        max_out < 0x0800_0000_0000_0000,
    ensures
        match r {
            Ok((q, g2, n2)) => metablocks(dict@, window as nat, lbits(buf@), pos as int, st_of(Seq::empty(), ring0, google0))
                    matches Some((st2, q2)) && q2 == q as int && st2.out == final(out)@.take(n2 as int)
                    && st2.google == g2 && n2 <= final(out)@.len(),
            Err(Error::Bad) => metablocks(dict@, window as nat, lbits(buf@), pos as int, st_of(Seq::empty(), ring0, google0)) is None,
            Err(Error::TooBig) => metablocks(dict@, window as nat, lbits(buf@), pos as int, st_of(Seq::empty(), ring0, google0))
                matches Some((st2, _)) ==> st2.out.len() > max_out,
        },
{
    hide(metablock);
    let ghost b = lbits(buf@);
    let ghost target = metablocks(dict@, window as nat, b, pos as int, st_of(Seq::empty(), ring0, google0));
    let mut p = pos;
    let mut n: usize = 0;
    let mut ring = ring0;
    let mut google = google0;
    proof { assert(out@.take(0) =~= Seq::<u8>::empty()); }
    loop
        invariant
            dict_ok(dict@), window < 0x100_0000, buf_ok(buf@), p <= 8 * buf.len(), ring_ok(ring), b == lbits(buf@),
            n <= out@.len(), n <= max_out, max_out < 0x0800_0000_0000_0000,
            metablocks(dict@, window as nat, b, p as int, st_of(out@.take(n as int), ring, google)) == target,
            target == metablocks(dict@, window as nat, lbits(buf@), pos as int, st_of(Seq::empty(), ring0, google0)),
        decreases 8 * buf.len() - p,
    {
        let ghost st = st_of(out@.take(n as int), ring, google);
        match metablock_x(dict, window, buf, p, out, n, ring, google, max_out) {
            Err(Error::Bad) => return Err(Error::Bad),
            Err(Error::TooBig) => {
                proof {
                    if let Some((st2, q, last)) = metablock(dict@, window as nat, b, p as int, st) {
                        if !last && !(q <= p || q > b.len()) {
                            lemma_metablocks_ge(dict@, window as nat, b, q, st2);
                        }
                    }
                }
                return Err(Error::TooBig);
            }
            Ok((q, ring2, g2, last, n2)) => {
                if last {
                    if zero_fill_x(buf, q) {
                        return Ok((align8_x(q), g2, n2));
                    }
                    return Err(Error::Bad);
                }
                if q <= p {
                    return Err(Error::Bad);
                }
                p = q;
                n = n2;
                ring = ring2;
                google = g2;
            }
        }
    }
}

pub fn wbits_x(buf: &[u8]) -> (r: Option<(u64, usize)>)
    requires buf_ok(buf@),
    ensures
        match r {
            Some((w, p)) => wbits(lbits(buf@)) == Some((w as nat, p as int)) && 10 <= w <= 24 && p <= 8 * buf.len(),
            None => wbits(lbits(buf@)) is None,
        },
{
    let x = match getbits_x(buf, 0, 1) { None => return None, Some(x) => x };
    if x == 0 {
        return Some((16, 1));
    }
    let n = match getbits_x(buf, 1, 3) { None => return None, Some(x) => x };
    proof { reveal_with_fuel(p2, 4); }
    if n != 0 {
        return Some((17 + n, 4));
    }
    let m = match getbits_x(buf, 4, 3) { None => return None, Some(x) => x };
    if m == 1 { None } else if m != 0 { Some((8 + m, 7)) } else { Some((17, 7)) }
}

/// The window of WBITS `w` (9.1).
pub fn window_x(w: u64) -> (r: u64)
    requires 10 <= w <= 24,
    ensures r as nat == (p2(w as nat) - 16) as nat, r < 0x100_0000,
{
    proof {
        vbits::prim_read::lemma_p2_eq_pow2(w as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(w as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, w);
        vbits::prim_read::lemma_p2_mono(w as nat, 24);
        assert(p2(24) == 0x100_0000 && p2(10) == 1024) by { reveal_with_fuel(p2, 25); }
        vbits::prim_read::lemma_p2_mono(10, w as nat);
    }
    (1u64 << w) - 16
}

/// Decode a Brotli stream with the static dictionary `dict` into `out`,
/// producing at most `max_out` bytes: the data is `out[..n]`; also the bits
/// the stream took (a whole number of bytes), and whether Google's decoder
/// accepts it. `out` keeps its length if that is more than `n` (room for
/// the next stream: it is not zeroed or allocated again).
pub fn brotli_into(dict: &[u8], buf: &[u8], max_out: usize, out: &mut Vec<u8>) -> (r: Result<(usize, usize, bool), Error>)
    requires dict_ok(dict@), buf_ok(buf@), max_out < 0x0800_0000_0000_0000,
    ensures
        match r {
            Ok((n, bits, g)) => brotli(dict@, lbits(buf@)) == Some((final(out)@.take(n as int), bits as nat, g))
                && n <= final(out)@.len(),
            Err(Error::Bad) => brotli(dict@, lbits(buf@)) is None,
            Err(Error::TooBig) => brotli(dict@, lbits(buf@)) matches Some((o, _, _)) ==> o.len() > max_out,
        },
{
    hide(metablocks);
    let (w, p) = match wbits_x(buf) { None => return Err(Error::Bad), Some(x) => x };
    let window = window_x(w);
    let ring: [u64; 4] = [4, 11, 15, 16];
    proof {
        assert(rseq(ring) =~= seq![4int, 11, 15, 16]);
        assert(st_of(Seq::empty(), ring, true) == St { out: Seq::empty(), ring: seq![4int, 11, 15, 16], google: true });
    }
    match metablocks_x(dict, window, buf, p, out, ring, true, max_out) {
        Err(e) => Err(e),
        Ok((q, g, n)) => Ok((n, q, g)),
    }
}

/// Decode a Brotli stream with the static dictionary `dict`, producing at
/// most `max_out` bytes: the data, the bits the stream took (a whole number
/// of bytes), and whether Google's decoder accepts it.
pub fn brotli_x(dict: &[u8], buf: &[u8], max_out: usize) -> (r: Result<(Vec<u8>, usize, bool), Error>)
    requires dict_ok(dict@), buf_ok(buf@), max_out < 0x0800_0000_0000_0000,
    ensures
        match r {
            Ok((o, bits, g)) => brotli(dict@, lbits(buf@)) == Some((o@, bits as nat, g)),
            Err(Error::Bad) => brotli(dict@, lbits(buf@)) is None,
            Err(Error::TooBig) => brotli(dict@, lbits(buf@)) matches Some((o, _, _)) ==> o.len() > max_out,
        },
{
    let mut out: Vec<u8> = Vec::new();
    match brotli_into(dict, buf, max_out, &mut out) {
        Err(e) => Err(e),
        Ok((n, q, g)) => {
            out.truncate(n);
            proof { assert(out@ =~= out@.take(n as int)); }
            Ok((out, q, g))
        }
    }
}

} // verus!
