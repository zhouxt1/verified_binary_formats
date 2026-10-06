//! RFC 1951 (DEFLATE), as a spec decoder over the stream's bits.
//!
//! The stream is `lbits(input)`: bytes LSB-first (3.1.1). Positions are bit
//! offsets from the start of the stream, so a stored block's byte alignment
//! is `p` rounded up to a multiple of 8.
//!
//! `inflate(b)` is the output, the number of bits the stream took (the rest
//! is not DEFLATE's), and whether the stream is also one zlib 1.3 accepts.
//! The decoder is RFC 1951's, read as leniently as the RFC allows; where zlib
//! is stricter, the stream decodes the same and the flag is false:
//!
//! * an incomplete Huffman code (a code whose lengths leave some bit strings
//!   unassigned). The RFC does not forbid one; zlib refuses any but a
//!   lit/length or distance code with a single code of length 1.
//! * more than 30 distance codes (HDIST > 29). The RFC's HDIST range is 1 to
//!   32; zlib refuses 31 and 32.
//!
//! Refused by both, so by this spec:
//!
//! * an over-subscribed code (lengths that no prefix code has);
//! * HLIT > 29, i.e. more than 286 lit/length codes (the RFC's range is 257
//!   to 286);
//! * lit/length symbols 286 and 287, distance symbols 30 and 31 ("will never
//!   actually occur");
//! * a distance back past the first byte of output (no preset dictionary);
//! * a dynamic block whose end-of-block code has no length, or a repeat code
//!   16 with nothing to repeat, or a run of lengths past HLIT + HDIST;
//! * a stored block with NLEN not the complement of LEN; block type 3.
//!
//! Bits after the final block, and the padding bits before a stored block's
//! LEN, are not looked at, as in the RFC and zlib.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::{bits_val, p2};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::lsb::lval;

verus! {

// ------------------------------------------------------------ bit fields

/// `n` bits at `p`, the first the least significant (3.1.1, data elements
/// other than Huffman codes).
pub open spec fn getbits(b: Seq<bool>, p: int, n: nat) -> Option<nat> {
    if 0 <= p && p + n <= b.len() { Some(lval(b.subrange(p, p + n))) } else { None }
}

/// `l` bits at `p` read as a Huffman code: the first is the code's most
/// significant (3.1.1, "starting with the most-significant bit of the code").
pub open spec fn codebits(b: Seq<bool>, p: int, l: nat) -> nat {
    bits_val(b.subrange(p, p + l))
}

// ------------------------------------------------- canonical Huffman codes

/// The longest code DEFLATE uses.
pub open spec fn maxbits() -> nat { 15 }

/// How many of the first `upto` symbols have code length `l`.
pub open spec fn count_len(lens: Seq<u8>, l: nat, upto: int) -> nat
    decreases upto,
{
    if upto <= 0 {
        0
    } else {
        count_len(lens, l, upto - 1) + (if lens[upto - 1] as nat == l { 1nat } else { 0nat })
    }
}

/// `bl_count[l]` of 3.2.2 step 1 (for l >= 1).
pub open spec fn bl_count(lens: Seq<u8>, l: nat) -> nat {
    count_len(lens, l, lens.len() as int)
}

/// `next_code[l]` of 3.2.2 step 2: `code = (code + bl_count[bits-1]) << 1`,
/// with `bl_count[0] = 0`.
pub open spec fn next_code(lens: Seq<u8>, l: nat) -> nat
    decreases l,
{
    if l <= 1 { 0 } else { 2 * (next_code(lens, (l - 1) as nat) + bl_count(lens, (l - 1) as nat)) }
}

/// The code of symbol `n` (3.2.2 step 3): codes of one length are assigned
/// consecutively in symbol order, from `next_code` of that length.
pub open spec fn code_of(lens: Seq<u8>, n: int) -> nat {
    next_code(lens, lens[n] as nat) + count_len(lens, lens[n] as nat, n)
}

/// The first symbol from `n` on with code length `l` whose code is the `l`
/// bits at `p`.
pub open spec fn find_n(lens: Seq<u8>, b: Seq<bool>, p: int, l: nat, n: int) -> Option<nat>
    decreases lens.len() - n,
{
    if n < 0 || n >= lens.len() {
        None
    } else if lens[n] as nat == l && code_of(lens, n) == codebits(b, p, l) {
        Some(n as nat)
    } else {
        find_n(lens, b, p, l, n + 1)
    }
}

/// The symbol whose code the bits at `p` start with, trying lengths from `l`
/// up: the symbol and the position after its code. In a code that is not
/// over-subscribed at most one symbol matches, so the order only makes the
/// spec a function.
pub open spec fn find_sym(lens: Seq<u8>, b: Seq<bool>, p: int, l: nat) -> Option<(nat, int)>
    decreases 16 - l,
{
    if l == 0 || l > maxbits() || p < 0 || p + l > b.len() {
        None
    } else {
        match find_n(lens, b, p, l, 0) {
            Some(n) => Some((n, p + l)),
            None => find_sym(lens, b, p, l + 1),
        }
    }
}

pub open spec fn decode_sym(lens: Seq<u8>, b: Seq<bool>, p: int) -> Option<(nat, int)> {
    find_sym(lens, b, p, 1)
}

/// Kraft sum of the first `upto` lengths, in units of 2^-15.
pub open spec fn kraft(lens: Seq<u8>, upto: int) -> nat
    decreases upto,
{
    if upto <= 0 {
        0
    } else {
        kraft(lens, upto - 1)
            + (if 1 <= lens[upto - 1] <= 15 { p2((15 - lens[upto - 1]) as nat) } else { 0nat })
    }
}

/// Every length is at most 15.
pub open spec fn lens_ok(lens: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] <= 15
}

/// Lengths some prefix code has (the Kraft inequality).
pub open spec fn not_oversub(lens: Seq<u8>) -> bool {
    kraft(lens, lens.len() as int) <= p2(15)
}

/// Lengths that leave no bit string unassigned.
pub open spec fn complete(lens: Seq<u8>) -> bool {
    kraft(lens, lens.len() as int) == p2(15)
}

/// Some symbol has a code.
pub open spec fn nonempty(lens: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < lens.len() && lens[i] != 0
}

/// zlib's rule (inftrees.c): no codes at all, or a complete code, or, for a
/// lit/length or distance code, a single code of length 1.
pub open spec fn zlib_ok(lens: Seq<u8>, cl_code: bool) -> bool {
    ||| !nonempty(lens)
    ||| complete(lens)
    ||| (!cl_code && bl_count(lens, 1) == 1 && kraft(lens, lens.len() as int) == p2(14))
}

// ------------------------------------------------------ the fixed tables

/// Base length of lit/length symbol `s` (257..285), 3.2.5.
pub open spec fn len_base(s: nat) -> nat {
    if s <= 264 { (s - 254) as nat }
    else if s <= 268 { (11 + 2 * (s - 265)) as nat }
    else if s <= 272 { (19 + 4 * (s - 269)) as nat }
    else if s <= 276 { (35 + 8 * (s - 273)) as nat }
    else if s <= 280 { (67 + 16 * (s - 277)) as nat }
    else if s <= 284 { (131 + 32 * (s - 281)) as nat }
    else { 258 }
}

/// Extra bits of lit/length symbol `s`, 3.2.5.
pub open spec fn len_extra(s: nat) -> nat {
    if s <= 264 || s == 285 { 0 } else { ((s - 261) / 4) as nat }
}

/// Base distance of distance symbol `d` (0..29), 3.2.5.
pub open spec fn dist_base(d: nat) -> nat {
    if d < 4 { d + 1 } else { (p2(((d / 2) - 1) as nat) * (2 + d % 2) + 1) as nat }
}

/// Extra bits of distance symbol `d`, 3.2.5.
pub open spec fn dist_extra(d: nat) -> nat {
    if d < 4 { 0 } else { ((d / 2) - 1) as nat }
}

/// The fixed lit/length code lengths, 3.2.6.
pub open spec fn fixed_lit() -> Seq<u8> {
    Seq::new(288, |i: int| if i < 144 { 8u8 } else if i < 256 { 9u8 } else if i < 280 { 7u8 } else { 8u8 })
}

/// The fixed distance code: 5-bit codes for all 32 symbols, 3.2.6.
pub open spec fn fixed_dist() -> Seq<u8> {
    Seq::new(32, |i: int| 5u8)
}

// ------------------------------------------------ LZ77 and compressed data

/// Copy `len` bytes from `d` back, one at a time, so that a copy may overlap
/// what it writes (3.2.3).
pub open spec fn lz_copy(out: Seq<u8>, d: nat, len: nat) -> Seq<u8>
    decreases len,
{
    if len == 0 { out } else { lz_copy(out.push(out[out.len() - d]), d, (len - 1) as nat) }
}

/// A decoded symbol's position is past the one it started at.
pub proof fn lemma_find_sym_adv(lens: Seq<u8>, b: Seq<bool>, p: int, l: nat)
    ensures
        find_sym(lens, b, p, l) matches Some((s, q)) ==> p < q <= b.len() && p + l <= q,
    decreases 16 - l,
{
    if !(l == 0 || l > maxbits() || p < 0 || p + l > b.len()) {
        lemma_find_sym_adv(lens, b, p, l + 1);
    }
}

/// The symbols of a compressed block from `p` to its end-of-block code,
/// appended to `out`: the output and the position after end-of-block.
pub open spec fn inflate_syms(lit: Seq<u8>, dist: Seq<u8>, b: Seq<bool>, p: int, out: Seq<u8>)
    -> Option<(Seq<u8>, int)>
    decreases b.len() - p,
{
    match decode_sym(lit, b, p) {
        None => None,
        Some((s, p1)) =>
            if p1 <= p || p1 > b.len() {
                None  // not reached (lemma_find_sym_adv); the measure
            } else if s < 256 {
                inflate_syms(lit, dist, b, p1, out.push(s as u8))
            } else if s == 256 {
                Some((out, p1))
            } else if s > 285 {
                None
            } else {
                match getbits(b, p1, len_extra(s)) {
                    None => None,
                    Some(e) => {
                        let len = len_base(s) + e;
                        let q2 = p1 + len_extra(s);
                        match decode_sym(dist, b, q2) {
                            None => None,
                            Some((ds, p3)) =>
                                if ds > 29 {
                                    None
                                } else {
                                    match getbits(b, p3, dist_extra(ds)) {
                                        None => None,
                                        Some(e2) => {
                                            let d = dist_base(ds) + e2;
                                            let p4 = p3 + dist_extra(ds);
                                            if d > out.len() || p4 <= p || p4 > b.len() {
                                                None
                                            } else {
                                                inflate_syms(lit, dist, b, p4, lz_copy(out, d, len))
                                            }
                                        }
                                    }
                                },
                        }
                    }
                }
            },
    }
}

// ---------------------------------------------------- the dynamic header

/// The order the code length code lengths come in, 3.2.7.
pub open spec fn cl_order(i: nat) -> nat {
    if i == 0 { 16 } else if i == 1 { 17 } else if i == 2 { 18 } else if i == 3 { 0 }
    else if i % 2 == 0 { (8 + (i - 4) / 2) as nat } else { (7 - (i - 5) / 2) as nat }
}

/// Read code length code lengths `i..hclen`, 3 bits each, into `acc`.
pub open spec fn read_cl(b: Seq<bool>, p: int, hclen: nat, i: nat, acc: Seq<u8>)
    -> Option<(Seq<u8>, int)>
    decreases hclen - i,
{
    if i >= hclen {
        Some((acc, p))
    } else {
        match getbits(b, p, 3) {
            None => None,
            Some(v) => read_cl(b, p + 3, hclen, i + 1, acc.update(cl_order(i) as int, v as u8)),
        }
    }
}

/// Decode code lengths with the code length code `cl` until there are
/// `total` of them (3.2.7): 0..15 literally, 16 repeats the previous 3..6
/// times, 17 and 18 write 3..10 and 11..138 zeros.
pub open spec fn read_lens(cl: Seq<u8>, b: Seq<bool>, p: int, total: nat, acc: Seq<u8>)
    -> Option<(Seq<u8>, int)>
    decreases total - acc.len(),
{
    if acc.len() >= total {
        Some((acc, p))
    } else {
        match decode_sym(cl, b, p) {
            None => None,
            Some((s, p1)) =>
                if s < 16 {
                    read_lens(cl, b, p1, total, acc.push(s as u8))
                } else {
                    let (nb, base) = if s == 16 { (2nat, 3nat) } else if s == 17 { (3nat, 3nat) } else { (7nat, 11nat) };
                    match getbits(b, p1, nb) {
                        None => None,
                        Some(e) => {
                            let rep = base + e;
                            if s > 18 || (s == 16 && acc.len() == 0) || acc.len() + rep > total {
                                None
                            } else {
                                let v: u8 = if s == 16 { acc.last() } else { 0u8 };
                                read_lens(cl, b, p1 + nb, total, acc + Seq::new(rep, |_i: int| v))
                            }
                        }
                    }
                },
        }
    }
}

/// A dynamic block's header (3.2.7): the lit/length and distance code
/// lengths, the position after them, and whether zlib accepts them.
pub open spec fn dyn_header(b: Seq<bool>, p: int) -> Option<(Seq<u8>, Seq<u8>, int, bool)> {
    match (getbits(b, p, 5), getbits(b, p + 5, 5), getbits(b, p + 10, 4)) {
        (Some(hlit), Some(hdist), Some(hclen)) => {
            let nlit = hlit + 257;
            let ndist = hdist + 1;
            if nlit > 286 {
                None
            } else {
                match read_cl(b, p + 14, hclen + 4, 0, Seq::new(19, |_i: int| 0u8)) {
                    None => None,
                    Some((cl, q)) =>
                        if !not_oversub(cl) {
                            None
                        } else {
                            match read_lens(cl, b, q, nlit + ndist, Seq::empty()) {
                                None => None,
                                Some((lens, r)) => {
                                    let lit = lens.subrange(0, nlit as int);
                                    let dist = lens.subrange(nlit as int, (nlit + ndist) as int);
                                    if lit[256] == 0 || !not_oversub(lit) || !not_oversub(dist) {
                                        None
                                    } else {
                                        let strict = zlib_ok(cl, true) && zlib_ok(lit, false)
                                            && zlib_ok(dist, false) && ndist <= 30;
                                        Some((lit, dist, r, strict))
                                    }
                                }
                            }
                        },
                }
            }
        }
        _ => None,
    }
}

// ------------------------------------------------------------- the stream

/// A stored block from `p` (just after its 3 header bits): skip to a byte
/// boundary, LEN, NLEN, then LEN bytes (3.2.4).
pub open spec fn stored(b: Seq<bool>, p: int) -> Option<(Seq<u8>, int)> {
    let q = if p % 8 == 0 { p } else { p + (8 - p % 8) };
    match (getbits(b, q, 16), getbits(b, q + 16, 16)) {
        (Some(len), Some(nlen)) =>
            if len + nlen != 65535 || q + 32 + 8 * len > b.len() {
                None
            } else {
                Some((Seq::new(len, |j: int| lval(b.subrange(q + 32 + 8 * j, q + 40 + 8 * j)) as u8),
                      q + 32 + 8 * len))
            },
        _ => None,
    }
}

/// One block from `p`: the output after it, the position after it, and
/// whether zlib accepts it.
pub open spec fn block(b: Seq<bool>, p: int, btype: nat, out: Seq<u8>) -> Option<(Seq<u8>, int, bool)> {
    if btype == 0 {
        match stored(b, p) {
            None => None,
            Some((bytes, q)) => Some((out + bytes, q, true)),
        }
    } else if btype == 1 {
        match inflate_syms(fixed_lit(), fixed_dist(), b, p, out) {
            None => None,
            Some((o, q)) => Some((o, q, true)),
        }
    } else if btype == 2 {
        match dyn_header(b, p) {
            None => None,
            Some((lit, dist, q, strict)) => match inflate_syms(lit, dist, b, q, out) {
                None => None,
                Some((o, r)) => Some((o, r, strict)),
            },
        }
    } else {
        None
    }
}

/// The blocks from `p` to the final one (3.2.3).
pub open spec fn inflate_blocks(b: Seq<bool>, p: int, out: Seq<u8>, strict: bool)
    -> Option<(Seq<u8>, int, bool)>
    decreases b.len() - p,
{
    match (getbits(b, p, 1), getbits(b, p + 1, 2)) {
        (Some(bfinal), Some(btype)) => match block(b, p + 3, btype, out) {
            None => None,
            Some((o, q, s)) =>
                if bfinal == 1 {
                    Some((o, q, strict && s))
                } else if q <= p || q > b.len() {
                    None  // not reached: every block reads its header
                } else {
                    inflate_blocks(b, q, o, strict && s)
                },
        },
        _ => None,
    }
}

/// A raw DEFLATE stream: the data, the bits the stream took, and whether
/// zlib accepts it.
pub open spec fn inflate(b: Seq<bool>) -> Option<(Seq<u8>, nat, bool)> {
    match inflate_blocks(b, 0, Seq::empty(), true) {
        None => None,
        Some((o, q, s)) => Some((o, q as nat, s)),
    }
}

} // verus!
