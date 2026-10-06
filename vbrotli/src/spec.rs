//! RFC 7932 (Brotli), as a spec decoder over the stream's bits.
//!
//! The stream is `lbits(input)`: bytes LSB-first, integers LSB-first and
//! prefix codes MSB-first (1.5.1), as in DEFLATE, so the bit fields and the
//! canonical prefix codes are `vdeflate::spec`'s. Positions are bit offsets
//! from the start of the stream.
//!
//! `brotli(dict, b)` is the output, the number of bits the stream took (a
//! whole number of bytes: the stream ends on a byte boundary, 9.2), and
//! whether Google's decoder (1.2.0) also accepts it. `dict` is the static
//! dictionary (8, Appendix A): the spec holds for any byte sequence laid out
//! as the dictionary is (`dict_ok`), and the decoder is handed Google's, which
//! a test checks byte for byte. Nothing here depends on the words themselves.
//!
//! The spec rejects a stream exactly where the RFC says a decoder should
//! ("should be rejected as invalid", "must be zero", "invalid and must not
//! be used"), and where it gives no reading at all:
//!
//! * the WBITS pattern 0010001 (9.1);
//! * a reserved bit set, a length whose last nibble or byte is zero when it
//!   has more than the fewest (9.2), fill bits that are not zero (9.2);
//! * a simple prefix code symbol outside the alphabet, or repeated (3.4); a
//!   code length code or code that is over-subscribed or not complete (other
//!   than a single symbol), a run of code lengths past the alphabet (3.5);
//! * a run of zeros past the end of a context map (7.3);
//! * a distance from the last-distance ring that is 0 or less (4);
//! * a dictionary reference of a length outside 4..24 or with a transform
//!   past 120 (8);
//! * an insert, copy or dictionary word that would take the meta-block past
//!   MLEN (9.3); a stream that ends before its last meta-block does (10);
//! * a block count used up in a category with one block type (only after
//!   2^24 elements, which takes commands that output nothing): the RFC's
//!   algorithm would read a block type with a code that does not exist.
//!
//! Some "must"s constrain the encoder and are not checked, as Google's
//! decoder does not check them: that NTREES is the number of distinct values
//! of the context map, and that NBLTYPES is the largest block type used plus
//! one (6, 7.3). Neither changes what a stream decodes to.
//!
//! Where Google's decoder is stricter, the stream decodes the same and the
//! flag is false: a dictionary word that transforms to nothing at a distance
//! of at most 120 (decode.c: "Invalid length-0 dictionary word after
//! transform").
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::{p2, lemma_p2_pos};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::lsb::lval;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::{getbits, decode_sym, lz_copy};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::tables::*;

verus! {

// ------------------------------------------------------------ bit fields

/// `p` rounded up to a byte boundary.
pub open spec fn align8(p: int) -> int {
    if p % 8 == 0 { p } else { p + (8 - p % 8) }
}

/// The fill bits from `p` to the next byte boundary are there and zero.
pub open spec fn zero_fill(b: Seq<bool>, p: int) -> bool {
    getbits(b, p, (align8(p) - p) as nat) == Some(0nat)
}

/// `n` bytes from the byte boundary `q`.
pub open spec fn bytes_at(b: Seq<bool>, q: int, n: nat) -> Seq<u8> {
    Seq::new(n, |j: int| lval(b.subrange(q + 8 * j, q + 8 * j + 8)) as u8)
}

// --------------------------------------------------------- prefix codes

/// How many of the first `upto` code lengths are not zero.
pub open spec fn nnz(lens: Seq<u8>, upto: int) -> nat
    decreases upto,
{
    if upto <= 0 { 0 } else { nnz(lens, upto - 1) + (if lens[upto - 1] != 0 { 1nat } else { 0nat }) }
}

/// The first symbol from `i` on whose code length is not zero.
pub open spec fn first_nz(lens: Seq<u8>, i: int) -> int
    decreases lens.len() - i,
{
    if i < 0 || i >= lens.len() || lens[i] != 0 { i } else { first_nz(lens, i + 1) }
}

/// One symbol with the prefix code of lengths `lens`: the symbol and the
/// position after its code. A code with one symbol takes no bits (3.4
/// NSYM = 1, 3.5); any other is the canonical code of its lengths (3.2).
pub open spec fn dsym(lens: Seq<u8>, b: Seq<bool>, p: int) -> Option<(nat, int)> {
    if nnz(lens, lens.len() as int) == 1 {
        Some((first_nz(lens, 0) as nat, p))
    } else {
        decode_sym(lens, b, p)
    }
}

/// ALPHABET_BITS of 3.4: the fewest bits that hold every symbol below
/// `asize` (alphabets here have 2 to 704 symbols).
pub open spec fn abits(asize: nat) -> nat {
    if asize <= 2 { 1 } else if asize <= 4 { 2 } else if asize <= 8 { 3 } else if asize <= 16 { 4 }
    else if asize <= 32 { 5 } else if asize <= 64 { 6 } else if asize <= 128 { 7 }
    else if asize <= 256 { 8 } else if asize <= 512 { 9 } else if asize <= 1024 { 10 } else { 11 }
}

/// Simple prefix code symbols until there are `n`, each `abits(asize)`
/// bits and below `asize` (3.4).
pub open spec fn read_syms(b: Seq<bool>, p: int, asize: nat, n: nat, acc: Seq<nat>)
    -> Option<(Seq<nat>, int)>
    decreases n - acc.len(),
{
    if acc.len() >= n {
        Some((acc, p))
    } else {
        match getbits(b, p, abits(asize)) {
            None => None,
            Some(v) => if v >= asize { None } else { read_syms(b, p + abits(asize), asize, n, acc.push(v)) },
        }
    }
}

pub open spec fn distinct(s: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

/// A simple prefix code (3.4), from just after its HSKIP of 1: its code
/// lengths. NSYM = 1 gives one symbol a nonzero length, which `dsym` reads
/// as a code of no bits.
pub open spec fn simple_code(b: Seq<bool>, p: int, asize: nat) -> Option<(Seq<u8>, int)> {
    match getbits(b, p, 2) {
        None => None,
        Some(m) => match read_syms(b, p + 2, asize, m + 1, Seq::empty()) {
            None => None,
            Some((s, q)) => {
                let z = Seq::new(asize, |_i: int| 0u8);
                if !distinct(s) {
                    None
                } else if m == 0 {
                    Some((z.update(s[0] as int, 1u8), q))
                } else if m == 1 {
                    Some((z.update(s[0] as int, 1u8).update(s[1] as int, 1u8), q))
                } else if m == 2 {
                    Some((z.update(s[0] as int, 1u8).update(s[1] as int, 2u8).update(s[2] as int, 2u8), q))
                } else {
                    match getbits(b, q, 1) {
                        None => None,
                        Some(ts) => if ts == 0 {
                            Some((z.update(s[0] as int, 2u8).update(s[1] as int, 2u8)
                                  .update(s[2] as int, 2u8).update(s[3] as int, 2u8), q + 1))
                        } else {
                            Some((z.update(s[0] as int, 1u8).update(s[1] as int, 2u8)
                                  .update(s[2] as int, 3u8).update(s[3] as int, 3u8), q + 1))
                        },
                    }
                }
            },
        },
    }
}

/// A code length code length, in the fixed code of 3.5 (bits read from the
/// right of the patterns there): 00 is 0, 10 is 3, 01 is 4, 011 is 2, 0111
/// is 1, 1111 is 5. The length and the position after it.
pub open spec fn cl_len(b: Seq<bool>, p: int) -> Option<(nat, int)> {
    match getbits(b, p, 2) {
        None => None,
        Some(v) => if v == 0 {
            Some((0, p + 2))
        } else if v == 2 {
            Some((3, p + 2))
        } else if v == 1 {
            Some((4, p + 2))
        } else {
            match getbits(b, p + 2, 1) {
                None => None,
                Some(x) => if x == 0 {
                    Some((2, p + 3))
                } else {
                    match getbits(b, p + 3, 1) {
                        None => None,
                        Some(y) => if y == 0 { Some((1, p + 4)) } else { Some((5, p + 4)) },
                    }
                },
            }
        },
    }
}

/// The order code length code lengths come in (3.5).
pub open spec fn cl_order() -> Seq<nat> {
    seq![1nat, 2, 3, 4, 0, 5, 17, 6, 16, 7, 8, 9, 10, 11, 12, 13, 14, 15]
}

/// Code length code lengths from the `i`-th in `cl_order` into `acc`, with
/// `space` (of 32) left and `num` nonzero so far (3.5). They stop when the
/// code is complete; one nonzero length after all 18 is a code of one
/// symbol; anything else is invalid.
pub open spec fn read_cl(b: Seq<bool>, p: int, i: nat, acc: Seq<u8>, space: int, num: nat)
    -> Option<(Seq<u8>, int)>
    decreases 18 - i,
{
    if i >= 18 {
        if num == 1 { Some((acc, p)) } else { None }
    } else {
        match cl_len(b, p) {
            None => None,
            Some((v, q)) => {
                let acc2 = acc.update(cl_order()[i as int] as int, v as u8);
                if v == 0 {
                    read_cl(b, q, i + 1, acc2, space, num)
                } else {
                    let s2 = space - (32nat / p2(v)) as int;
                    if s2 == 0 {
                        Some((acc2, q))
                    } else if s2 < 0 {
                        None
                    } else {
                        read_cl(b, q, i + 1, acc2, s2, num + 1)
                    }
                }
            },
        }
    }
}

/// Symbol code lengths (3.5) with the code length code `cl`: `acc` has
/// them for the symbols before `sym`, `space` (of 32768) is left, `prev` is
/// the last nonzero length (8 at first), and `rep` is the count of the run
/// just read if it was of `rep_len`s (0 after a single length). They stop
/// when the code is complete or the alphabet is used up; it must then be
/// complete.
pub open spec fn read_lens(
    cl: Seq<u8>, b: Seq<bool>, p: int, asize: nat, acc: Seq<u8>, sym: nat, space: int,
    prev: nat, rep: nat, rep_len: nat,
) -> Option<(Seq<u8>, int)>
    decreases asize - sym,
{
    if sym >= asize || space <= 0 {
        if space == 0 { Some((acc, p)) } else { None }
    } else {
        match dsym(cl, b, p) {
            None => None,
            Some((s, q)) =>
                if s == 0 {
                    read_lens(cl, b, q, asize, acc, sym + 1, space, prev, 0, rep_len)
                } else if s < 16 {
                    read_lens(cl, b, q, asize, acc.update(sym as int, s as u8), sym + 1,
                              space - (32768nat / p2(s)) as int, s, 0, rep_len)
                } else {
                    // 16 repeats the last nonzero length, 17 repeats zero; a
                    // repeat right after one of the same kind extends it.
                    let nb: nat = if s == 16 { 2 } else { 3 };
                    let nl: nat = if s == 16 { prev } else { 0 };
                    match getbits(b, q, nb) {
                        None => None,
                        Some(e) => {
                            let old: nat = if rep_len == nl { rep } else { 0 };
                            let r: nat = (if old > 0 { ((old - 2) * p2(nb)) as nat } else { 0nat }) + e + 3;
                            let delta = r - old;
                            if s > 17 || delta <= 0 || sym + delta > asize {
                                None
                            } else {
                                let acc2 = Seq::new(asize, |j: int|
                                    if sym <= j < sym + delta { nl as u8 } else { acc[j] });
                                let sp2 = if nl == 0 { space } else { space - delta * (32768nat / p2(nl)) as int };
                                read_lens(cl, b, q + nb, asize, acc2, (sym + delta) as nat, sp2, prev, r, nl)
                            }
                        }
                    }
                },
        }
    }
}

/// A prefix code over an alphabet of `asize` symbols (3.4, 3.5): its code
/// lengths and the position after it.
pub open spec fn read_code(b: Seq<bool>, p: int, asize: nat) -> Option<(Seq<u8>, int)> {
    match getbits(b, p, 2) {
        None => None,
        Some(h) =>
            if h == 1 {
                simple_code(b, p + 2, asize)
            } else {
                match read_cl(b, p + 2, h, Seq::new(18, |_i: int| 0u8), 32, 0) {
                    None => None,
                    Some((cl, q)) =>
                        read_lens(cl, b, q, asize, Seq::new(asize, |_i: int| 0u8), 0, 32768, 8, 0, 0),
                }
            },
    }
}

// ------------------------------------------------------------- integers

/// The 1..11-bit code of 9.2 for NBLTYPES - 1 and NTREES - 1 (0..255).
pub open spec fn varlen8(b: Seq<bool>, p: int) -> Option<(nat, int)> {
    match getbits(b, p, 1) {
        None => None,
        Some(x) => if x == 0 {
            Some((0, p + 1))
        } else {
            match getbits(b, p + 1, 3) {
                None => None,
                Some(n) => if n == 0 {
                    Some((1, p + 4))
                } else {
                    match getbits(b, p + 4, n) {
                        None => None,
                        Some(e) => Some((p2(n) + e, p + 4 + n)),
                    }
                },
            }
        },
    }
}

/// Block count codes: base and extra bits (6).
pub open spec fn bc_base() -> Seq<nat> {
    seq![1nat, 5, 9, 13, 17, 25, 33, 41, 49, 65, 81, 97, 113, 145, 177, 209, 241, 305, 369, 497,
         753, 1265, 2289, 4337, 8433, 16625]
}

pub open spec fn bc_extra() -> Seq<nat> {
    seq![2nat, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 7, 8, 9, 10, 11, 12, 13, 24]
}

/// Insert length codes: base and extra bits (5).
pub open spec fn ins_base() -> Seq<nat> {
    seq![0nat, 1, 2, 3, 4, 5, 6, 8, 10, 14, 18, 26, 34, 50, 66, 98, 130, 194, 322, 578, 1090, 2114,
         6210, 22594]
}

pub open spec fn ins_extra() -> Seq<nat> {
    seq![0nat, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 8, 9, 10, 12, 14, 24]
}

/// Copy length codes: base and extra bits (5).
pub open spec fn copy_base() -> Seq<nat> {
    seq![2nat, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 18, 22, 30, 38, 54, 70, 102, 134, 198, 326, 582,
         1094, 2118]
}

pub open spec fn copy_extra() -> Seq<nat> {
    seq![0nat, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 8, 9, 10, 24]
}

/// Where the insert and copy length codes of each 64-symbol cell of the
/// insert-and-copy alphabet start (5).
pub open spec fn cell_ins() -> Seq<nat> { seq![0nat, 0, 0, 0, 8, 8, 0, 16, 8, 16, 16] }

pub open spec fn cell_copy() -> Seq<nat> { seq![0nat, 8, 0, 8, 0, 8, 16, 0, 16, 8, 16] }

/// The insert length code of insert-and-copy symbol `c` (0..703).
pub open spec fn ins_code(c: nat) -> nat { cell_ins()[(c / 64) as int] + (c / 8) % 8 }

/// Its copy length code.
pub open spec fn copy_code(c: nat) -> nat { cell_copy()[(c / 64) as int] + c % 8 }

/// A block count (6): the count and the position after it.
pub open spec fn read_count(code: Seq<u8>, b: Seq<bool>, p: int) -> Option<(nat, int)> {
    match dsym(code, b, p) {
        None => None,
        Some((s, q)) =>
            if s >= 26 {
                None
            } else {
                match getbits(b, q, bc_extra()[s as int]) {
                    None => None,
                    Some(e) => Some((bc_base()[s as int] + e, q + bc_extra()[s as int])),
                }
            },
    }
}

// ---------------------------------------------------- the context model

/// The context map values (7.3) until there are `size`: symbol 0 is a 0,
/// 1..rlemax a run of zeros, and above that the value `s - rlemax`.
pub open spec fn read_cmap_vals(code: Seq<u8>, rlemax: nat, b: Seq<bool>, p: int, size: nat, acc: Seq<nat>)
    -> Option<(Seq<nat>, int)>
    decreases size - acc.len() via read_cmap_vals_decreases
{
    if acc.len() >= size {
        Some((acc, p))
    } else {
        match dsym(code, b, p) {
            None => None,
            Some((s, q)) =>
                if s == 0 {
                    read_cmap_vals(code, rlemax, b, q, size, acc.push(0))
                } else if s <= rlemax {
                    match getbits(b, q, s) {
                        None => None,
                        Some(e) =>
                            if acc.len() + p2(s) + e > size {
                                None
                            } else {
                                read_cmap_vals(code, rlemax, b, q + s, size,
                                               acc + Seq::new(p2(s) + e, |_i: int| 0nat))
                            },
                    }
                } else {
                    read_cmap_vals(code, rlemax, b, q, size, acc.push((s - rlemax) as nat))
                },
        }
    }
}

#[via_fn]
proof fn read_cmap_vals_decreases(code: Seq<u8>, rlemax: nat, b: Seq<bool>, p: int, size: nat, acc: Seq<nat>) {
    match dsym(code, b, p) {
        Some((s, q)) => lemma_p2_pos(s),
        None => {}
    }
}

/// Move the `i`-th entry of the move-to-front list to the front.
pub open spec fn mtf_step(mtf: Seq<nat>, i: nat) -> Seq<nat> {
    seq![mtf[i as int]] + mtf.take(i as int) + mtf.skip(i as int + 1)
}

/// The inverse move-to-front transform of 7.3, with the list `mtf`.
pub open spec fn imtf(v: Seq<nat>, mtf: Seq<nat>) -> Seq<nat>
    decreases v.len(),
{
    if v.len() == 0 {
        Seq::empty()
    } else {
        seq![mtf[v[0] as int]] + imtf(v.skip(1), mtf_step(mtf, v[0]))
    }
}

/// Every value of a context map names one of its NTREES codes.
pub open spec fn cmap_below(map: Seq<nat>, ntrees: nat) -> bool {
    forall|i: int| 0 <= i < map.len() ==> #[trigger] map[i] < ntrees
}

/// NTREES and a context map of `size` entries (7.3, 9.2): the map, NTREES
/// and the position after them.
pub open spec fn read_cmap(b: Seq<bool>, p: int, size: nat) -> Option<(Seq<nat>, nat, int)> {
    match varlen8(b, p) {
        None => None,
        Some((t, q)) =>
            if t == 0 {
                Some((Seq::new(size, |_i: int| 0nat), 1, q))
            } else {
                let ntrees = t + 1;
                let rle = match getbits(b, q, 1) {
                    None => None,
                    Some(x) => if x == 0 {
                        Some((0nat, q + 1))
                    } else {
                        match getbits(b, q + 1, 4) {
                            None => None,
                            Some(r) => Some((r + 1, q + 5)),
                        }
                    },
                };
                match rle {
                    None => None,
                    Some((rlemax, q2)) => match read_code(b, q2, ntrees + rlemax) {
                        None => None,
                        Some((code, q3)) => match read_cmap_vals(code, rlemax, b, q3, size, Seq::empty()) {
                            None => None,
                            Some((v, q4)) => match getbits(b, q4, 1) {
                                None => None,
                                Some(x) => {
                                    let map = if x == 1 { imtf(v, Seq::new(256, |i: int| i as nat)) } else { v };
                                    if !cmap_below(map, ntrees) {
                                        None  // not reached: every value is below NTREES
                                    } else {
                                        Some((map, ntrees, q4 + 1))
                                    }
                                }
                            },
                        },
                    },
                }
            },
    }
}

/// The last byte of the output, or 0 (7.1).
pub open spec fn p1(out: Seq<u8>) -> u8 { if out.len() >= 1 { out[out.len() - 1] } else { 0 } }

/// The byte before it, or 0.
pub open spec fn p2b(out: Seq<u8>) -> u8 { if out.len() >= 2 { out[out.len() - 2] } else { 0 } }

/// The literal context ID of context mode `mode` (7.1).
pub open spec fn lit_ctx(mode: nat, x1: u8, x2: u8) -> nat {
    if mode == 0 {
        (x1 % 64) as nat
    } else if mode == 1 {
        (x1 / 4) as nat
    } else if mode == 2 {
        (lut0()[x1 as int] | lut1()[x2 as int]) as nat
    } else {
        (8 * lut2()[x1 as int] + lut2()[x2 as int]) as nat
    }
}

/// The distance context ID of a copy length (7.2).
pub open spec fn dist_ctx(clen: nat) -> nat { if clen > 4 { 3 } else { (clen - 2) as nat } }

// -------------------------------------------------------------- distances

/// The size of the distance alphabet (3.3, 4).
pub open spec fn dist_asize(npostfix: nat, ndirect: nat) -> nat { 16 + ndirect + 48 * p2(npostfix) }

/// The distance of short code `c` (0..15) from the ring of the last four,
/// `ring[0]` the last (4).
pub open spec fn short_dist(ring: Seq<int>, c: nat) -> int {
    if c < 4 {
        ring[c as int]
    } else {
        let base = if c < 10 { ring[0] } else { ring[1] };
        let k: int = if c < 10 { c - 4 } else { c - 10 };
        if k % 2 == 0 { base - (k / 2 + 1) } else { base + (k / 2 + 1) }
    }
}

/// The extra bits of distance code `dcode` >= 16 + NDIRECT (4).
pub open spec fn dist_nbits(npostfix: nat, ndirect: nat, dcode: nat) -> nat {
    1 + (dcode - ndirect - 16) as nat / p2(npostfix + 1)
}

/// The distance of code `dcode` >= 16 + NDIRECT with extra bits `dextra` (4).
pub open spec fn long_dist(npostfix: nat, ndirect: nat, dcode: nat, dextra: nat) -> nat {
    let x = (dcode - ndirect - 16) as nat;
    let hcode = x / p2(npostfix);
    let lcode = x % p2(npostfix);
    let offset = ((2 + hcode % 2) * p2(dist_nbits(npostfix, ndirect, dcode)) - 4) as nat;
    (offset + dextra) * p2(npostfix) + lcode + ndirect + 1
}

// ----------------------------------------------------- static dictionary

/// DOFFSET of 8: where the words of length `len` start.
pub open spec fn doffset(len: nat) -> nat
    decreases len,
{
    if len == 0 {
        0
    } else {
        let l = (len - 1) as nat;
        doffset(l) + l * (if l >= 4 { p2(ndbits()[l as int] as nat) } else { 0nat })
    }
}

/// The size of the dictionary (DICTSIZE of 8).
pub open spec fn dict_size() -> nat { doffset(25) }

/// A dictionary laid out as the RFC's is.
pub open spec fn dict_ok(dict: Seq<u8>) -> bool { dict.len() == dict_size() }

/// The word of length `len` (4..24) and index `idx`.
pub open spec fn dict_word(dict: Seq<u8>, len: nat, idx: nat) -> Seq<u8> {
    dict.subrange((doffset(len) + idx * len) as int, (doffset(len) + idx * len + len) as int)
}

/// `Ferment` of 8 at `pos`: the word after it.
pub open spec fn ferment(w: Seq<u8>, pos: int) -> Seq<u8> {
    if w[pos] < 192 {
        if 97 <= w[pos] <= 122 { w.update(pos, w[pos] ^ 32u8) } else { w }
    } else if w[pos] < 224 {
        if pos + 1 < w.len() { w.update(pos + 1, w[pos + 1] ^ 32u8) } else { w }
    } else {
        if pos + 2 < w.len() { w.update(pos + 2, w[pos + 2] ^ 5u8) } else { w }
    }
}

/// How far `Ferment` at `pos` moves on.
pub open spec fn ferment_step(w: Seq<u8>, pos: int) -> int {
    if w[pos] < 192 { 1 } else if w[pos] < 224 { 2 } else { 3 }
}

/// `FermentAll` of 8, from `i` on.
pub open spec fn ferment_all(w: Seq<u8>, i: int) -> Seq<u8>
    decreases w.len() + 3 - i via ferment_all_decreases
{
    if i < 0 || i >= w.len() {
        w
    } else {
        ferment_all(ferment(w, i), i + ferment_step(w, i))
    }
}

#[via_fn]
proof fn ferment_all_decreases(w: Seq<u8>, i: int) {
    if 0 <= i < w.len() {
        assert(ferment(w, i).len() == w.len());
        assert(ferment_step(w, i) >= 1);
    }
}

/// Elementary transform `t` of a word (8): 0 Identity, 1 FermentFirst,
/// 2 FermentAll, 3..11 OmitFirst1..9, 12..20 OmitLast1..9.
pub open spec fn elem(t: nat, w: Seq<u8>) -> Seq<u8> {
    if t == 0 {
        w
    } else if t == 1 {
        if w.len() > 0 { ferment(w, 0) } else { w }
    } else if t == 2 {
        ferment_all(w, 0)
    } else if t <= 11 {
        let k = t - 2;
        if w.len() < k { Seq::empty() } else { w.skip(k) }
    } else {
        let k = t - 11;
        if w.len() < k { Seq::empty() } else { w.take(w.len() - k) }
    }
}

/// Transform `id` (0..120) of a word: prefix, elementary transform, suffix
/// (8, Appendix B).
pub open spec fn transform(id: nat, w: Seq<u8>) -> Seq<u8> {
    tr_pre().subrange(tr_pre_off()[id as int] as int, tr_pre_off()[id as int + 1] as int)
        + elem(tr_type()[id as int] as nat, w)
        + tr_suf().subrange(tr_suf_off()[id as int] as int, tr_suf_off()[id as int + 1] as int)
}

// ------------------------------------------------- the meta-block header

/// One of the three block categories of a meta-block (literals,
/// insert-and-copy lengths, distances): NBLTYPES, the codes for block types
/// and counts, and the first block's count (9.2).
pub struct Cat {
    pub n: nat,
    pub tcode: Seq<u8>,
    pub ccode: Seq<u8>,
    pub first: nat,
}

/// A category's header (9.2). With one block type, the count is 2^24 (10).
pub open spec fn read_cat(b: Seq<bool>, p: int) -> Option<(Cat, int)> {
    match varlen8(b, p) {
        None => None,
        Some((v, q)) =>
            if v == 0 {
                Some((Cat { n: 1, tcode: Seq::empty(), ccode: Seq::empty(), first: p2(24) }, q))
            } else {
                match read_code(b, q, v + 3) {
                    None => None,
                    Some((tcode, q2)) => match read_code(b, q2, 26) {
                        None => None,
                        Some((ccode, q3)) => match read_count(ccode, b, q3) {
                            None => None,
                            Some((first, q4)) => Some((Cat { n: v + 1, tcode, ccode, first }, q4)),
                        },
                    },
                }
            },
    }
}

/// `n` context modes, two bits each (7.1).
pub open spec fn read_modes(b: Seq<bool>, p: int, n: nat, acc: Seq<nat>) -> Option<(Seq<nat>, int)>
    decreases n - acc.len(),
{
    if acc.len() >= n {
        Some((acc, p))
    } else {
        match getbits(b, p, 2) {
            None => None,
            Some(m) => read_modes(b, p + 2, n, acc.push(m)),
        }
    }
}

/// `n` prefix codes over an alphabet of `asize`.
pub open spec fn read_codes(b: Seq<bool>, p: int, asize: nat, n: nat, acc: Seq<Seq<u8>>)
    -> Option<(Seq<Seq<u8>>, int)>
    decreases n - acc.len(),
{
    if acc.len() >= n {
        Some((acc, p))
    } else {
        match read_code(b, p, asize) {
            None => None,
            Some((c, q)) => read_codes(b, q, asize, n, acc.push(c)),
        }
    }
}

/// A compressed meta-block's header after ISUNCOMPRESSED (9.2).
pub struct Hdr {
    pub cl: Cat,
    pub ci: Cat,
    pub cd: Cat,
    pub npostfix: nat,
    pub ndirect: nat,
    pub modes: Seq<nat>,
    pub cmapl: Seq<nat>,
    pub cmapd: Seq<nat>,
    pub lit: Seq<Seq<u8>>,
    pub cmd: Seq<Seq<u8>>,
    pub dist: Seq<Seq<u8>>,
}

pub open spec fn read_hdr(b: Seq<bool>, p: int) -> Option<(Hdr, int)> {
    match read_cat(b, p) {
        None => None,
        Some((cl, p1)) => match read_cat(b, p1) {
            None => None,
            Some((ci, p2_)) => match read_cat(b, p2_) {
                None => None,
                Some((cd, p3)) => match (getbits(b, p3, 2), getbits(b, p3 + 2, 4)) {
                    (Some(npostfix), Some(nd4)) => {
                        let ndirect = nd4 * p2(npostfix);
                        match read_modes(b, p3 + 6, cl.n, Seq::empty()) {
                            None => None,
                            Some((modes, p4)) => match read_cmap(b, p4, 64 * cl.n) {
                                None => None,
                                Some((cmapl, ntl, p5)) => match read_cmap(b, p5, 4 * cd.n) {
                                    None => None,
                                    Some((cmapd, ntd, p6)) => match read_codes(b, p6, 256, ntl, Seq::empty()) {
                                        None => None,
                                        Some((lit, p7)) => match read_codes(b, p7, 704, ci.n, Seq::empty()) {
                                            None => None,
                                            Some((cmd, p8)) =>
                                                match read_codes(b, p8, dist_asize(npostfix, ndirect), ntd, Seq::empty()) {
                                                    None => None,
                                                    Some((dist, p9)) => Some((
                                                        Hdr { cl, ci, cd, npostfix, ndirect, modes, cmapl, cmapd, lit, cmd, dist },
                                                        p9)),
                                                },
                                        },
                                    },
                                },
                            },
                        }
                    }
                    _ => None,
                },
            },
        },
    }
}

// -------------------------------------------------------------- commands

/// A category's current block: its type, the type before it, and how many
/// more elements it has (6).
pub struct Blk {
    pub t: nat,
    pub prev: nat,
    pub left: nat,
}

/// A category's first block (6, 10).
pub open spec fn blk0(c: Cat) -> Blk { Blk { t: 0, prev: 1, left: c.first } }

/// Take the next element of a category: switch blocks first if the block
/// is used up (6, 9.3). The block the element is in and the position after
/// the switch.
pub open spec fn next_blk(c: Cat, k: Blk, b: Seq<bool>, p: int) -> Option<(Blk, int)> {
    if k.left > 0 {
        Some((Blk { t: k.t, prev: k.prev, left: (k.left - 1) as nat }, p))
    } else if c.n < 2 {
        None
    } else {
        match dsym(c.tcode, b, p) {
            None => None,
            Some((s, q)) => {
                let t: nat = if s == 0 { k.prev } else if s == 1 { (k.t + 1) % c.n } else { (s - 2) as nat };
                match read_count(c.ccode, b, q) {
                    None => None,
                    Some((cnt, r)) => Some((Blk { t, prev: k.t, left: (cnt - 1) as nat }, r)),
                }
            },
        }
    }
}

/// `n` literals appended to `out` (9.3): the output, the literal block and
/// the position after them.
pub open spec fn lits(h: Hdr, b: Seq<bool>, p: int, n: nat, out: Seq<u8>, bl: Blk)
    -> Option<(Seq<u8>, Blk, int)>
    decreases n,
{
    if n == 0 {
        Some((out, bl, p))
    } else {
        match next_blk(h.cl, bl, b, p) {
            None => None,
            Some((bl2, q)) => {
                let ctx = lit_ctx(h.modes[bl2.t as int], p1(out), p2b(out));
                match dsym(h.lit[h.cmapl[(64 * bl2.t + ctx) as int] as int], b, q) {
                    None => None,
                    Some((s, r)) => lits(h, b, r, (n - 1) as nat, out.push(s as u8), bl2),
                }
            },
        }
    }
}

/// The decoder's state between commands and meta-blocks: the output, the
/// last four distances (`ring[0]` the last), and whether Google's decoder
/// accepts the stream so far.
pub struct St {
    pub out: Seq<u8>,
    pub ring: Seq<int>,
    pub google: bool,
}

/// The distance of a command whose insert-and-copy symbol is `c` and copy
/// length `clen`: the distance, whether it came from an explicit distance
/// code other than 0 (so goes into the ring if it is not a dictionary
/// reference), the distance block and the position after it (4, 9.3).
pub open spec fn read_dist(h: Hdr, ring: Seq<int>, c: nat, clen: nat, b: Seq<bool>, p: int, bd: Blk)
    -> Option<(int, bool, Blk, int)>
{
    if c < 128 {
        Some((ring[0], false, bd, p))
    } else {
        match next_blk(h.cd, bd, b, p) {
            None => None,
            Some((bd2, q)) => match dsym(h.dist[h.cmapd[(4 * bd2.t + dist_ctx(clen)) as int] as int], b, q) {
                None => None,
                Some((dc, q2)) =>
                    if dc < 16 {
                        let d = short_dist(ring, dc);
                        if d <= 0 { None } else { Some((d, dc != 0, bd2, q2)) }
                    } else if dc < 16 + h.ndirect {
                        Some((dc - 15, true, bd2, q2))
                    } else {
                        let nb = dist_nbits(h.npostfix, h.ndirect, dc);
                        match getbits(b, q2, nb) {
                            None => None,
                            Some(e) => Some((long_dist(h.npostfix, h.ndirect, dc, e) as int, true, bd2, q2 + nb)),
                        }
                    },
            },
        }
    }
}

/// A dictionary reference (8): distance `d` past `maxd`, length `clen`.
/// The new state, or nothing if it is invalid or would pass `end`.
pub open spec fn dict_ref(dict: Seq<u8>, maxd: int, st: St, d: int, clen: nat, end: nat) -> Option<St> {
    let wid = (d - maxd - 1) as nat;
    if clen < 4 || clen > 24 {
        None
    } else {
        let nw = p2(ndbits()[clen as int] as nat);
        let tid = wid / nw;
        if tid > 120 {
            None
        } else {
            let w = transform(tid, dict_word(dict, clen, wid % nw));
            if st.out.len() + w.len() > end {
                None
            } else {
                Some(St { out: st.out + w, ring: st.ring, google: st.google && !(w.len() == 0 && d <= 120) })
            }
        }
    }
}

/// The copy part of a command: `clen` bytes from `d` back, or, past the
/// window or the start of the output, a dictionary word (4, 8). The new
/// state, or nothing if it is invalid or would pass `end`.
pub open spec fn do_copy(dict: Seq<u8>, window: nat, st: St, d: int, explicit: bool, clen: nat, end: nat)
    -> Option<St>
{
    let maxd: int = if st.out.len() < window { st.out.len() as int } else { window as int };
    if d > maxd {
        dict_ref(dict, maxd, st, d, clen, end)
    } else if st.out.len() + clen > end {
        None
    } else {
        Some(St {
            out: lz_copy(st.out, d as nat, clen),
            ring: if explicit { seq![d] + st.ring.take(3) } else { st.ring },
            google: st.google,
        })
    }
}

/// The start of a command (9.3): its block, its insert-and-copy symbol,
/// the insert and copy lengths, and the position after their extra bits.
pub open spec fn cmd_head(h: Hdr, b: Seq<bool>, p: int, bi: Blk) -> Option<(Blk, nat, nat, nat, int)> {
    match next_blk(h.ci, bi, b, p) {
        None => None,
        Some((bi2, q)) => match dsym(h.cmd[bi2.t as int], b, q) {
            None => None,
            Some((c, q1)) => {
                let ic = ins_code(c);
                let cc = copy_code(c);
                match getbits(b, q1, ins_extra()[ic as int]) {
                    None => None,
                    Some(e1) => {
                        let q2 = q1 + ins_extra()[ic as int];
                        match getbits(b, q2, copy_extra()[cc as int]) {
                            None => None,
                            Some(e2) => Some((bi2, c, ins_base()[ic as int] + e1, copy_base()[cc as int] + e2,
                                              q2 + copy_extra()[cc as int])),
                        }
                    }
                }
            },
        },
    }
}

/// The end of a command (9.3): its distance and its copy or dictionary
/// word; the state, the distance block and the position after it.
pub open spec fn cmd_tail(dict: Seq<u8>, window: nat, h: Hdr, b: Seq<bool>, p: int, end: nat, st: St,
                          c: nat, clen: nat, bd: Blk) -> Option<(St, Blk, int)> {
    match read_dist(h, st.ring, c, clen, b, p, bd) {
        None => None,
        Some((d, explicit, bd2, q)) => match do_copy(dict, window, st, d, explicit, clen, end) {
            None => None,
            Some(st2) => Some((st2, bd2, q)),
        },
    }
}

/// What one command leaves: the meta-block done (the state and the
/// position after it), or the state and blocks for the next command.
pub enum Step {
    Done(St, int),
    Next(St, Blk, Blk, Blk, int),
}

/// One command (9.3), from the state `st` and the blocks `bl`, `bi`, `bd`.
pub open spec fn cmd_step(
    dict: Seq<u8>, window: nat, h: Hdr, b: Seq<bool>, p: int, end: nat, st: St, bl: Blk, bi: Blk, bd: Blk,
) -> Option<Step> {
    match cmd_head(h, b, p, bi) {
        None => None,
        Some((bi2, c, ilen, clen, q3)) =>
            if st.out.len() + ilen > end {
                None
            } else {
                match lits(h, b, q3, ilen, st.out, bl) {
                    None => None,
                    Some((out2, bl2, q4)) =>
                        if out2.len() >= end {
                            // The copy length of the last command is ignored.
                            Some(Step::Done(St { out: out2, ring: st.ring, google: st.google }, q4))
                        } else {
                            match cmd_tail(dict, window, h, b, q4, end, St { out: out2, ring: st.ring, google: st.google },
                                           c, clen, bd) {
                                None => None,
                                Some((st2, bd2, q5)) =>
                                    if st2.out.len() >= end {
                                        Some(Step::Done(st2, q5))
                                    } else {
                                        Some(Step::Next(st2, bl2, bi2, bd2, q5))
                                    },
                            }
                        },
                }
            },
    }
}

/// Commands until the output reaches `end` (9.3, 10): the state and the
/// position after them. `bl`, `bi`, `bd` are the three categories' blocks.
pub open spec fn commands(
    dict: Seq<u8>, window: nat, h: Hdr, b: Seq<bool>, p: int, end: nat, st: St, bl: Blk, bi: Blk, bd: Blk,
) -> Option<(St, int)>
    decreases end - st.out.len(), b.len() - p, bi.left,
{
    match cmd_step(dict, window, h, b, p, end, st, bl, bi, bd) {
        None => None,
        Some(Step::Done(st2, q)) => Some((st2, q)),
        Some(Step::Next(st2, bl2, bi2, bd2, q)) =>
            if !((st2.out.len() > st.out.len())
                 || (st2.out.len() == st.out.len() && p < q <= b.len())
                 || (st2.out.len() == st.out.len() && q == p && bi2.left < bi.left)) {
                None  // not reached: a command outputs, reads, or uses up its block
            } else {
                commands(dict, window, h, b, q, end, st2, bl2, bi2, bd2)
            },
    }
}

// ------------------------------------------------------------ the stream

/// One meta-block from `p` (9.2, 9.3): the state after it, the position
/// after it, and whether it is the last.
pub open spec fn metablock(dict: Seq<u8>, window: nat, b: Seq<bool>, p: int, st: St)
    -> Option<(St, int, bool)>
{
    match getbits(b, p, 1) {
        None => None,
        Some(islast) => {
            let empty = if islast == 1 { getbits(b, p + 1, 1) } else { Some(0nat) };
            match empty {
                None => None,
                Some(e) =>
                    if e == 1 {
                        Some((st, p + 2, true))
                    } else {
                        let q = if islast == 1 { p + 2 } else { p + 1 };
                        match getbits(b, q, 2) {
                            None => None,
                            Some(m) =>
                                if m == 3 {
                                    metadata(b, q + 2, st, islast == 1)
                                } else {
                                    let nib = m + 4;
                                    match getbits(b, q + 2, 4 * nib) {
                                        None => None,
                                        Some(v) =>
                                            if nib > 4 && v / p2(4 * (nib - 1) as nat) == 0 {
                                                None
                                            } else {
                                                data(dict, window, b, q + 2 + 4 * nib, st, v + 1, islast == 1)
                                            },
                                    }
                                },
                        }
                    },
            }
        },
    }
}

/// A metadata meta-block from its reserved bit (9.2): skipped.
pub open spec fn metadata(b: Seq<bool>, p: int, st: St, last: bool) -> Option<(St, int, bool)> {
    match (getbits(b, p, 1), getbits(b, p + 1, 2)) {
        (Some(reserved), Some(nbytes)) => {
            let len = if nbytes == 0 { Some(0nat) } else {
                match getbits(b, p + 3, 8 * nbytes) {
                    None => None,
                    Some(v) => if nbytes > 1 && v / p2(8 * (nbytes - 1) as nat) == 0 { None } else { Some(v + 1) },
                }
            };
            let r = p + 3 + 8 * nbytes;
            match len {
                None => None,
                Some(n) =>
                    if reserved != 0 || !zero_fill(b, r) || align8(r) + 8 * n > b.len() {
                        None
                    } else {
                        Some((st, align8(r) + 8 * n, last))
                    },
            }
        }
        _ => None,
    }
}

/// A meta-block with data, from just after MLEN (9.2): uncompressed or
/// compressed.
pub open spec fn data(dict: Seq<u8>, window: nat, b: Seq<bool>, p: int, st: St, mlen: nat, last: bool)
    -> Option<(St, int, bool)>
{
    let unc = if last { Some(0nat) } else { getbits(b, p, 1) };
    let r = if last { p } else { p + 1 };
    match unc {
        None => None,
        Some(u) =>
            if u == 1 {
                if !zero_fill(b, r) || align8(r) + 8 * mlen > b.len() {
                    None
                } else {
                    Some((St { out: st.out + bytes_at(b, align8(r), mlen), ring: st.ring, google: st.google },
                          align8(r) + 8 * mlen, false))
                }
            } else {
                match read_hdr(b, r) {
                    None => None,
                    Some((h, r2)) =>
                        match commands(dict, window, h, b, r2, st.out.len() + mlen, st,
                                       blk0(h.cl), blk0(h.ci), blk0(h.cd)) {
                            None => None,
                            Some((st2, r3)) => Some((st2, r3, last)),
                        },
                }
            },
    }
}

/// The meta-blocks from `p` to the last, and the fill bits after it (9.2):
/// the state and the position after the stream.
pub open spec fn metablocks(dict: Seq<u8>, window: nat, b: Seq<bool>, p: int, st: St) -> Option<(St, int)>
    decreases b.len() - p,
{
    match metablock(dict, window, b, p, st) {
        None => None,
        Some((st2, q, last)) =>
            if last {
                if zero_fill(b, q) { Some((st2, align8(q))) } else { None }
            } else if q <= p || q > b.len() {
                None  // not reached: every meta-block reads its header
            } else {
                metablocks(dict, window, b, q, st2)
            },
    }
}

/// WBITS (9.1): the value and the bits it took.
pub open spec fn wbits(b: Seq<bool>) -> Option<(nat, int)> {
    match getbits(b, 0, 1) {
        None => None,
        Some(x) => if x == 0 {
            Some((16, 1))
        } else {
            match getbits(b, 1, 3) {
                None => None,
                Some(n) => if n != 0 {
                    Some((17 + n, 4))
                } else {
                    match getbits(b, 4, 3) {
                        None => None,
                        Some(m) => if m == 1 { None } else if m != 0 { Some((8 + m, 7)) } else { Some((17, 7)) },
                    }
                },
            }
        },
    }
}

/// A Brotli stream with the static dictionary `dict`: the data, the bits
/// the stream took, and whether Google's decoder accepts it.
pub open spec fn brotli(dict: Seq<u8>, b: Seq<bool>) -> Option<(Seq<u8>, nat, bool)> {
    match wbits(b) {
        None => None,
        Some((w, p)) =>
            match metablocks(dict, (p2(w) - 16) as nat, b, p,
                             St { out: Seq::empty(), ring: seq![4int, 11, 15, 16], google: true }) {
                None => None,
                Some((st, q)) => Some((st.out, q as nat, st.google)),
            },
    }
}

} // verus!
