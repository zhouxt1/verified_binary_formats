//! RFC 9649 section 3 (the WebP lossless bitstream, VP8L), as a spec
//! decoder over the stream's bits.
//!
//! The stream is `lbits(input)`: bytes LSB-first, `ReadBits(n)` values
//! LSB-first, prefix codes MSB-first (3.2, 3.7), as in DEFLATE, so the bit
//! fields and the canonical prefix codes are `vdeflate::spec`'s, and a code
//! of one symbol, read with no bits, is `vbrotli::spec::dsym`. Positions are
//! bit offsets from the start of the stream (its signature byte, 0x2f).
//!
//! `vp8l(b)` is the image (its width, height, alpha hint and ARGB pixels in
//! scan-line order), the number of bits the stream took (the rest is not
//! looked at), and a flag, `strict`, false where the stream relies on what
//! libwebp accepts and the RFC's text rules out.
//!
//! The spec rejects a stream where the RFC says to ("MUST be treated as an
//! error", "MUST indicate a corrupted bitstream", "the bitstream is
//! invalid"), where it says a tree "must be" complete, and where it gives no
//! reading. Where the RFC does not say what a decoder does, the spec is
//! libwebp 1.6.0's decoder (`src/dec/vp8l_dec.c`, `src/utils/huffman_utils.c`,
//! `src/dsp/lossless.c`), and each such place says `LIBWEBP:`. The executable
//! transcription `vwebp-tool/src/specdec.rs`, function by function, was
//! tested against libwebp before this was written (difftest/webp/README.md).
//!
//! * A prefix code of two or more symbols must be complete; a code of one
//!   symbol is read with no bits, whatever its length (LIBWEBP; the RFC
//!   gives it length 1: `strict` is false otherwise); no symbols at all is
//!   invalid.
//! * A simple code's symbol past the alphabet is dropped (LIBWEBP; `strict`
//!   is false).
//! * `max_symbol` counts code length code symbols read, a repeat as one
//!   (LIBWEBP); a repeat past the alphabet is invalid.
//! * A transform type twice is invalid ("allowed to be used only once").
//! * A color cache index of bits outside 1..11 is invalid (MUST).
//! * An LZ77 copy from before the first pixel or past the last is invalid
//!   (LIBWEBP).
//! * Predictor modes are a green value's low 4 bits; 14 and 15 are mode 0
//!   (LIBWEBP; the RFC has 14 modes).
//! * A color index past the color table is transparent black (the RFC's
//!   "should").
//! * The color cache hash is taken mod 2^32 (LIBWEBP).
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::{getbits, complete};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbrotli::spec::{nnz, first_nz, dsym};

verus! {

// ------------------------------------------------------------- pixels

/// The channels of an ARGB pixel: alpha in bits 31..24, red 23..16, green
/// 15..8, blue 7..0 (3.2).
pub open spec fn alpha(c: u32) -> int { (c >> 24u32) as int }
pub open spec fn red(c: u32) -> int { ((c >> 16u32) & 0xffu32) as int }
pub open spec fn green(c: u32) -> int { ((c >> 8u32) & 0xffu32) as int }
pub open spec fn blue(c: u32) -> int { (c & 0xffu32) as int }

/// A channel value mod 256.
pub open spec fn byte(x: int) -> u32 { (x % 256) as u32 }

/// The pixel of four channel values, each taken mod 256.
pub open spec fn argb(a: int, r: int, g: int, b: int) -> u32 {
    (byte(a) << 24u32) | (byte(r) << 16u32) | (byte(g) << 8u32) | byte(b)
}

/// Channel by channel sum, mod 256 (`PredictorTransformOutput`, and the
/// color table's deltas, 3.5.4).
pub open spec fn add_pixels(a: u32, b: u32) -> u32 {
    argb(alpha(a) + alpha(b), red(a) + red(b), green(a) + green(b), blue(a) + blue(b))
}

/// `(num + den - 1) / den` (`DIV_ROUND_UP`, 3.5.1).
pub open spec fn div_round_up(num: nat, den: nat) -> nat {
    if den == 0 { 0 } else { ((num + den - 1) / (den as int)) as nat }
}

// --------------------------------------------------------- prefix codes

/// Whether a decoder takes the code of lengths `lens` (3.7.2.1): `None` if
/// not, else whether the RFC's text does too. Two or more symbols must be
/// "a complete binary tree". A single symbol is one ("a single leaf node is
/// considered a complete binary tree"), which the RFC gives length 1 and
/// LIBWEBP takes at any length (BuildHuffmanTable); it is read with no bits
/// (`dsym`). No symbols is invalid (LIBWEBP; the RFC codes an empty code as
/// one of symbol 0).
pub open spec fn code_ok(lens: Seq<u8>) -> Option<bool> {
    let n = nnz(lens, lens.len() as int);
    if n == 0 {
        None
    } else if n == 1 {
        Some(lens[first_nz(lens, 0)] == 1)
    } else if complete(lens) {
        Some(true)
    } else {
        None
    }
}

/// `code_lengths[s] = 1` of a simple code (3.7.2.1.1). LIBWEBP drops a
/// symbol past the alphabet (the second symbol is 8 bits; the distance
/// alphabet has 40).
pub open spec fn set_one(lens: Seq<u8>, s: nat) -> Seq<u8> {
    if s < lens.len() { lens.update(s as int, 1u8) } else { lens }
}

/// A simple code length code (3.7.2.1.1), from just after its first bit:
/// the code lengths, the position after, and whether every symbol was in
/// the alphabet.
pub open spec fn simple_code(b: Seq<bool>, p: int, asize: nat) -> Option<(Seq<u8>, int, bool)> {
    match getbits(b, p, 1) {
        None => None,
        Some(ns) => match getbits(b, p + 1, 1) {
            None => None,
            Some(first8) => {
                let nb: nat = if first8 == 1 { 8 } else { 1 };
                match getbits(b, p + 2, nb) {
                    None => None,
                    Some(s0) => {
                        let z = Seq::new(asize, |_i: int| 0u8);
                        let q = p + 2 + nb;
                        if ns == 0 {
                            Some((set_one(z, s0), q, s0 < asize))
                        } else {
                            match getbits(b, q, 8) {
                                None => None,
                                Some(s1) => Some((set_one(set_one(z, s0), s1), q + 8, s0 < asize && s1 < asize)),
                            }
                        }
                    },
                }
            },
        },
    }
}

/// `kCodeLengthCodeOrder` (3.7.2.1.2).
pub open spec fn cl_order() -> Seq<nat> {
    seq![17nat, 18, 0, 1, 2, 3, 4, 5, 16, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
}

/// The code length code lengths from the `i`-th of `n` (3 bits each, in
/// `cl_order`) into `acc`.
pub open spec fn read_cl(b: Seq<bool>, p: int, i: nat, n: nat, acc: Seq<u8>) -> Option<(Seq<u8>, int)>
    decreases n - i,
{
    if i >= n || i >= 19 {
        Some((acc, p))
    } else {
        match getbits(b, p, 3) {
            None => None,
            Some(v) => read_cl(b, p + 3, i + 1, n, acc.update(cl_order()[i as int] as int, v as u8)),
        }
    }
}

/// Code lengths (3.7.2.1.2) with the code length code `cl`: `acc` has them
/// for the symbols before `sym`, `left` more code length code symbols may be
/// read (`max_symbol`, LIBWEBP: a repeat counts as one), `prev` is the last
/// nonzero length (8 at first). They stop when every symbol has one or
/// `left` is used up; the rest stay 0.
pub open spec fn read_lens(cl: Seq<u8>, b: Seq<bool>, p: int, asize: nat, acc: Seq<u8>, sym: nat, left: nat, prev: nat)
    -> Option<(Seq<u8>, int)>
    decreases asize - sym,
{
    if sym >= asize || left == 0 {
        Some((acc, p))
    } else {
        match dsym(cl, b, p) {
            None => None,
            Some((c, q)) =>
                if c < 16 {
                    read_lens(cl, b, q, asize, acc.update(sym as int, c as u8), sym + 1, (left - 1) as nat,
                              if c != 0 { c } else { prev })
                } else if c > 18 {
                    None  // not reached: the code length code has 19 symbols
                } else {
                    // 16 repeats the last nonzero length 3..6 times, 17 zero
                    // 3..10 times, 18 zero 11..138 times
                    let eb: nat = if c == 16 { 2 } else if c == 17 { 3 } else { 7 };
                    let off: nat = if c == 18 { 11 } else { 3 };
                    let v: nat = if c == 16 { prev } else { 0 };
                    match getbits(b, q, eb) {
                        None => None,
                        Some(e) => {
                            let r = e + off;
                            if sym + r > asize {
                                None  // LIBWEBP: a repeat past the alphabet
                            } else {
                                let acc2 = Seq::new(asize, |j: int| if sym <= j < sym + r { v as u8 } else { acc[j] });
                                read_lens(cl, b, q + eb, asize, acc2, sym + r, (left - 1) as nat, prev)
                            }
                        },
                    }
                },
        }
    }
}

/// A normal code length code (3.7.2.1.2), from just after its first bit.
pub open spec fn normal_code(b: Seq<bool>, p: int, asize: nat) -> Option<(Seq<u8>, int, bool)> {
    match getbits(b, p, 4) {
        None => None,
        Some(n) => match read_cl(b, p + 4, 0, n + 4, Seq::new(19, |_i: int| 0u8)) {
            None => None,
            Some((cl, q)) => match code_ok(cl) {
                None => None,
                Some(st) => match getbits(b, q, 1) {
                    None => None,
                    Some(use_len) => {
                        let zeros = Seq::new(asize, |_i: int| 0u8);
                        if use_len == 0 {
                            match read_lens(cl, b, q + 1, asize, zeros, 0, asize, 8) {
                                None => None,
                                Some((lens, r)) => Some((lens, r, st)),
                            }
                        } else {
                            match getbits(b, q + 1, 3) {
                                None => None,
                                Some(k) => {
                                    let nb = 2 + 2 * k;
                                    match getbits(b, q + 4, nb) {
                                        None => None,
                                        Some(m) =>
                                            if m + 2 > asize {
                                                None  // "the bitstream is invalid"
                                            } else {
                                                match read_lens(cl, b, q + 4 + nb, asize, zeros, 0, m + 2, 8) {
                                                    None => None,
                                                    Some((lens, r)) => Some((lens, r, st)),
                                                }
                                            },
                                    }
                                },
                            }
                        }
                    },
                },
            },
        },
    }
}

/// A prefix code over an alphabet of `asize` symbols (3.7.2.1): its code
/// lengths, the position after it, and `strict`.
pub open spec fn read_code(b: Seq<bool>, p: int, asize: nat) -> Option<(Seq<u8>, int, bool)> {
    let r = match getbits(b, p, 1) {
        None => None,
        Some(simple) => if simple == 1 { simple_code(b, p + 1, asize) } else { normal_code(b, p + 1, asize) },
    };
    match r {
        None => None,
        Some((lens, q, st)) => match code_ok(lens) {
            None => None,
            Some(st2) => Some((lens, q, st && st2)),
        },
    }
}

/// The alphabet of the `j`-th code of a prefix code group (3.7.2.2):
/// green, length prefixes and cache indexes; red; blue; alpha; distance.
pub open spec fn asize(j: nat, cache_bits: nat) -> nat {
    if j == 0 { 256 + 24 + (if cache_bits > 0 { p2(cache_bits) } else { 0 }) } else if j < 4 { 256 } else { 40 }
}

/// The codes of a prefix code group from the `acc.len()`-th.
pub open spec fn read_codes(b: Seq<bool>, p: int, cache_bits: nat, acc: Seq<Seq<u8>>, st: bool)
    -> Option<(Seq<Seq<u8>>, int, bool)>
    decreases 5 - acc.len(),
{
    if acc.len() >= 5 {
        Some((acc, p, st))
    } else {
        match read_code(b, p, asize(acc.len(), cache_bits)) {
            None => None,
            Some((lens, q, st2)) => read_codes(b, q, cache_bits, acc.push(lens), st && st2),
        }
    }
}

/// `n` prefix code groups from the `acc.len()`-th.
pub open spec fn read_groups(b: Seq<bool>, p: int, cache_bits: nat, n: nat, acc: Seq<Seq<Seq<u8>>>, st: bool)
    -> Option<(Seq<Seq<Seq<u8>>>, int, bool)>
    decreases n - acc.len(),
{
    if acc.len() >= n {
        Some((acc, p, st))
    } else {
        match read_codes(b, p, cache_bits, Seq::empty(), true) {
            None => None,
            Some((g, q, st2)) => read_groups(b, q, cache_bits, n, acc.push(g), st && st2),
        }
    }
}

// ------------------------------------------------------------ image data

/// LZ77 prefix coding (3.6.2.2): the value of prefix symbol `s` and its
/// extra bits at `p`.
pub open spec fn prefix_value(b: Seq<bool>, p: int, s: nat) -> Option<(nat, int)> {
    if s < 4 {
        Some((s + 1, p))
    } else {
        let eb = ((s - 2) / 2) as nat;
        let off = (2 + s % 2) * p2(eb);
        match getbits(b, p, eb) {
            None => None,
            Some(e) => Some(((off + e + 1) as nat, p + eb)),
        }
    }
}

/// Figure 20: the (xi, yi) of distance codes 1..120.
pub open spec fn dist_map() -> Seq<(int, int)> {
    seq![
        (0int, 1int), (1, 0), (1, 1), (-1, 1), (0, 2), (2, 0), (1, 2), (-1, 2), (2, 1), (-2, 1), (2, 2), (-2, 2),
        (0, 3), (3, 0), (1, 3), (-1, 3), (3, 1), (-3, 1), (2, 3), (-2, 3), (3, 2), (-3, 2), (0, 4), (4, 0),
        (1, 4), (-1, 4), (4, 1), (-4, 1), (3, 3), (-3, 3), (2, 4), (-2, 4), (4, 2), (-4, 2), (0, 5), (3, 4),
        (-3, 4), (4, 3), (-4, 3), (5, 0), (1, 5), (-1, 5), (5, 1), (-5, 1), (2, 5), (-2, 5), (5, 2), (-5, 2),
        (4, 4), (-4, 4), (3, 5), (-3, 5), (5, 3), (-5, 3), (0, 6), (6, 0), (1, 6), (-1, 6), (6, 1), (-6, 1),
        (2, 6), (-2, 6), (6, 2), (-6, 2), (4, 5), (-4, 5), (5, 4), (-5, 4), (3, 6), (-3, 6), (6, 3), (-6, 3),
        (0, 7), (7, 0), (1, 7), (-1, 7), (5, 5), (-5, 5), (7, 1), (-7, 1), (4, 6), (-4, 6), (6, 4), (-6, 4),
        (2, 7), (-2, 7), (7, 2), (-7, 2), (3, 7), (-3, 7), (7, 3), (-7, 3), (5, 6), (-5, 6), (6, 5), (-6, 5),
        (8, 0), (4, 7), (-4, 7), (7, 4), (-7, 4), (8, 1), (8, 2), (6, 6), (-6, 6), (8, 3), (5, 7), (-5, 7),
        (7, 5), (-7, 5), (8, 4), (6, 7), (-6, 7), (7, 6), (-7, 6), (8, 5), (7, 7), (-7, 7), (8, 6), (8, 7)
    ]
}

/// A distance code (at least 1) as a distance in scan-line order, in an
/// image `w` wide (3.6.2.2.1).
pub open spec fn plane_dist(dcode: nat, w: nat) -> nat {
    if dcode > 120 {
        (dcode - 120) as nat
    } else if dcode == 0 {
        1  // not reached: prefix values are at least 1
    } else {
        let (xi, yi) = dist_map()[dcode - 1];
        let d = xi + yi * w;
        if d < 1 { 1 } else { d as nat }
    }
}

/// The color cache slot of color `c`, for a cache of `2^cache_bits`
/// entries (3.6.2.3). LIBWEBP takes the product mod 2^32 (VP8LHashPix).
pub open spec fn cache_key(c: u32, cache_bits: nat) -> int {
    ((c as nat * 0x1e35a7bdnat) % 0x1_0000_0000nat) as int / (p2((32 - cache_bits) as nat) as int)
}

/// The pixels so far and the color cache ("all entries ... set to zero" at
/// first, 3.6.2.3).
pub struct St {
    pub px: Seq<u32>,
    pub cache: Seq<u32>,
}

pub open spec fn st0(cache_bits: nat) -> St {
    St { px: Seq::empty(), cache: Seq::new(if cache_bits > 0 { p2(cache_bits) } else { 0 }, |_i: int| 0u32) }
}

/// One more pixel, inserted into the cache ("inserting every pixel, be it
/// produced by backward referencing or as literals, into the cache in the
/// order they appear").
pub open spec fn put(st: St, c: u32, cache_bits: nat) -> St {
    St {
        px: st.px.push(c),
        cache: if cache_bits > 0 { st.cache.update(cache_key(c, cache_bits), c) } else { st.cache },
    }
}

/// `n` pixels copied from `d` back, one at a time (so a copy may overlap
/// its own output).
pub open spec fn copy_px(st: St, d: nat, n: nat, cache_bits: nat) -> St
    decreases n,
{
    if n == 0 {
        st
    } else {
        copy_px(put(st, st.px[st.px.len() - d], cache_bits), d, (n - 1) as nat, cache_bits)
    }
}

/// Which prefix code group each pixel uses (3.7.2.2): one everywhere, or
/// the one an entropy image `ew` tiles wide names for the tile, each tile
/// `2^bits` square.
pub enum Meta {
    One,
    Tiles { bits: nat, ew: nat, img: Seq<u32> },
}

/// The meta prefix code of an entropy image pixel: its red and green.
pub open spec fn meta_code(c: u32) -> int { ((c >> 8u32) & 0xffffu32) as int }

pub open spec fn group_at(m: Meta, x: nat, y: nat) -> int {
    match m {
        Meta::One => 0,
        Meta::Tiles { bits, ew, img } => meta_code(img[((y / p2(bits)) * ew + x / p2(bits)) as int]),
    }
}

/// One pixel, a copy, or a cache hit (3.7.2.3), in an image `w` wide of
/// `total` pixels, with the groups `gs`.
pub open spec fn pix_step(b: Seq<bool>, p: int, w: nat, total: nat, cache_bits: nat,
                          gs: Seq<Seq<Seq<u8>>>, m: Meta, st: St) -> Option<(St, int)> {
    let i = st.px.len();
    let g = gs[group_at(m, (i % w) as nat, (i / w) as nat)];
    match dsym(g[0], b, p) {
        None => None,
        Some((s, q)) =>
            if s < 256 {
                match dsym(g[1], b, q) {
                    None => None,
                    Some((r, q1)) => match dsym(g[2], b, q1) {
                        None => None,
                        Some((bl, q2)) => match dsym(g[3], b, q2) {
                            None => None,
                            Some((a, q3)) => Some((put(st, argb(a as int, r as int, s as int, bl as int), cache_bits), q3)),
                        },
                    },
                }
            } else if s < 256 + 24 {
                match prefix_value(b, q, (s - 256) as nat) {
                    None => None,
                    Some((len, q1)) => match dsym(g[4], b, q1) {
                        None => None,
                        Some((ds, q2)) => match prefix_value(b, q2, ds) {
                            None => None,
                            Some((dcode, q3)) => {
                                let d = plane_dist(dcode, w);
                                // LIBWEBP: from before the first pixel or
                                // past the last is invalid
                                if d > i || len > total - i {
                                    None
                                } else {
                                    Some((copy_px(st, d, len, cache_bits), q3))
                                }
                            },
                        },
                    },
                }
            } else {
                let k = s - (256 + 24);
                if k >= st.cache.len() {
                    None  // not reached: the green alphabet ends with the cache
                } else {
                    Some((put(st, st.cache[k], cache_bits), q))
                }
            },
    }
}

/// The pixels from `st` on, until there are `total` (3.6.2).
pub open spec fn decode_pixels(b: Seq<bool>, p: int, w: nat, total: nat, cache_bits: nat,
                               gs: Seq<Seq<Seq<u8>>>, m: Meta, st: St) -> Option<(Seq<u32>, int)>
    decreases total - st.px.len(),
{
    if st.px.len() >= total {
        Some((st.px, p))
    } else {
        match pix_step(b, p, w, total, cache_bits, gs, m, st) {
            None => None,
            Some((st2, q)) =>
                if st2.px.len() <= st.px.len() || st2.px.len() > total {
                    None  // not reached: a step adds 1 to total - i pixels
                } else {
                    decode_pixels(b, q, w, total, cache_bits, gs, m, st2)
                },
        }
    }
}

/// color-cache-info (3.6.2.3, 3.8.3): 0, or 1 and 4 bits in 1..11.
pub open spec fn read_cache_bits(b: Seq<bool>, p: int) -> Option<(nat, int)> {
    match getbits(b, p, 1) {
        None => None,
        Some(x) => if x == 0 {
            Some((0, p + 1))
        } else {
            match getbits(b, p + 1, 4) {
                None => None,
                Some(cb) => if 1 <= cb <= 11 { Some((cb, p + 5)) } else { None },
            }
        },
    }
}

/// An entropy-coded image of `w` x `h` (3.8.3): the sub-resolution images
/// and the color table. Its own color cache, one prefix code group.
pub open spec fn entropy_coded_image(b: Seq<bool>, p: int, w: nat, h: nat) -> Option<(Seq<u32>, int, bool)> {
    match read_cache_bits(b, p) {
        None => None,
        Some((cb, q)) => match read_codes(b, q, cb, Seq::empty(), true) {
            None => None,
            Some((g, q2, st)) => match decode_pixels(b, q2, w, w * h, cb, seq![g], Meta::One, st0(cb)) {
                None => None,
                Some((px, q3)) => Some((px, q3, st)),
            },
        },
    }
}

/// The largest meta prefix code of the first `n` pixels of an entropy image.
pub open spec fn max_meta(img: Seq<u32>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        let m = max_meta(img, n - 1);
        if meta_code(img[n - 1]) > m { meta_code(img[n - 1]) } else { m }
    }
}

/// The spatially-coded image of `w` x `h` (3.8.3): the ARGB image's data,
/// with meta prefix codes. As many groups as the largest meta prefix code
/// plus one, each read and valid whether a tile uses it or not (3.7.2.2.2;
/// LIBWEBP reads unused ones and checks them the same).
pub open spec fn spatially_coded_image(b: Seq<bool>, p: int, w: nat, h: nat) -> Option<(Seq<u32>, int, bool)> {
    match read_cache_bits(b, p) {
        None => None,
        Some((cb, q)) => match getbits(b, q, 1) {
            None => None,
            Some(use_meta) => {
                let mh: Option<(Meta, nat, int, bool)> = if use_meta == 0 {
                    Some((Meta::One, 1nat, q + 1, true))
                } else {
                    match getbits(b, q + 1, 3) {
                        None => None,
                        Some(pb) => {
                            let bits = pb + 2;
                            let ew = div_round_up(w, p2(bits));
                            match entropy_coded_image(b, q + 4, ew, div_round_up(h, p2(bits))) {
                                None => None,
                                Some((img, q2, st)) =>
                                    Some((Meta::Tiles { bits, ew, img }, (max_meta(img, img.len() as int) + 1) as nat, q2, st)),
                            }
                        },
                    }
                };
                match mh {
                    None => None,
                    Some((m, ngroups, q2, st)) => match read_groups(b, q2, cb, ngroups, Seq::empty(), true) {
                        None => None,
                        Some((gs, q3, st2)) => match decode_pixels(b, q3, w, w * h, cb, gs, m, st0(cb)) {
                            None => None,
                            Some((px, q4)) => Some((px, q4, st && st2)),
                        },
                    },
                }
            },
        },
    }
}

// -------------------------------------------------------------- transforms

/// A transform (3.5), with what its inverse needs: the tile size bits, the
/// image's width when it was read, and its image; for color indexing the
/// width bits, the width before bundling, the color table (deltas undone,
/// zero past its size up to 2^(8 >> width bits) entries).
pub enum Tr {
    Predictor { bits: nat, w: nat, img: Seq<u32> },
    Color { bits: nat, w: nat, img: Seq<u32> },
    SubtractGreen,
    ColorIndexing { wb: nat, w: nat, pal: Seq<u32> },
}

pub open spec fn tr_type(t: Tr) -> nat {
    match t {
        Tr::Predictor { .. } => 0,
        Tr::Color { .. } => 1,
        Tr::SubtractGreen => 2,
        Tr::ColorIndexing { .. } => 3,
    }
}

/// Some transform of `ts` is of type `ty`.
pub open spec fn seen(ts: Seq<Tr>, ty: nat) -> bool {
    exists|k: int| 0 <= k < ts.len() && tr_type(#[trigger] ts[k]) == ty
}

/// The color table's first `k + 1` colors, deltas undone (3.5.4: "adding the
/// previous color component values by each ARGB component separately").
pub open spec fn palette_at(deltas: Seq<u32>, k: int) -> u32
    decreases k,
{
    if k <= 0 { deltas[0] } else { add_pixels(palette_at(deltas, k - 1), deltas[k]) }
}

/// Table 3: how many bits of a bundled pixel each index takes.
pub open spec fn width_bits(n: nat) -> nat {
    if n > 16 { 0 } else if n > 4 { 1 } else if n > 2 { 2 } else { 3 }
}

/// The color table, padded with transparent black to every index a
/// bundled pixel can hold ("should be set to 0x00000000").
pub open spec fn palette(deltas: Seq<u32>, wb: nat) -> Seq<u32> {
    Seq::new(p2((8nat / p2(wb)) as nat), |k: int| if k < deltas.len() { palette_at(deltas, k) } else { 0u32 })
}

/// The transforms from the `ts.len()`-th (3.5, 3.8.2), for an image `w`
/// wide (after the color indexing ones so far) and `h` high: all of them,
/// the width the image data then has, the position after the 0 that ends
/// them, and `strict`. There are four types, each allowed once, so a fifth
/// transform is a repeat.
pub open spec fn read_transforms(b: Seq<bool>, p: int, w: nat, h: nat, ts: Seq<Tr>, st: bool)
    -> Option<(Seq<Tr>, nat, int, bool)>
    decreases 4 - ts.len(),
{
    match getbits(b, p, 1) {
        None => None,
        Some(more) => if more == 0 {
            Some((ts, w, p + 1, st))
        } else if ts.len() >= 4 {
            None  // a type twice
        } else {
            match getbits(b, p + 1, 2) {
                None => None,
                Some(ty) =>
                    if seen(ts, ty) {
                        None  // "allowed to be used only once"
                    } else if ty == 2 {
                        read_transforms(b, p + 3, w, h, ts.push(Tr::SubtractGreen), st)
                    } else if ty == 3 {
                        match getbits(b, p + 3, 8) {
                            None => None,
                            Some(n1) => {
                                let n = n1 + 1;
                                let wb = width_bits(n);
                                match entropy_coded_image(b, p + 11, n, 1) {
                                    None => None,
                                    Some((deltas, q, st2)) =>
                                        read_transforms(b, q, div_round_up(w, p2(wb)), h,
                                            ts.push(Tr::ColorIndexing { wb, w, pal: palette(deltas, wb) }), st && st2),
                                }
                            },
                        }
                    } else {
                        match getbits(b, p + 3, 3) {
                            None => None,
                            Some(sb) => {
                                let bits = sb + 2;
                                match entropy_coded_image(b, p + 6, div_round_up(w, p2(bits)), div_round_up(h, p2(bits))) {
                                    None => None,
                                    Some((img, q, st2)) => {
                                        let t = if ty == 0 { Tr::Predictor { bits, w, img } } else { Tr::Color { bits, w, img } };
                                        read_transforms(b, q, w, h, ts.push(t), st && st2)
                                    },
                                }
                            },
                        }
                    },
            }
        },
    }
}

// ----------------------------------------------------- inverse transforms

/// `Average2`, channel by channel.
pub open spec fn avg(x: int, y: int) -> int { (x + y) / 2 }

pub open spec fn average2(a: u32, b: u32) -> u32 {
    argb(avg(alpha(a), alpha(b)), avg(red(a), red(b)), avg(green(a), green(b)), avg(blue(a), blue(b)))
}

pub open spec fn abs(x: int) -> int { if x < 0 { -x } else { x } }

/// `Select`: of L and T, the one nearer (in Manhattan distance over the
/// channels) to L + T - TL; T on a tie.
pub open spec fn select(l: u32, t: u32, tl: u32) -> u32 {
    let pl = abs(alpha(t) - alpha(tl)) + abs(red(t) - red(tl)) + abs(green(t) - green(tl)) + abs(blue(t) - blue(tl));
    let pt = abs(alpha(l) - alpha(tl)) + abs(red(l) - red(tl)) + abs(green(l) - green(tl)) + abs(blue(l) - blue(tl));
    if pl < pt { l } else { t }
}

pub open spec fn clamp(a: int) -> int { if a < 0 { 0 } else if a > 255 { 255 } else { a } }

/// C's `/ 2`, which truncates toward zero (int's `/` floors).
pub open spec fn cdiv2(x: int) -> int { if x >= 0 { x / 2 } else { -((-x) / 2) } }

pub open spec fn clamp_add_subtract_full(a: u32, b: u32, c: u32) -> u32 {
    argb(clamp(alpha(a) + alpha(b) - alpha(c)), clamp(red(a) + red(b) - red(c)),
         clamp(green(a) + green(b) - green(c)), clamp(blue(a) + blue(b) - blue(c)))
}

pub open spec fn cash(a: int, b: int) -> int { clamp(a + cdiv2(a - b)) }

pub open spec fn clamp_add_subtract_half(a: u32, b: u32) -> u32 {
    argb(cash(alpha(a), alpha(b)), cash(red(a), red(b)), cash(green(a), green(b)), cash(blue(a), blue(b)))
}

/// Table 2's modes; 14 and 15 are mode 0 (LIBWEBP).
pub open spec fn predict(mode: int, l: u32, t: u32, tr: u32, tl: u32) -> u32 {
    if mode == 1 { l }
    else if mode == 2 { t }
    else if mode == 3 { tr }
    else if mode == 4 { tl }
    else if mode == 5 { average2(average2(l, tr), t) }
    else if mode == 6 { average2(l, tl) }
    else if mode == 7 { average2(l, t) }
    else if mode == 8 { average2(tl, t) }
    else if mode == 9 { average2(t, tr) }
    else if mode == 10 { average2(average2(l, tl), average2(t, tr)) }
    else if mode == 11 { select(l, t, tl) }
    else if mode == 12 { clamp_add_subtract_full(l, t, tl) }
    else if mode == 13 { clamp_add_subtract_half(average2(l, t), tl) }
    else { 0xff000000u32 }
}

/// The tile of pixel (x, y) in a sub-resolution image of `2^bits` tiles,
/// for an image `w` wide.
pub open spec fn tile(img: Seq<u32>, bits: nat, w: nat, x: nat, y: nat) -> u32 {
    img[((y / p2(bits)) * div_round_up(w, p2(bits)) + x / p2(bits)) as int]
}

/// The prediction for pixel `i` of an image `w` wide, from the pixels
/// before it (`out`): black for the first; L on the top row; T in the left
/// column; else the tile's mode, the green value's low 4 bits (LIBWEBP). The
/// rightmost column's TR is the current row's first pixel, which in
/// scan-line order is the one after T (3.5.1).
pub open spec fn prediction(bits: nat, w: nat, img: Seq<u32>, out: Seq<u32>, i: int) -> u32 {
    let x = (i % w as int) as nat;
    let y = (i / w as int) as nat;
    if i == 0 {
        0xff000000u32
    } else if y == 0 {
        out[i - 1]
    } else if x == 0 {
        out[i - w]
    } else {
        predict(green(tile(img, bits, w, x, y)) % 16, out[i - 1], out[i - w], out[i - w + 1], out[i - w - 1])
    }
}

/// The inverse predictor transform, pixel by pixel from `out.len()`.
pub open spec fn inv_predictor(bits: nat, w: nat, img: Seq<u32>, px: Seq<u32>, out: Seq<u32>) -> Seq<u32>
    decreases px.len() - out.len(),
{
    if out.len() >= px.len() {
        out
    } else {
        let i = out.len() as int;
        inv_predictor(bits, w, img, px, out.push(add_pixels(px[i], prediction(bits, w, img, out, i))))
    }
}

/// An unsigned byte as a signed one (3.5.2).
pub open spec fn sbyte(v: int) -> int { if v >= 128 { v - 256 } else { v } }

/// `ColorTransformDelta`: `(t * c) >> 5`, an arithmetic shift (int's `/`
/// by a positive number floors); only its low 8 bits are used.
pub open spec fn ct_delta(t: int, c: int) -> int { (sbyte(t) * sbyte(c)) / 32 }

/// The inverse color transform of one pixel, with the element `e` (alpha
/// 255, red red_to_blue, green green_to_blue, blue green_to_red).
pub open spec fn inv_color_px(c: u32, e: u32) -> u32 {
    let nr = (red(c) + ct_delta(blue(e), green(c))) % 256;
    let nb = (blue(c) + ct_delta(green(e), green(c)) + ct_delta(red(e), nr)) % 256;
    argb(alpha(c), nr, green(c), nb)
}

pub open spec fn inv_color(bits: nat, w: nat, img: Seq<u32>, px: Seq<u32>) -> Seq<u32> {
    Seq::new(px.len(), |i: int| inv_color_px(px[i], tile(img, bits, w, (i % w as int) as nat, (i / w as int) as nat)))
}

/// `AddGreenToBlueAndRed`.
pub open spec fn inv_subtract_green(px: Seq<u32>) -> Seq<u32> {
    Seq::new(px.len(), |i: int| argb(alpha(px[i]), red(px[i]) + green(px[i]), green(px[i]), blue(px[i]) + green(px[i])))
}

/// The color index of pixel (x, y) of an image `w` wide whose pixels were
/// bundled `2^wb` to a pixel: the `x % 2^wb`-th field of `8 >> wb` bits of
/// the bundled pixel's green, from the least significant (3.5.4).
pub open spec fn color_index(wb: nat, w: nat, px: Seq<u32>, x: nat, y: nat) -> int {
    let g = green(px[(y * div_round_up(w, p2(wb)) + x / p2(wb)) as int]);
    if wb == 0 {
        g
    } else {
        let nb = (8nat / p2(wb)) as nat;
        (g / (p2((x % p2(wb)) * nb) as int)) % (p2(nb) as int)
    }
}

pub open spec fn inv_color_indexing(wb: nat, w: nat, h: nat, pal: Seq<u32>, px: Seq<u32>) -> Seq<u32> {
    Seq::new(w * h, |i: int| pal[color_index(wb, w, px, (i % w as int) as nat, (i / w as int) as nat)])
}

pub open spec fn inverse(t: Tr, h: nat, px: Seq<u32>) -> Seq<u32> {
    match t {
        Tr::Predictor { bits, w, img } => inv_predictor(bits, w, img, px, Seq::empty()),
        Tr::Color { bits, w, img } => inv_color(bits, w, img, px),
        Tr::SubtractGreen => inv_subtract_green(px),
        Tr::ColorIndexing { wb, w, pal } => inv_color_indexing(wb, w, h, pal, px),
    }
}

/// The inverses of the first `k` transforms, last one first ("in the
/// reverse order that they are read from the bitstream").
pub open spec fn inverses(ts: Seq<Tr>, k: int, h: nat, px: Seq<u32>) -> Seq<u32>
    decreases k,
{
    if k <= 0 { px } else { inverses(ts, k - 1, h, inverse(ts[k - 1], h, px)) }
}

// -------------------------------------------------------------- the image

pub struct Image {
    pub w: nat,
    pub h: nat,
    pub alpha_hint: bool,
    pub px: Seq<u32>,
}

/// A VP8L bitstream (3.4 on): the signature 0x2f, the width and height (14
/// bits each, less 1), the alpha hint, the version (MUST be 0), the
/// transforms, the image data, and the inverse transforms. The image, the
/// bits the stream took, and `strict`.
pub open spec fn vp8l(b: Seq<bool>) -> Option<(Image, nat, bool)> {
    match (getbits(b, 0, 8), getbits(b, 8, 14), getbits(b, 22, 14), getbits(b, 36, 1), getbits(b, 37, 3)) {
        (Some(sig), Some(w1), Some(h1), Some(a), Some(ver)) =>
            if sig != 0x2f || ver != 0 {
                None
            } else {
                let w = w1 + 1;
                let h = h1 + 1;
                match read_transforms(b, 40, w, h, Seq::empty(), true) {
                    None => None,
                    Some((ts, dw, p, st)) => match spatially_coded_image(b, p, dw, h) {
                        None => None,
                        Some((px, q, st2)) =>
                            Some((Image { w, h, alpha_hint: a == 1, px: inverses(ts, ts.len() as int, h, px) },
                                  q as nat, st && st2)),
                    },
                }
            },
        _ => None,
    }
}

} // verus!
