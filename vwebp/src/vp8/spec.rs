//! A VP8 key frame (RFC 6386), the image of a lossy WebP file, as a spec
//! decoder over the frame's bytes.
//!
//! RFC 6386 section 1: "The bitstream is defined by the reference source
//! code and not this narrative." This is that code (section 20, "dixie"),
//! restricted to key frames: the executable transcription
//! `vwebp-tool/src/vp8spec.rs`, function by function, which was tested
//! against the reference decoder itself (built from the RFC's text) and
//! against libwebp before this was written (difftest/webp/README.md, "Lossy
//! images"). Where dixie keeps state in fixed-width integers the spec does
//! too (the bool decoder's `unsigned int`s, coefficients in `short`s, the
//! transforms' first passes in `short`s), with the C semantics.
//!
//! It is written operationally, in dixie's order of work, so that the
//! decoder can follow it step by step:
//!
//! 1. the frame header and the first partition's header (`header`);
//! 2. every macroblock's modes, from the first partition (`modes`);
//! 3. macroblock by macroblock, in raster order, its tokens from its row's
//!    partition and its reconstruction (`decode_mbs`): intra prediction
//!    from the pixels reconstructed so far, plus the inverse transforms;
//! 4. the loop filter over the whole frame, macroblock by macroblock
//!    (`loop_filter`); dixie filters row r - 1 after predicting row r,
//!    which gives the same planes: prediction reads only unfiltered
//!    pixels, and a row's filter reads nothing below it.
//!
//! Planes are rows of pixels (`Seq<Seq<u8>>`), of whole macroblocks; the
//! frame is their top left `w` x `h` (chroma `(w+1)/2` x `(h+1)/2`).
use vstd::prelude::*;
use super::tab::*;

verus! {

// ------------------------------------------------------ the bool decoder

/// dixie's `struct bool_decoder` (20.2): the next byte `pos` of the
/// partition, where it ends (0 for a partition of fewer than 2 bytes,
/// which init_bool_decoder does not read at all), and the three
/// `unsigned int`s.
pub struct BState {
    pub pos: nat,
    pub end: nat,
    pub range: u32,
    pub value: u32,
    pub bit_count: u32,
}

/// init_bool_decoder.
pub open spec fn b_init(buf: Seq<u8>) -> BState {
    if buf.len() >= 2 {
        BState { pos: 2, end: buf.len(), range: 255, value: ((buf[0] as u32) << 8u32) | (buf[1] as u32), bit_count: 0 }
    } else {
        BState { pos: 0, end: 0, range: 255, value: 0, bit_count: 0 }
    }
}

/// The shifts at the end of bool_get: while `range < 128`, shift `value`
/// and `range` left (`value` is 32 bits: what leaves the top is lost),
/// and every 8 shifts take in the next byte, if there is one.
pub open spec fn b_norm(buf: Seq<u8>, s: BState) -> BState
    decreases 256 - s.range,
{
    if s.range >= 128 || s.range == 0 {
        s
    } else {
        let v = s.value << 1u32;
        let r = (s.range * 2) as u32;
        let bc = s.bit_count + 1;
        let s2 = if bc == 8 {
            if s.pos < s.end && s.pos < buf.len() {
                BState { pos: s.pos + 1, end: s.end, range: r, value: v | (buf[s.pos as int] as u32), bit_count: 0 }
            } else {
                BState { pos: s.pos, end: s.end, range: r, value: v, bit_count: 0 }
            }
        } else {
            BState { pos: s.pos, end: s.end, range: r, value: v, bit_count: bc as u32 }
        };
        b_norm(buf, s2)
    }
}

/// bool_get: one bool, 1 with probability `(256 - prob) / 256`.
#[verifier::opaque]
pub open spec fn b_get(buf: Seq<u8>, s: BState, prob: u8) -> (bool, BState) {
    let split = (1 + ((s.range - 1) * prob) / 256) as u32;
    let big = (split * 256) as u32;
    if s.value >= big {
        (true, b_norm(buf, BState { pos: s.pos, end: s.end, range: (s.range - split) as u32, value: (s.value - big) as u32, bit_count: s.bit_count }))
    } else {
        (false, b_norm(buf, BState { pos: s.pos, end: s.end, range: split, value: s.value, bit_count: s.bit_count }))
    }
}

pub open spec fn b_bit(buf: Seq<u8>, s: BState) -> (bool, BState) { b_get(buf, s, 128) }

/// bool_get_uint: `n` bits at probability 128, most significant first.
pub open spec fn b_uint(buf: Seq<u8>, s: BState, n: nat) -> (int, BState)
    decreases n,
{
    if n == 0 {
        (0, s)
    } else {
        let (v, s1) = b_uint(buf, s, (n - 1) as nat);
        let (b, s2) = b_bit(buf, s1);
        (2 * v + if b { 1int } else { 0 }, s2)
    }
}

/// bool_get_int: a magnitude of `n` bits, then a sign.
pub open spec fn b_int(buf: Seq<u8>, s: BState, n: nat) -> (int, BState) {
    let (v, s1) = b_uint(buf, s, n);
    let (neg, s2) = b_bit(buf, s1);
    (if neg { -v } else { v }, s2)
}

/// bool_maybe_get_int: a flag, then `b_int`; else 0.
pub open spec fn b_maybe(buf: Seq<u8>, s: BState, n: nat) -> (int, BState) {
    let (f, s1) = b_bit(buf, s);
    if f { b_int(buf, s1, n) } else { (0, s1) }
}

/// `k` values of `b_maybe(n)`, appended to `acc`.
pub open spec fn b_maybes(buf: Seq<u8>, s: BState, n: nat, k: nat, acc: Seq<int>) -> (Seq<int>, BState)
    decreases k,
{
    if k == 0 {
        (acc, s)
    } else {
        let (v, s1) = b_maybe(buf, s, n);
        b_maybes(buf, s1, n, (k - 1) as nat, acc.push(v))
    }
}

// ------------------------------------------------------------- the header

pub struct Seg {
    pub enabled: bool,
    pub update_map: bool,
    pub update_data: bool,
    pub abs: bool,
    /// The segment id tree's probabilities (3).
    pub tree: Seq<u8>,
    /// Loop filter levels and quantizer indexes (4 each), deltas unless `abs`.
    pub lf: Seq<int>,
    pub quant: Seq<int>,
}

pub struct Filt {
    pub simple: bool,
    pub level: int,
    pub sharpness: int,
    pub delta: bool,
    pub ref_delta: Seq<int>,
    pub mode_delta: Seq<int>,
}

pub struct Quant {
    pub q: int,
    pub y1_dc: int,
    pub y2_dc: int,
    pub y2_ac: int,
    pub uv_dc: int,
    pub uv_ac: int,
}

pub struct Hdr {
    pub w: nat,
    pub h: nat,
    pub seg: Seg,
    pub filt: Filt,
    pub quant: Quant,
    /// The coefficient probabilities (4 x 8 x 3 x 11, flattened).
    pub probs: Seq<u8>,
    /// mb_no_coeff_skip, and the skip probability.
    pub skip: Option<u8>,
}

pub open spec fn zeros4() -> Seq<int> { seq![0int, 0, 0, 0] }

/// The segment tree's three probabilities: each 255 unless sent.
pub open spec fn tree_probs(buf: Seq<u8>, s: BState, k: nat, acc: Seq<u8>) -> (Seq<u8>, BState)
    decreases k,
{
    if k == 0 {
        (acc, s)
    } else {
        let (f, s1) = b_bit(buf, s);
        let (v, s2) = if f { let (v, s2) = b_uint(buf, s1, 8); (v as u8, s2) } else { (255u8, s1) };
        tree_probs(buf, s2, (k - 1) as nat, acc.push(v))
    }
}

/// decode_segmentation_header, on a key frame.
pub open spec fn seg_hdr(buf: Seq<u8>, s: BState) -> (Seg, BState) {
    let (en, s1) = b_bit(buf, s);
    if !en {
        (Seg { enabled: false, update_map: false, update_data: false, abs: false, tree: seq![0u8, 0, 0], lf: zeros4(), quant: zeros4() }, s1)
    } else {
        let (um, s2) = b_bit(buf, s1);
        let (ud, s3) = b_bit(buf, s2);
        let (abs, s4) = if ud { b_bit(buf, s3) } else { (false, s3) };
        let (quant, s5) = if ud { b_maybes(buf, s4, 7, 4, Seq::empty()) } else { (zeros4(), s4) };
        let (lf, s6) = if ud { b_maybes(buf, s5, 6, 4, Seq::empty()) } else { (zeros4(), s5) };
        let (tree, s7) = if um { tree_probs(buf, s6, 3, Seq::empty()) } else { (seq![0u8, 0, 0], s6) };
        (Seg { enabled: true, update_map: um, update_data: ud, abs, tree, lf, quant }, s7)
    }
}

/// decode_loopfilter_header, on a key frame.
pub open spec fn filt_hdr(buf: Seq<u8>, s: BState) -> (Filt, BState) {
    let (simple, s1) = b_bit(buf, s);
    let (level, s2) = b_uint(buf, s1, 6);
    let (sharpness, s3) = b_uint(buf, s2, 3);
    let (delta, s4) = b_bit(buf, s3);
    let (upd, s5) = if delta { b_bit(buf, s4) } else { (false, s4) };
    let (ref_delta, s6) = if upd { b_maybes(buf, s5, 6, 4, Seq::empty()) } else { (zeros4(), s5) };
    let (mode_delta, s7) = if upd { b_maybes(buf, s6, 6, 4, Seq::empty()) } else { (zeros4(), s6) };
    (Filt { simple, level, sharpness, delta, ref_delta, mode_delta }, s7)
}

/// decode_quantizer_header.
pub open spec fn quant_hdr(buf: Seq<u8>, s: BState) -> (Quant, BState) {
    let (q, s1) = b_uint(buf, s, 7);
    let (y1_dc, s2) = b_maybe(buf, s1, 4);
    let (y2_dc, s3) = b_maybe(buf, s2, 4);
    let (y2_ac, s4) = b_maybe(buf, s3, 4);
    let (uv_dc, s5) = b_maybe(buf, s4, 4);
    let (uv_ac, s6) = b_maybe(buf, s5, 4);
    (Quant { q, y1_dc, y2_dc, y2_ac, uv_dc, uv_ac }, s6)
}

/// decode_entropy_header's coefficient probability updates, from the
/// `acc.len()`-th on.
pub open spec fn coeff_probs(buf: Seq<u8>, s: BState, acc: Seq<u8>) -> (Seq<u8>, BState)
    decreases 1056 - acc.len(),
{
    if acc.len() >= 1056 {
        (acc, s)
    } else {
        let i = acc.len() as int;
        let (u, s1) = b_get(buf, s, COEFF_UPDATE_PROBS@[i]);
        let (v, s2) = if u { let (v, s2) = b_uint(buf, s1, 8); (v as u8, s2) } else { (DEFAULT_COEFF_PROBS@[i], s1) };
        coeff_probs(buf, s2, acc.push(v))
    }
}

/// A 3-byte little-endian size at `i`.
pub open spec fn le24(b: Seq<u8>, i: int) -> nat {
    b[i] as nat + 256 * b[i + 1] as nat + 65536 * b[i + 2] as nat
}

/// decode_and_init_token_partitions: of `rest` (the frame after the first
/// partition) and `n` partitions, the `acc.len()`-th on; `at` is where it
/// starts, `sz` the bytes not yet given to a partition.
pub open spec fn parts(rest: Seq<u8>, n: nat, at: nat, sz: nat, acc: Seq<Seq<u8>>) -> Option<Seq<Seq<u8>>>
    decreases n - acc.len(),
{
    if acc.len() >= n {
        Some(acc)
    } else {
        let i = acc.len() as int;
        let psz = if i < n - 1 { le24(rest, 3 * i) } else { sz };
        if sz < psz || at + psz > rest.len() {
            None
        } else {
            parts(rest, n, at + psz, (sz - psz) as nat, acc.push(rest.subrange(at as int, (at + psz) as int)))
        }
    }
}

pub open spec fn token_parts(rest: Seq<u8>, n: nat) -> Option<Seq<Seq<u8>>> {
    if n < 1 || rest.len() < 3 * (n - 1) {
        None
    } else {
        parts(rest, n, (3 * (n - 1)) as nat, (rest.len() - 3 * (n - 1)) as nat, Seq::empty())
    }
}

/// The frame tag (9.1): 3 bytes, little-endian.
pub open spec fn tag(b: Seq<u8>) -> nat { le24(b, 0) }

/// vp8_parse_frame_header and decode_frame's key frame header, up to the
/// per-macroblock data: the header, the first partition (with its reader
/// after the header), and the token partitions. None where dixie reports
/// an error; also for an interframe (WebP holds key frames only).
pub open spec fn header(b: Seq<u8>) -> Option<(Hdr, Seq<u8>, BState, Seq<Seq<u8>>)> {
    if b.len() < 10 {
        None
    } else {
        let t = tag(b);
        let part0 = t / 32;
        if b.len() <= part0 + 10 || t % 2 != 0 || b[3] != 0x9d || b[4] != 0x01 || b[5] != 0x2a {
            None
        } else {
            let w = b[6] as nat + 256 * (b[7] as nat % 64);
            let h = b[8] as nat + 256 * (b[9] as nat % 64);
            if w == 0 || h == 0 || (t / 8) % 2 == 1 {
                None
            } else {
                let p0 = b.subrange(10, (10 + part0) as int);
                let rest = b.subrange((10 + part0) as int, b.len() as int);
                let s0 = b_init(p0);
                let (cs, s1) = b_uint(p0, s0, 2);
                if cs != 0 {
                    None  // color space and clamping type: "Reserved bits not supported"
                } else {
                    let (seg, s2) = seg_hdr(p0, s1);
                    let (filt, s3) = filt_hdr(p0, s2);
                    let (np, s4) = b_uint(p0, s3, 2);
                    let n = if np == 0 { 1nat } else if np == 1 { 2nat } else if np == 2 { 4nat } else { 8nat };
                    match token_parts(rest, n) {
                        None => None,
                        Some(ps) => {
                            let (quant, s5) = quant_hdr(p0, s4);
                            let (_refresh, s6) = b_bit(p0, s5);
                            let (probs, s7) = coeff_probs(p0, s6, Seq::empty());
                            let (sk, s8) = b_bit(p0, s7);
                            let (skip, s9) = if sk { let (v, s9) = b_uint(p0, s8, 8); (Some(v as u8), s9) } else { (None, s8) };
                            Some((Hdr { w, h, seg, filt, quant, probs, skip }, p0, s9, ps))
                        },
                    }
                }
            }
        }
    }
}

// --------------------------------------------------------------- the modes

// 16x16 luma and 8x8 chroma modes.
pub open spec fn m_dc() -> nat { 0 }
pub open spec fn m_v() -> nat { 1 }
pub open spec fn m_h() -> nat { 2 }
pub open spec fn m_tm() -> nat { 3 }
pub open spec fn m_b() -> nat { 4 }

/// A macroblock's modes (20.11: the key frame parts of modemv.c).
pub struct Mb {
    pub segment: nat,
    pub skip: bool,
    pub y_mode: nat,
    pub uv_mode: nat,
    /// The 16 subblock modes if `y_mode` is B_PRED (else 16 zeros).
    pub b_modes: Seq<nat>,
}

/// kf_y_mode_tree with kf_y_mode_probs {145, 156, 163, 128}.
#[verifier::opaque]
pub open spec fn read_y_mode(buf: Seq<u8>, s: BState) -> (nat, BState) {
    let (a, s1) = b_get(buf, s, 145);
    if !a {
        (m_b(), s1)
    } else {
        let (b, s2) = b_get(buf, s1, 156);
        if !b {
            let (c, s3) = b_get(buf, s2, 163);
            (if c { m_v() } else { m_dc() }, s3)
        } else {
            let (c, s3) = b_get(buf, s2, 128);
            (if c { m_tm() } else { m_h() }, s3)
        }
    }
}

/// uv_mode_tree with kf_uv_mode_probs {142, 114, 183}.
#[verifier::opaque]
pub open spec fn read_uv_mode(buf: Seq<u8>, s: BState) -> (nat, BState) {
    let (a, s1) = b_get(buf, s, 142);
    if !a {
        (m_dc(), s1)
    } else {
        let (b, s2) = b_get(buf, s1, 114);
        if !b {
            (m_v(), s2)
        } else {
            let (c, s3) = b_get(buf, s2, 183);
            (if c { m_tm() } else { m_h() }, s3)
        }
    }
}

/// b_mode_tree with the 9 probabilities at `KF_B_MODE_PROBS[at..at + 9]`:
///   node 0: B_DC | node 1;  1: B_TM | 2;  2: B_VE | 3;  3: 4 | 6;
///   4: B_HE | 5;  5: B_RD | B_VR;  6: B_LD | 7;  7: B_VL | 8;  8: B_HD | B_HU.
/// Subblock modes: B_DC 0, B_TM 1, B_VE 2, B_HE 3, B_LD 4, B_RD 5, B_VR 6,
/// B_VL 7, B_HD 8, B_HU 9.
#[verifier::opaque]
pub open spec fn read_b_mode(buf: Seq<u8>, s: BState, at: int) -> (nat, BState) {
    let p = |k: int| KF_B_MODE_PROBS@[at + k];
    let (n0, s0) = b_get(buf, s, p(0));
    if !n0 { (0, s0) } else {
        let (n1, s1) = b_get(buf, s0, p(1));
        if !n1 { (1, s1) } else {
            let (n2, s2) = b_get(buf, s1, p(2));
            if !n2 { (2, s2) } else {
                let (n3, s3) = b_get(buf, s2, p(3));
                if !n3 {
                    let (n4, s4) = b_get(buf, s3, p(4));
                    if !n4 { (3, s4) } else {
                        let (n5, s5) = b_get(buf, s4, p(5));
                        (if n5 { 6 } else { 5 }, s5)
                    }
                } else {
                    let (n6, s6) = b_get(buf, s3, p(6));
                    if !n6 { (4, s6) } else {
                        let (n7, s7) = b_get(buf, s6, p(7));
                        if !n7 { (7, s7) } else {
                            let (n8, s8) = b_get(buf, s7, p(8));
                            (if n8 { 9 } else { 8 }, s8)
                        }
                    }
                }
            }
        }
    }
}

/// The subblock mode a macroblock that is not B_PRED implies for its
/// neighbours' contexts (above_block_mode, left_block_mode).
pub open spec fn implied(y_mode: nat) -> nat {
    if y_mode == m_dc() { 0 } else if y_mode == m_v() { 2 } else if y_mode == m_h() { 3 } else { 1 }
}

/// The subblock modes of a macroblock's bottom row (`side` 0) or right
/// column (`side` 1), as its neighbours' contexts see them.
pub open spec fn edge_modes(mb: Mb, side: nat) -> Seq<nat> {
    Seq::new(4, |k: int| if mb.y_mode == m_b() {
        if side == 0 { mb.b_modes[12 + k] } else { mb.b_modes[4 * k + 3] }
    } else {
        implied(mb.y_mode)
    })
}

/// Outside the frame, the contexts are B_DC (dixie's calloc'd border).
pub open spec fn dc4() -> Seq<nat> { seq![0nat, 0, 0, 0] }

/// The subblock modes from the `acc.len()`-th: each read with the
/// probabilities of the modes above and to its left (`above` and `left`
/// are the neighbouring macroblocks' edges).
pub open spec fn b_modes(buf: Seq<u8>, s: BState, above: Seq<nat>, left: Seq<nat>, acc: Seq<nat>) -> (Seq<nat>, BState)
    decreases 16 - acc.len(),
{
    if acc.len() >= 16 {
        (acc, s)
    } else {
        let b = acc.len() as int;
        let a = if b < 4 { above[b] } else { acc[b - 4] };
        let l = if b % 4 == 0 { left[b / 4] } else { acc[b - 1] };
        let (m, s1) = read_b_mode(buf, s, ((a * 10 + l) * 9) as int);
        b_modes(buf, s1, above, left, acc.push(m))
    }
}

/// One macroblock's modes (the key frame case of
/// vp8_dixie_modemv_process_row and decode_kf_mb_mode).
#[verifier::opaque]
pub open spec fn mb_modes(hd: Hdr, buf: Seq<u8>, s: BState, above: Seq<nat>, left: Seq<nat>) -> (Mb, BState) {
    let (segment, s1) = if hd.seg.update_map {
        let (a, s1a) = b_get(buf, s, hd.seg.tree[0]);
        if !a {
            let (b, s1b) = b_get(buf, s1a, hd.seg.tree[1]);
            (if b { 1nat } else { 0nat }, s1b)
        } else {
            let (b, s1b) = b_get(buf, s1a, hd.seg.tree[2]);
            (if b { 3nat } else { 2nat }, s1b)
        }
    } else {
        (0nat, s)
    };
    let (skip, s2) = match hd.skip { Some(p) => b_get(buf, s1, p), None => (false, s1) };
    let (y_mode, s3) = read_y_mode(buf, s2);
    let (bm, s4) = if y_mode == m_b() { b_modes(buf, s3, above, left, Seq::empty()) } else { (Seq::new(16, |k: int| 0nat), s3) };
    let (uv_mode, s5) = read_uv_mode(buf, s4);
    (Mb { segment, skip, y_mode, uv_mode, b_modes: bm }, s5)
}

/// A row of macroblocks' modes, from the `acc.len()`-th: `above` are the
/// row above's bottom edges (one per column), `left` the previous
/// macroblock's right edge.
pub open spec fn modes_row(hd: Hdr, buf: Seq<u8>, s: BState, mbw: nat, above: Seq<Seq<nat>>, left: Seq<nat>, acc: Seq<Mb>)
    -> (Seq<Mb>, BState)
    decreases mbw - acc.len(),
{
    if acc.len() >= mbw {
        (acc, s)
    } else {
        let x = acc.len() as int;
        let (mb, s1) = mb_modes(hd, buf, s, above[x], left);
        modes_row(hd, buf, s1, mbw, above, edge_modes(mb, 1), acc.push(mb))
    }
}

/// Every macroblock's modes, rows from the `acc.len()`-th.
pub open spec fn modes(hd: Hdr, buf: Seq<u8>, s: BState, mbw: nat, mbh: nat, acc: Seq<Seq<Mb>>) -> (Seq<Seq<Mb>>, BState)
    decreases mbh - acc.len(),
{
    if acc.len() >= mbh {
        (acc, s)
    } else {
        let above = if acc.len() == 0 {
            Seq::new(mbw, |x: int| dc4())
        } else {
            Seq::new(mbw, |x: int| edge_modes(acc.last()[x], 0))
        };
        let (row, s1) = modes_row(hd, buf, s, mbw, above, dc4(), Seq::empty());
        modes(hd, buf, s1, mbw, mbh, acc.push(row))
    }
}

// -------------------------------------------------------------- the tokens

/// The extra bits' probabilities of DCT_VAL_CATEGORY1..6 (tokens.c's
/// `extrabits`), each category's most significant bit first: cat1 at 0,
/// cat2 at 1, cat3 at 3, cat4 at 6, cat5 at 10, cat6 at 15.
pub const CAT_PROBS: [u8; 26] = [
    159,
    165, 145,
    173, 148, 140,
    176, 155, 140, 135,
    180, 157, 141, 134, 130,
    254, 254, 243, 230, 196, 177, 153, 140, 133, 130, 129,
];

/// Dequantization factors, DC and AC, for Y (type 0 and 3 blocks), U and V
/// (type 2), Y2 (type 1) (struct dequant_factors).
pub struct Fac {
    pub y1: (int, int),
    pub uv: (int, int),
    pub y2: (int, int),
}

pub open spec fn clamp_q(q: int) -> int { if q < 0 { 0 } else if q > 127 { 127 } else { q } }

pub open spec fn dc_q(q: int) -> int { DC_Q@[clamp_q(q)] as int }
pub open spec fn ac_q(q: int) -> int { AC_Q@[clamp_q(q)] as int }

/// dequant_init for a segment's quantizer index `q`. dixie keeps the
/// factors of each segment from frame to frame and recomputes them only if
/// the index changed or `delta_update`; its cache starts at index -1 with
/// factors 0. So in a first frame a segment whose index is -1, with
/// `delta_update` clear (the frame's index 0, no quantizer deltas), keeps
/// factors 0.
pub open spec fn factors(q: int, qh: Quant) -> Fac {
    let delta_update = qh.q != 0 || qh.y1_dc != 0 || qh.y2_dc != 0 || qh.y2_ac != 0 || qh.uv_dc != 0 || qh.uv_ac != 0;
    if q == -1 && !delta_update {
        Fac { y1: (0, 0), uv: (0, 0), y2: (0, 0) }
    } else {
        let y2ac = ac_q(q + qh.y2_ac) * 155 / 100;
        let uvdc = dc_q(q + qh.uv_dc);
        Fac {
            y1: (dc_q(q + qh.y1_dc), ac_q(q)),
            uv: (if uvdc > 132 { 132 } else { uvdc }, ac_q(q + qh.uv_ac)),
            y2: (dc_q(q + qh.y2_dc) * 2, if y2ac < 8 { 8 } else { y2ac }),
        }
    }
}

/// The quantizer index of segment `i`.
pub open spec fn seg_q(hd: Hdr, i: int) -> int {
    if !hd.seg.enabled { hd.quant.q } else if hd.seg.abs { hd.seg.quant[i] } else { hd.quant.q + hd.seg.quant[i] }
}

/// A value stored in a C `short`: its low 16 bits, as two's complement.
pub open spec fn wrap16(x: int) -> int {
    let m = x % 65536;  // in 0..65535 (int's % takes the divisor's sign)
    if m >= 32768 { m - 65536 } else { m }
}

/// Coefficient positions in zigzag order, and each position's band
/// (tokens.c's `zigzag` and `bands_x`).
pub const ZIGZAG: [u8; 16] = [0, 1, 4, 8, 5, 2, 3, 6, 9, 12, 13, 10, 7, 11, 14, 15];
pub const BANDS: [u8; 16] = [0, 1, 2, 3, 6, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 7];

/// Where the 11 probabilities of block type `ty`, position `c`'s band and
/// context `ctx` start.
pub open spec fn pbase(ty: int, c: int, ctx: int) -> int { ((ty * 8 + BANDS@[c] as int) * 3 + ctx) * 11 }

/// The extra bits of a DCT_VAL_CATEGORY token: `n` more bits, each at the
/// next probability of `CAT_PROBS[at..]`, most significant first, added to `v`.
pub open spec fn extra(buf: Seq<u8>, s: BState, at: int, n: nat, v: int) -> (int, BState)
    decreases n,
{
    if n == 0 {
        (v, s)
    } else {
        let (b, s1) = b_get(buf, s, CAT_PROBS@[at]);
        extra(buf, s1, at + 1, (n - 1) as nat, 2 * v + if b { 1int } else { 0 })
    }
}

/// DCT_VAL_CATEGORY1..6: the least value, where its probabilities start in
/// CAT_PROBS, and how many extra bits.
pub const CAT_BASE: [u8; 6] = [5, 7, 11, 19, 35, 67];
pub const CAT_AT: [u8; 6] = [0, 1, 3, 6, 10, 15];
pub const CAT_LEN: [u8; 6] = [1, 2, 3, 4, 5, 11];

/// A token's value, past the ONE_CONTEXT_NODE (the bool at `p[2]` was 1),
/// with the probabilities at `p = probs[pb..]`.
pub open spec fn big_value(buf: Seq<u8>, s: BState, probs: Seq<u8>, pb: int) -> (int, BState) {
    let (lo, s1) = b_get(buf, s, probs[pb + 3]);
    if !lo {
        let (two, s2) = b_get(buf, s1, probs[pb + 4]);
        if !two { (2, s2) } else {
            let (three, s3) = b_get(buf, s2, probs[pb + 5]);
            (if three { 4 } else { 3 }, s3)
        }
    } else {
        let (hl, s2) = b_get(buf, s1, probs[pb + 6]);
        let (cat, s4) = if !hl {
            let (c1, s3) = b_get(buf, s2, probs[pb + 7]);
            (if c1 { 1int } else { 0 }, s3)
        } else {
            let (c34, s3) = b_get(buf, s2, probs[pb + 8]);
            if !c34 {
                let (c3, s3b) = b_get(buf, s3, probs[pb + 9]);
                (if c3 { 3int } else { 2 }, s3b)
            } else {
                let (c5, s3b) = b_get(buf, s3, probs[pb + 10]);
                (if c5 { 5int } else { 4 }, s3b)
            }
        };
        let (e, s5) = extra(buf, s4, CAT_AT@[cat] as int, CAT_LEN@[cat] as nat, 0);
        (CAT_BASE@[cat] as int + e, s5)
    }
}

/// The tokens of one block from position `c` (decode_mb_tokens, from
/// BLOCK_LOOP to BLOCK_FINISHED): `eob` says an end of block may come next
/// (not after a zero token). Coefficients are dequantized (DC factor at
/// position 0, AC after) and stored in 16 bits, at their zigzag place in
/// `out`. Returns them, the final position, and the reader. A block runs to
/// position 15 at most, where it ends without an end-of-block token.
pub open spec fn tokens(buf: Seq<u8>, s: BState, probs: Seq<u8>, ty: int, c: int, ctx: int, eob: bool,
    dqf: (int, int), out: Seq<int>) -> (Seq<int>, int, BState)
    decreases 16 - c, if eob { 1int } else { 0 },
{
    if c < 0 || c > 15 {
        (out, c, s)
    } else {
        let pb = pbase(ty, c, ctx);
        if eob {
            let (more, s1) = b_get(buf, s, probs[pb]);
            if !more { (out, c, s1) } else { tokens(buf, s1, probs, ty, c, ctx, false, dqf, out) }
        } else {
            let (nz, s1) = b_get(buf, s, probs[pb + 1]);
            if !nz {
                if c == 15 { (out, 15, s1) } else { tokens(buf, s1, probs, ty, c + 1, 0, false, dqf, out) }
            } else {
                let (one, s2) = b_get(buf, s1, probs[pb + 2]);
                let (v, s3) = if !one { (1int, s2) } else { big_value(buf, s2, probs, pb) };
                let (neg, s4) = b_bit(buf, s3);
                let f = if c > 0 { dqf.1 } else { dqf.0 };
                let out2 = out.update(ZIGZAG@[c] as int, wrap16((if neg { -v } else { v }) * f));
                if c == 15 { (out2, 15, s4) } else { tokens(buf, s4, probs, ty, c + 1, if v == 1 { 1 } else { 2 }, true, dqf, out2) }
            }
        }
    }
}

pub open spec fn zeros16() -> Seq<int> { Seq::new(16, |k: int| 0int) }

/// Which of the 9 entries of a left or above token context block `i` uses
/// (4 Y, 2 U, 2 V, Y2).
pub const LEFT_CTX: [u8; 25] = [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8];
pub const ABOVE_CTX: [u8; 25] = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 4, 5, 6, 7, 6, 7, 8];

/// The `k`-th block a macroblock's tokens go to, and its type: Y2 (24,
/// type 1) first unless B_PRED, then the Y blocks (type 0 after a Y2, else
/// 3), then U (16..19) and V (20..23) (type 2).
pub open spec fn nblocks(bpred: bool) -> int { if bpred { 24 } else { 25 } }
pub open spec fn block_at(bpred: bool, k: int) -> (int, int) {
    if bpred {
        if k < 16 { (k, 3) } else { (k, 2) }
    } else {
        if k == 0 { (24, 1) } else if k <= 16 { (k - 1, 0) } else { (k - 1, 2) }
    }
}

/// A macroblock's token contexts and coefficients (25 blocks of 16, in
/// block order), with whether any block had a token other than an
/// immediate end of block (dixie's eob_mask).
pub struct TokState {
    pub s: BState,
    pub left: Seq<int>,
    pub above: Seq<int>,
    pub coeffs: Seq<Seq<int>>,
    pub nonzero: bool,
}

/// The factors of a block type: Y2 for type 1, UV for type 2, else Y1.
pub open spec fn fac_of(f: Fac, ty: int) -> (int, int) { if ty == 1 { f.y2 } else if ty == 2 { f.uv } else { f.y1 } }

/// The blocks of a macroblock's tokens from the `k`-th (decode_mb_tokens).
pub open spec fn mb_blocks(buf: Seq<u8>, probs: Seq<u8>, f: Fac, bpred: bool, k: int, t: TokState) -> TokState
    decreases 25 - k,
{
    if k < 0 || k >= nblocks(bpred) {
        t
    } else {
        let (i, ty) = block_at(bpred, k);
        let ctx = t.left[LEFT_CTX@[i] as int] + t.above[ABOVE_CTX@[i] as int];
        let first = if ty == 0 { 1int } else { 0 };
        let (out, c, s1) = tokens(buf, t.s, probs, ty, first, ctx, true, fac_of(f, ty), zeros16());
        let nz = if c != first { 1int } else { 0 };
        mb_blocks(buf, probs, f, bpred, k + 1, TokState {
            s: s1,
            left: t.left.update(LEFT_CTX@[i] as int, nz),
            above: t.above.update(ABOVE_CTX@[i] as int, nz),
            coeffs: t.coeffs.update(i, out),
            nonzero: t.nonzero || c != first,
        })
    }
}

/// A macroblock's tokens (vp8_dixie_tokens_process_row's body): for a
/// skipped one, no coefficients, and the contexts reset (the Y2 entry only
/// if the macroblock has a Y2 block).
#[verifier::opaque]
pub open spec fn mb_tokens(buf: Seq<u8>, probs: Seq<u8>, f: Fac, mb: Mb, s: BState, left: Seq<int>, above: Seq<int>) -> TokState {
    let bpred = mb.y_mode == m_b();
    let zero = Seq::new(25, |i: int| zeros16());
    if mb.skip {
        let keep = |c: Seq<int>| Seq::new(9, |k: int| if k == 8 && bpred { c[8] } else { 0int });
        TokState { s, left: keep(left), above: keep(above), coeffs: zero, nonzero: false }
    } else {
        mb_blocks(buf, probs, f, bpred, 0, TokState { s, left, above, coeffs: zero, nonzero: false })
    }
}

// ----------------------------------------------------- inverse transforms

/// sinpi8sqrt2 and cospi8sqrt2minus1 products (idct_add.c); an arithmetic
/// shift right by 16 is a division that floors.
pub open spec fn ms(x: int) -> int { (x * 35468) / 65536 }
pub open spec fn mc(x: int) -> int { x + (x * 20091) / 65536 }

/// vp8_dixie_walsh: the inverse WHT of the Y2 block, each Y block's DC.
/// The first pass is stored in `short`s.
pub open spec fn iwht_col(i: Seq<int>, k: int) -> Seq<int> {
    let a1 = i[k] + i[12 + k];
    let b1 = i[4 + k] + i[8 + k];
    let c1 = i[4 + k] - i[8 + k];
    let d1 = i[k] - i[12 + k];
    seq![wrap16(a1 + b1), wrap16(c1 + d1), wrap16(a1 - b1), wrap16(d1 - c1)]
}

/// The first pass, column `k`'s four values at rows 0..3.
pub open spec fn iwht1(i: Seq<int>) -> Seq<int> {
    Seq::new(16, |j: int| iwht_col(i, j % 4)[j / 4])
}

#[verifier::opaque]
pub open spec fn iwht(i: Seq<int>) -> Seq<int> {
    let o = iwht1(i);
    Seq::new(16, |j: int| {
        let r = j / 4;
        let a1 = o[4 * r] + o[4 * r + 3];
        let b1 = o[4 * r + 1] + o[4 * r + 2];
        let c1 = o[4 * r + 1] - o[4 * r + 2];
        let d1 = o[4 * r] - o[4 * r + 3];
        let v = if j % 4 == 0 { a1 + b1 } else if j % 4 == 1 { c1 + d1 } else if j % 4 == 2 { a1 - b1 } else { d1 - c1 };
        wrap16((v + 3) / 8)
    })
}

/// idct_columns for column `k`: rows 0..3.
pub open spec fn idct_col(i: Seq<int>, k: int) -> Seq<int> {
    let a1 = i[k] + i[8 + k];
    let b1 = i[k] - i[8 + k];
    let c1 = ms(i[4 + k]) - mc(i[12 + k]);
    let d1 = mc(i[4 + k]) + ms(i[12 + k]);
    seq![wrap16(a1 + d1), wrap16(b1 + c1), wrap16(b1 - c1), wrap16(a1 - d1)]
}

pub open spec fn idct1(i: Seq<int>) -> Seq<int> {
    Seq::new(16, |j: int| idct_col(i, j % 4)[j / 4])
}

/// vp8_dixie_idct_add's residual: the value added to the prediction at
/// (row j / 4, column j % 4), before clamping.
#[verifier::opaque]
pub open spec fn idct(i: Seq<int>) -> Seq<int> {
    let t = idct1(i);
    Seq::new(16, |j: int| {
        let r = j / 4;
        let a1 = t[4 * r] + t[4 * r + 2];
        let b1 = t[4 * r] - t[4 * r + 2];
        let c1 = ms(t[4 * r + 1]) - mc(t[4 * r + 3]);
        let d1 = mc(t[4 * r + 1]) + ms(t[4 * r + 3]);
        let v = if j % 4 == 0 { a1 + d1 } else if j % 4 == 1 { b1 + c1 } else if j % 4 == 2 { b1 - c1 } else { a1 - d1 };
        (v + 4) / 8
    })
}

// ------------------------------------------------------ intra prediction

pub type Plane = Seq<Seq<u8>>;

pub open spec fn clamp255(x: int) -> u8 { if x < 0 { 0 } else if x > 255 { 255 } else { x as u8 } }

/// The plane with the `n` x `n` block at (x, y) set to `f(row, column)`.
pub open spec fn set_block(p: Plane, x: int, y: int, n: int, f: spec_fn(int, int) -> u8) -> Plane {
    Seq::new(p.len(), |r: int| if y <= r < y + n {
        Seq::new(p[r].len(), |c: int| if x <= c < x + n { f(r - y, c - x) } else { p[r][c] })
    } else {
        p[r]
    })
}

/// A 4x4 residual added to the block at (x, y), clamped (the end of
/// vp8_dixie_idct_add).
pub open spec fn add_px(p: Plane, x: int, y: int, res: Seq<int>, r: int, c: int) -> u8 {
    clamp255(p[y + r][x + c] as int + res[4 * r + c])
}

#[verifier::opaque]
pub open spec fn add_block(p: Plane, x: int, y: int, res: Seq<int>) -> Plane {
    set_block(p, x, y, 4, |r: int, c: int| add_px(p, x, y, res, r, c))
}

/// What a predictor reads around the block at (x, y): outside the frame
/// (dixie's border), the row above is 127, the column to the left 129,
/// and the pixel above-left 127 in the first row, else 129 in the first
/// column (fixup_left, fixup_above, and the 127 above the top left
/// macroblock).
pub open spec fn above(p: Plane, x: int, y: int, k: int) -> int { if y == 0 { 127 } else { p[y - 1][x + k] as int } }
pub open spec fn left(p: Plane, x: int, y: int, k: int) -> int { if x == 0 { 129 } else { p[y + k][x - 1] as int } }
pub open spec fn above_left(p: Plane, x: int, y: int) -> int {
    if y == 0 { 127 } else if x == 0 { 129 } else { p[y - 1][x - 1] as int }
}

/// The edges DC_PRED averages: out of the frame, the column to the left
/// copies the row above and the row above copies the column to the left
/// (fixup_left, fixup_above), so a block on one edge averages the other;
/// the top left block averages 127s and 129s.
pub open spec fn dc_above(p: Plane, x: int, y: int, k: int) -> int {
    if y == 0 && x > 0 { left(p, x, y, k) } else { above(p, x, y, k) }
}
pub open spec fn dc_left(p: Plane, x: int, y: int, k: int) -> int {
    if x == 0 && y > 0 { above(p, x, y, k) } else { left(p, x, y, k) }
}

/// The sum of the first `k` of each edge.
pub open spec fn dc_sum(p: Plane, x: int, y: int, k: int) -> int
    decreases k,
{
    if k <= 0 { 0 } else { dc_sum(p, x, y, k - 1) + dc_above(p, x, y, k - 1) + dc_left(p, x, y, k - 1) }
}

/// predict_dc_nxn.
pub open spec fn dc(p: Plane, x: int, y: int, n: int) -> u8 {
    ((dc_sum(p, x, y, n) + n) / (2 * n)) as u8
}

/// predict_{dc,v,h,tm}_nxn: pixel (r, c) of the `n` x `n` block at (x, y).
pub open spec fn pred_px(p: Plane, x: int, y: int, n: int, mode: nat, r: int, c: int) -> u8 {
    if mode == m_dc() { dc(p, x, y, n) }
    else if mode == m_v() { above(p, x, y, c) as u8 }
    else if mode == m_h() { left(p, x, y, r) as u8 }
    else { clamp255(left(p, x, y, r) + above(p, x, y, c) - above_left(p, x, y)) }
}

#[verifier::opaque]
pub open spec fn predict(p: Plane, x: int, y: int, n: int, mode: nat) -> Plane {
    set_block(p, x, y, n, |r: int, c: int| pred_px(p, x, y, n, mode, r, c))
}

/// The 4 pixels above-right of subblock `b` of the macroblock at (mbx,
/// mby), in a plane `mbw` macroblocks wide. Subblocks in the right column
/// (3, 7, 11, 15) all read the ones above-right of subblock 3, from the
/// macroblock row above (copy_down); for the last macroblock of a row these
/// are its last pixel above, repeated (dixie extends each row by 4 pixels),
/// and in the first macroblock row they are 127. Other subblocks read the
/// row above them.
pub open spec fn above_right(p: Plane, mbw: int, mbx: int, mby: int, b: int, k: int) -> int {
    let bx = b % 4;
    let by = b / 4;
    let x = mbx * 16 + bx * 4;
    let y = mby * 16 + by * 4;
    if bx < 3 && by > 0 {
        p[y - 1][x + 4 + k] as int
    } else if mby == 0 {
        127
    } else if bx < 3 {
        p[mby * 16 - 1][x + 4 + k] as int
    } else if mbx == mbw - 1 {
        p[mby * 16 - 1][mbw * 16 - 1] as int
    } else {
        p[mby * 16 - 1][mbx * 16 + 16 + k] as int
    }
}

pub open spec fn avg3(x: int, y: int, z: int) -> u8 { ((x + 2 * y + z + 2) / 4) as u8 }
pub open spec fn avg2(x: int, y: int) -> u8 { ((x + y + 1) / 2) as u8 }

/// The ten 4x4 predictors (predict_*_4x4), pixel (r, c): `a` is the row
/// above with the pixel above-left first (a[0] above-left, a[1..9] above
/// and above-right: above[k] is a[k + 1]), `l` the column to the left.
pub open spec fn pred4(mode: nat, a: Seq<int>, l: Seq<int>, r: int, c: int) -> u8 {
    let t = |k: int| a[k + 1];
    let p = a[0];
    if mode == 0 {  // B_DC_PRED
        ((t(0) + t(1) + t(2) + t(3) + l[0] + l[1] + l[2] + l[3] + 4) / 8) as u8
    } else if mode == 1 {  // B_TM_PRED
        clamp255(l[r] + t(c) - p)
    } else if mode == 2 {  // B_VE_PRED
        avg3(a[c], a[c + 1], a[c + 2])
    } else if mode == 3 {  // B_HE_PRED
        if r == 0 { avg3(p, l[0], l[1]) } else if r == 1 { avg3(l[0], l[1], l[2]) }
        else if r == 2 { avg3(l[1], l[2], l[3]) } else { avg3(l[2], l[3], l[3]) }
    } else if mode == 4 {  // B_LD_PRED
        let k = r + c;
        if k < 6 { avg3(t(k), t(k + 1), t(k + 2)) } else { avg3(t(6), t(7), t(7)) }
    } else if mode == 5 {  // B_RD_PRED
        let e = seq![l[3], l[2], l[1], l[0], p, t(0), t(1), t(2), t(3)];
        let k = 4 - r + c;
        avg3(e[k - 1], e[k], e[k + 1])
    } else if mode == 6 {  // B_VR_PRED
        seq![
            avg2(p, t(0)), avg2(t(0), t(1)), avg2(t(1), t(2)), avg2(t(2), t(3)),
            avg3(l[0], p, t(0)), avg3(p, t(0), t(1)), avg3(t(0), t(1), t(2)), avg3(t(1), t(2), t(3)),
            avg3(l[1], l[0], p), avg2(p, t(0)), avg2(t(0), t(1)), avg2(t(1), t(2)),
            avg3(l[2], l[1], l[0]), avg3(l[0], p, t(0)), avg3(p, t(0), t(1)), avg3(t(0), t(1), t(2))
        ][4 * r + c]
    } else if mode == 7 {  // B_VL_PRED
        seq![
            avg2(t(0), t(1)), avg2(t(1), t(2)), avg2(t(2), t(3)), avg2(t(3), t(4)),
            avg3(t(0), t(1), t(2)), avg3(t(1), t(2), t(3)), avg3(t(2), t(3), t(4)), avg3(t(3), t(4), t(5)),
            avg2(t(1), t(2)), avg2(t(2), t(3)), avg2(t(3), t(4)), avg3(t(4), t(5), t(6)),
            avg3(t(1), t(2), t(3)), avg3(t(2), t(3), t(4)), avg3(t(3), t(4), t(5)), avg3(t(5), t(6), t(7))
        ][4 * r + c]
    } else if mode == 8 {  // B_HD_PRED
        seq![
            avg2(l[0], p), avg3(l[0], p, t(0)), avg3(p, t(0), t(1)), avg3(t(0), t(1), t(2)),
            avg2(l[1], l[0]), avg3(l[1], l[0], p), avg2(l[0], p), avg3(l[0], p, t(0)),
            avg2(l[2], l[1]), avg3(l[2], l[1], l[0]), avg2(l[1], l[0]), avg3(l[1], l[0], p),
            avg2(l[3], l[2]), avg3(l[3], l[2], l[1]), avg2(l[2], l[1]), avg3(l[2], l[1], l[0])
        ][4 * r + c]
    } else {  // B_HU_PRED
        let l3 = l[3] as u8;
        seq![
            avg2(l[0], l[1]), avg3(l[0], l[1], l[2]), avg2(l[1], l[2]), avg3(l[1], l[2], l[3]),
            avg2(l[1], l[2]), avg3(l[1], l[2], l[3]), avg2(l[2], l[3]), avg3(l[2], l[3], l[3]),
            avg2(l[2], l[3]), avg3(l[2], l[3], l[3]), l3, l3,
            l3, l3, l3, l3
        ][4 * r + c]
    }
}

/// Subblock `b` of the macroblock at (mbx, mby) predicted from the pixels
/// reconstructed so far, then its residual added.
/// What subblock `b`'s predictor reads: above-left, above and above-right
/// (`b_above`), and to the left (`b_left`).
pub open spec fn b_above(p: Plane, mbw: int, mbx: int, mby: int, b: int) -> Seq<int> {
    let x = mbx * 16 + (b % 4) * 4;
    let y = mby * 16 + (b / 4) * 4;
    Seq::new(9, |k: int| if k == 0 { above_left(p, x, y) } else if k <= 4 { above(p, x, y, k - 1) }
                         else { above_right(p, mbw, mbx, mby, b, k - 5) })
}

pub open spec fn b_left(p: Plane, mbx: int, mby: int, b: int) -> Seq<int> {
    Seq::new(4, |k: int| left(p, mbx * 16 + (b % 4) * 4, mby * 16 + (b / 4) * 4, k))
}

/// Subblock `b` predicted.
#[verifier::opaque]
pub open spec fn b_pred4(p: Plane, mbw: int, mbx: int, mby: int, b: int, mode: nat) -> Plane {
    let a = b_above(p, mbw, mbx, mby, b);
    let l = b_left(p, mbx, mby, b);
    set_block(p, mbx * 16 + (b % 4) * 4, mby * 16 + (b / 4) * 4, 4, |r: int, c: int| pred4(mode, a, l, r, c))
}

pub open spec fn b_block(p: Plane, mbw: int, mbx: int, mby: int, b: int, mode: nat, coeffs: Seq<int>) -> Plane {
    add_block(b_pred4(p, mbw, mbx, mby, b, mode), mbx * 16 + (b % 4) * 4, mby * 16 + (b / 4) * 4, idct(coeffs))
}

/// b_pred, subblocks from the `b`-th.
pub open spec fn b_pred(p: Plane, mbw: int, mbx: int, mby: int, mb: Mb, coeffs: Seq<Seq<int>>, b: int) -> Plane
    decreases 16 - b,
{
    if b < 0 || b >= 16 { p } else {
        b_pred(b_block(p, mbw, mbx, mby, b, mb.b_modes[b], coeffs[b]), mbw, mbx, mby, mb, coeffs, b + 1)
    }
}

/// The residuals of blocks `b..n`, block `k` at (x + 4 (k % cols),
/// y + 4 (k / cols)) with coefficients `cs[k]`.
pub open spec fn add_blocks(p: Plane, x: int, y: int, cols: int, n: int, cs: Seq<Seq<int>>, b: int) -> Plane
    decreases n - b,
{
    if b < 0 || b >= n || cols <= 0 { p } else {
        add_blocks(add_block(p, x + 4 * (b % cols), y + 4 * (b / cols), idct(cs[b])), x, y, cols, n, cs, b + 1)
    }
}

/// fixup_dc_coeffs: the Y2 block gives each Y block's DC.
pub open spec fn luma_cs(coeffs: Seq<Seq<int>>) -> Seq<Seq<int>> {
    Seq::new(16, |b: int| coeffs[b].update(0, iwht(coeffs[24])[b]))
}

/// predict_intra_luma for the macroblock at (mbx, mby).
#[verifier::opaque]
pub open spec fn luma(p: Plane, mbw: int, mbx: int, mby: int, mb: Mb, coeffs: Seq<Seq<int>>) -> Plane {
    if mb.y_mode == m_b() {
        b_pred(p, mbw, mbx, mby, mb, coeffs, 0)
    } else {
        add_blocks(predict(p, mbx * 16, mby * 16, 16, mb.y_mode), mbx * 16, mby * 16, 4, 16, luma_cs(coeffs), 0)
    }
}

/// predict_intra_chroma for one chroma plane, blocks `first..first + 4`.
#[verifier::opaque]
pub open spec fn chroma(p: Plane, mbx: int, mby: int, mode: nat, coeffs: Seq<Seq<int>>, first: int) -> Plane {
    add_blocks(predict(p, mbx * 8, mby * 8, 8, mode), mbx * 8, mby * 8, 2, 4, coeffs.subrange(first, first + 4), 0)
}

// ------------------------------------------------- the macroblocks, in order

pub struct Planes {
    pub y: Plane,
    pub u: Plane,
    pub v: Plane,
}

/// What `decode_mbs` carries from macroblock to macroblock: the planes, the
/// token partitions' readers, the token contexts above each column and to
/// the left, and each macroblock's dixie eob_mask != 0, rows so far.
pub struct Dec {
    pub pl: Planes,
    pub ps: Seq<BState>,
    pub above: Seq<Seq<int>>,
    pub left: Seq<int>,
    pub nz: Seq<Seq<bool>>,
}

pub open spec fn zeros9() -> Seq<int> { Seq::new(9, |k: int| 0int) }

/// The factors of each segment.
pub open spec fn facs(hd: Hdr) -> Seq<Fac> { Seq::new(4, |i: int| factors(seg_q(hd, i), hd.quant)) }

/// Macroblock (x, y): its tokens from its row's partition, then its
/// reconstruction.
#[verifier::opaque]
pub open spec fn decode_mb(hd: Hdr, parts: Seq<Seq<u8>>, mbs: Seq<Seq<Mb>>, mbw: int, x: int, y: int, d: Dec) -> Dec {
    let mb = mbs[y][x];
    let k = y % (parts.len() as int);
    let t = mb_tokens(parts[k], hd.probs, facs(hd)[mb.segment as int], mb, d.ps[k], d.left, d.above[x]);
    let pl = Planes {
        y: luma(d.pl.y, mbw, x, y, mb, t.coeffs),
        u: chroma(d.pl.u, x, y, mb.uv_mode, t.coeffs, 16),
        v: chroma(d.pl.v, x, y, mb.uv_mode, t.coeffs, 20),
    };
    Dec { pl, ps: d.ps.update(k, t.s), above: d.above.update(x, t.above), left: t.left, nz: d.nz.update(y, d.nz[y].push(t.nonzero)) }
}

/// Row `y`'s macroblocks from the `x`-th.
pub open spec fn decode_row(hd: Hdr, parts: Seq<Seq<u8>>, mbs: Seq<Seq<Mb>>, mbw: int, x: int, y: int, d: Dec) -> Dec
    decreases mbw - x,
{
    if x < 0 || x >= mbw { d } else { decode_row(hd, parts, mbs, mbw, x + 1, y, decode_mb(hd, parts, mbs, mbw, x, y, d)) }
}

/// The rows from the `y`-th; each starts with the left contexts cleared.
pub open spec fn decode_rows(hd: Hdr, parts: Seq<Seq<u8>>, mbs: Seq<Seq<Mb>>, mbw: int, mbh: int, y: int, d: Dec) -> Dec
    decreases mbh - y,
{
    if y < 0 || y >= mbh { d } else {
        let d1 = Dec { pl: d.pl, ps: d.ps, above: d.above, left: zeros9(), nz: d.nz.push(Seq::empty()) };
        decode_rows(hd, parts, mbs, mbw, mbh, y + 1, decode_row(hd, parts, mbs, mbw, 0, y, d1))
    }
}

pub open spec fn zero_plane(w: int, h: int) -> Plane { Seq::new(h as nat, |r: int| Seq::new(w as nat, |c: int| 0u8)) }

// --------------------------------------------------------- the loop filter

pub open spec fn s8(x: int) -> int { if x < -128 { -128 } else if x > 127 { 127 } else { x } }

/// Pixel `k` across an edge at (x, y) of `p`: across columns (`dir` 0, a
/// vertical edge) or rows (1); k = -4..-1 is p3..p0, 0..3 q0..q3.
pub open spec fn px(p: Plane, x: int, y: int, dir: int, k: int) -> int {
    if dir == 0 { p[y][x + k] as int } else { p[y + k][x] as int }
}

pub open spec fn setpx(p: Plane, x: int, y: int, dir: int, k: int, v: u8) -> Plane {
    if dir == 0 { p.update(y, p[y].update(x + k, v)) } else { p.update(y + k, p[y + k].update(x, v)) }
}

pub open spec fn absd(a: int, b: int) -> int { if a >= b { a - b } else { b - a } }

pub open spec fn hev(p: Plane, x: int, y: int, dir: int, t: int) -> bool {
    absd(px(p, x, y, dir, -2), px(p, x, y, dir, -1)) > t || absd(px(p, x, y, dir, 1), px(p, x, y, dir, 0)) > t
}

pub open spec fn simple_threshold(p: Plane, x: int, y: int, dir: int, limit: int) -> bool {
    absd(px(p, x, y, dir, -1), px(p, x, y, dir, 0)) * 2 + absd(px(p, x, y, dir, -2), px(p, x, y, dir, 1)) / 2 <= limit
}

pub open spec fn normal_threshold(p: Plane, x: int, y: int, dir: int, e: int, i: int) -> bool {
    let g = |k: int| px(p, x, y, dir, k);
    simple_threshold(p, x, y, dir, 2 * e + i)
        && absd(g(-4), g(-3)) <= i && absd(g(-3), g(-2)) <= i && absd(g(-2), g(-1)) <= i
        && absd(g(3), g(2)) <= i && absd(g(2), g(1)) <= i && absd(g(1), g(0)) <= i
}

/// filter_common.
pub open spec fn common(p: Plane, x: int, y: int, dir: int, outer: bool) -> Plane {
    let g = |k: int| px(p, x, y, dir, k);
    let a = s8(3 * (g(0) - g(-1)) + if outer { s8(g(-2) - g(1)) } else { 0 });
    let f1 = (if a + 4 > 127 { 127 } else { a + 4 }) / 8;
    let f2 = (if a + 3 > 127 { 127 } else { a + 3 }) / 8;
    let p1 = setpx(setpx(p, x, y, dir, -1, clamp255(g(-1) + f2)), x, y, dir, 0, clamp255(g(0) - f1));
    if outer { p1 } else {
        let a2 = (f1 + 1) / 2;
        setpx(setpx(p1, x, y, dir, -2, clamp255(g(-2) + a2)), x, y, dir, 1, clamp255(g(1) - a2))
    }
}

/// filter_mb_edge.
pub open spec fn mb_edge(p: Plane, x: int, y: int, dir: int) -> Plane {
    let g = |k: int| px(p, x, y, dir, k);
    let w = s8(s8(g(-2) - g(1)) + 3 * (g(0) - g(-1)));
    let a0 = (27 * w + 63) / 128;
    let a1 = (18 * w + 63) / 128;
    let a2 = (9 * w + 63) / 128;
    let p1 = setpx(setpx(p, x, y, dir, -1, clamp255(g(-1) + a0)), x, y, dir, 0, clamp255(g(0) - a0));
    let p2 = setpx(setpx(p1, x, y, dir, -2, clamp255(g(-2) + a1)), x, y, dir, 1, clamp255(g(1) - a1));
    setpx(setpx(p2, x, y, dir, -3, clamp255(g(-3) + a2)), x, y, dir, 2, clamp255(g(2) - a2))
}

/// The kinds of edge filter: a macroblock edge, a subblock edge, simple.
pub open spec fn kind_mb() -> int { 0 }
pub open spec fn kind_sub() -> int { 1 }
pub open spec fn kind_simple() -> int { 2 }

/// One pixel line across an edge.
#[verifier::opaque]
pub open spec fn filter_line(p: Plane, x: int, y: int, dir: int, kind: int, e: int, i: int, h: int) -> Plane {
    if kind == kind_simple() {
        if simple_threshold(p, x, y, dir, e) { common(p, x, y, dir, true) } else { p }
    } else if kind == kind_mb() {
        if normal_threshold(p, x, y, dir, e, i) {
            if hev(p, x, y, dir, h) { common(p, x, y, dir, true) } else { mb_edge(p, x, y, dir) }
        } else { p }
    } else {
        if normal_threshold(p, x, y, dir, e, i) { common(p, x, y, dir, hev(p, x, y, dir, h)) } else { p }
    }
}

/// The lines of an edge from the `k`-th of `n`: a vertical edge (dir 0) at
/// column x has lines at rows y..y + n, a horizontal one at row y columns
/// x..x + n.
pub open spec fn filter_edge(p: Plane, x: int, y: int, dir: int, n: int, kind: int, e: int, i: int, h: int, k: int) -> Plane
    decreases n - k,
{
    if k < 0 || k >= n { p } else {
        let (lx, ly) = if dir == 0 { (x, y + k) } else { (x + k, y) };
        filter_edge(filter_line(p, lx, ly, dir, kind, e, i, h), x, y, dir, n, kind, e, i, h, k + 1)
    }
}

/// calculate_filter_parameters for a key frame macroblock: the edge limit
/// (the filter level), the interior limit and the high edge variance
/// threshold.
pub open spec fn clamp63(x: int) -> int { if x < 0 { 0 } else if x > 63 { 63 } else { x } }

pub open spec fn filter_level(hd: Hdr, mb: Mb) -> int {
    let base = if !hd.seg.enabled { hd.filt.level }
               else if hd.seg.abs { hd.seg.lf[mb.segment as int] }
               else { hd.filt.level + hd.seg.lf[mb.segment as int] };
    let l1 = clamp63(base);
    let l2 = if hd.filt.delta { l1 + hd.filt.ref_delta[0] + if mb.y_mode == m_b() { hd.filt.mode_delta[0] } else { 0 } } else { l1 };
    clamp63(l2)
}

pub open spec fn interior_limit(hd: Hdr, level: int) -> int {
    let sh = hd.filt.sharpness;
    let i1 = if sh != 0 { level / (if sh > 4 { 4int } else { 2 }) } else { level };
    let i2 = if sh != 0 && i1 > 9 - sh { 9 - sh } else { i1 };
    if i2 < 1 { 1 } else { i2 }
}

pub open spec fn hev_threshold(level: int) -> int { (if level >= 15 { 1int } else { 0 }) + (if level >= 40 { 1int } else { 0 }) }

/// The loop filter of one macroblock (filter_row_normal/simple's body),
/// on the three planes.
#[verifier::opaque]
pub open spec fn filter_mb(hd: Hdr, mb: Mb, nz: bool, x: int, y: int, pl: Planes) -> Planes {
    let e = filter_level(hd, mb);
    let i = interior_limit(hd, e);
    let h = hev_threshold(e);
    let inner = nz || mb.y_mode == m_b();
    let (yx, yy, cx, cy) = (x * 16, y * 16, x * 8, y * 8);
    if e == 0 {
        pl
    } else if hd.filt.simple {
        let mbl = (e + 2) * 2 + i;
        let bl = e * 2 + i;
        let s = kind_simple();
        let p0 = pl.y;
        let p1 = if x > 0 { filter_edge(p0, yx, yy, 0, 16, s, mbl, 0, 0, 0) } else { p0 };
        let p2 = if inner { filter_edge(filter_edge(filter_edge(p1, yx + 4, yy, 0, 16, s, bl, 0, 0, 0), yx + 8, yy, 0, 16, s, bl, 0, 0, 0), yx + 12, yy, 0, 16, s, bl, 0, 0, 0) } else { p1 };
        let p3 = if y > 0 { filter_edge(p2, yx, yy, 1, 16, s, mbl, 0, 0, 0) } else { p2 };
        let p4 = if inner { filter_edge(filter_edge(filter_edge(p3, yx, yy + 4, 1, 16, s, bl, 0, 0, 0), yx, yy + 8, 1, 16, s, bl, 0, 0, 0), yx, yy + 12, 1, 16, s, bl, 0, 0, 0) } else { p3 };
        Planes { y: p4, u: pl.u, v: pl.v }
    } else {
        let mbk = kind_mb();
        let sub = kind_sub();
        // Left edge, inner vertical edges, top edge, inner horizontal edges.
        let (y1, u1, v1) = if x > 0 {
            (filter_edge(pl.y, yx, yy, 0, 16, mbk, e + 2, i, h, 0),
             filter_edge(pl.u, cx, cy, 0, 8, mbk, e + 2, i, h, 0),
             filter_edge(pl.v, cx, cy, 0, 8, mbk, e + 2, i, h, 0))
        } else { (pl.y, pl.u, pl.v) };
        let (y2, u2, v2) = if inner {
            (filter_edge(filter_edge(filter_edge(y1, yx + 4, yy, 0, 16, sub, e, i, h, 0), yx + 8, yy, 0, 16, sub, e, i, h, 0), yx + 12, yy, 0, 16, sub, e, i, h, 0),
             filter_edge(u1, cx + 4, cy, 0, 8, sub, e, i, h, 0),
             filter_edge(v1, cx + 4, cy, 0, 8, sub, e, i, h, 0))
        } else { (y1, u1, v1) };
        let (y3, u3, v3) = if y > 0 {
            (filter_edge(y2, yx, yy, 1, 16, mbk, e + 2, i, h, 0),
             filter_edge(u2, cx, cy, 1, 8, mbk, e + 2, i, h, 0),
             filter_edge(v2, cx, cy, 1, 8, mbk, e + 2, i, h, 0))
        } else { (y2, u2, v2) };
        let (y4, u4, v4) = if inner {
            (filter_edge(filter_edge(filter_edge(y3, yx, yy + 4, 1, 16, sub, e, i, h, 0), yx, yy + 8, 1, 16, sub, e, i, h, 0), yx, yy + 12, 1, 16, sub, e, i, h, 0),
             filter_edge(u3, cx, cy + 4, 1, 8, sub, e, i, h, 0),
             filter_edge(v3, cx, cy + 4, 1, 8, sub, e, i, h, 0))
        } else { (y3, u3, v3) };
        Planes { y: y4, u: u4, v: v4 }
    }
}

/// Row `y`'s macroblocks from the `x`-th.
pub open spec fn filter_row(hd: Hdr, mbs: Seq<Seq<Mb>>, nz: Seq<Seq<bool>>, mbw: int, x: int, y: int, pl: Planes) -> Planes
    decreases mbw - x,
{
    if x < 0 || x >= mbw { pl } else {
        filter_row(hd, mbs, nz, mbw, x + 1, y, filter_mb(hd, mbs[y][x], nz[y][x], x, y, pl))
    }
}

/// vp8_dixie_loopfilter_process_row over the rows from the `y`-th; none
/// at all if the frame's level is 0.
pub open spec fn loop_filter(hd: Hdr, mbs: Seq<Seq<Mb>>, nz: Seq<Seq<bool>>, mbw: int, mbh: int, y: int, pl: Planes) -> Planes
    decreases mbh - y,
{
    if hd.filt.level == 0 || y < 0 || y >= mbh { pl } else {
        loop_filter(hd, mbs, nz, mbw, mbh, y + 1, filter_row(hd, mbs, nz, mbw, 0, y, pl))
    }
}

// ----------------------------------------------------------------- a frame

/// A decoded frame: `w` x `h` luma, chroma `(w+1)/2` x `(h+1)/2`, as rows.
pub struct Frame {
    pub w: nat,
    pub h: nat,
    pub y: Plane,
    pub u: Plane,
    pub v: Plane,
}

pub open spec fn crop(p: Plane, w: nat, h: nat) -> Plane {
    Seq::new(h, |r: int| p[r].subrange(0, w as int))
}

/// Before the first macroblock: zero planes, the token partitions' readers
/// at their starts, no token contexts.
pub open spec fn dec0(ps: Seq<Seq<u8>>, mbw: int, mbh: int) -> Dec {
    Dec {
        pl: Planes { y: zero_plane(mbw * 16, mbh * 16), u: zero_plane(mbw * 8, mbh * 8), v: zero_plane(mbw * 8, mbh * 8) },
        ps: Seq::new(ps.len(), |k: int| b_init(ps[k])),
        above: Seq::new(mbw as nat, |x: int| zeros9()),
        left: zeros9(),
        nz: Seq::empty(),
    }
}

/// The frame's planes before cropping.
pub open spec fn planes(b: Seq<u8>) -> Option<(Hdr, Planes)> {
    match header(b) {
        None => None,
        Some((hd, p0, s0, ps)) => {
            let mbw = ((hd.w + 15) / 16) as int;
            let mbh = ((hd.h + 15) / 16) as int;
            let (mbs, _s) = modes(hd, p0, s0, mbw as nat, mbh as nat, Seq::empty());
            let d = decode_rows(hd, ps, mbs, mbw, mbh, 0, dec0(ps, mbw, mbh));
            Some((hd, loop_filter(hd, mbs, d.nz, mbw, mbh, 0, d.pl)))
        },
    }
}

/// A VP8 key frame, decoded as RFC 6386's reference decoder does; None
/// where it reports an error.
pub open spec fn vp8(b: Seq<u8>) -> Option<Frame> {
    match planes(b) {
        None => None,
        Some((hd, pl)) => {
            let cw = (hd.w + 1) / 2;
            let ch = (hd.h + 1) / 2;
            Some(Frame { w: hd.w, h: hd.h, y: crop(pl.y, hd.w, hd.h), u: crop(pl.u, cw, ch), v: crop(pl.v, cw, ch) })
        },
    }
}

} // verus!
