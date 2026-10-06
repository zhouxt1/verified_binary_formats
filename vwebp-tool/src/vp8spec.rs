//! The executable spec for lossy WebP: decoding one VP8 key frame (the
//! payload of a WebP "VP8 " chunk) to its Y'CbCr 4:2:0 planes.
//!
//! RFC 6386 section 1: "The bitstream is defined by the reference source
//! code and not this narrative." So this is a transcription of the RFC's
//! reference decoder (section 20, "dixie"), restricted to key frames, the
//! only frames a WebP file holds. It is written for reading, not speed: the
//! mode and token data are parsed for the whole frame first, the frame is
//! then reconstructed macroblock by macroblock without the loop filter, and
//! the loop filter then runs over the whole frame. dixie interleaves the
//! three by rows, which gives the same result: intra prediction reads only
//! unfiltered pixels (dixie filters row r-1 after predicting row r), and the
//! filter of a row reads nothing below it.
//!
//! Where dixie prepares out-of-frame pixels by writing into a border around
//! the frame (fixup_left, fixup_above, copy_down and the extension of each
//! row), this spec states the value each predictor reads (`Edge`); see the
//! comments there. The difftest against dixie itself (difftest/webp/rfc)
//! checks the two agree.
//!
//! The Verus spec will mirror this file function by function.
//!
//! Alongside the frame, `vp8_lib` computes the `lib` flag: libwebp
//! (v1.6.0) decodes the same frame to the same planes. libwebp's VP8
//! decoder is not dixie: it refuses some frames dixie decodes, and differs
//! from it on a few others. `Notes` lists each such point, recorded as the
//! spec meets it; the flag is that none occurred. See difftest/webp/README.md.
use crate::vp8tab::*;
use std::cell::RefCell;

/// Where libwebp's decoder parts from dixie's, met while decoding a frame.
#[derive(Default, Clone, Debug)]
pub struct Notes {
    /// show_frame is 0: libwebp refuses ("Frame not displayable").
    pub hidden: bool,
    /// The last token partition is empty: libwebp refuses (ParsePartitions
    /// wants part_start < buf_end).
    pub last_empty: bool,
    /// libwebp's bit reader reached its end of data in the first partition
    /// or a token partition some row reads (it refuses: "Premature
    /// end-of-file"); dixie reads zeros past the end.
    pub eof: bool,
    /// A partition that is read from has 1 byte, which dixie does not read
    /// (init_bool_decoder) and libwebp does.
    pub one_byte: bool,
    /// A partition some row reads starts with 0xff. No encoder writes that:
    /// the decoder's value starts outside its interval (value >= range <<
    /// 8), and stays outside. dixie's 32-bit `value` then overflows and
    /// wraps (as this spec's does); libwebp's 64-bit window and FFmpeg's
    /// reader part from it and from each other.
    pub ff_start: bool,
    /// A macroblock with coefficients uses a segment whose dixie factors are
    /// 0 (`factors`); libwebp's are those of index 0.
    pub zero_factors: bool,
    /// Segmentation is on but the frame sends no segment data, and the
    /// frame's quantizer index is not 0: libwebp starts a key frame's
    /// segment header with absolute values (ResetSegmentHeader sets
    /// absolute_delta), so its segments get quantizer index 0; dixie (and
    /// libvpx) start with deltas, so they get the frame's index. (For the
    /// filter level the same rule is in `lib_level`.)
    pub absolute: bool,
    /// An inverse transform had an intermediate value outside 16 bits:
    /// dixie keeps its first pass in 16 bits, libwebp's C code in `int` and
    /// its SSE2 code in 16 bits throughout.
    pub wide: bool,
    /// A macroblock's loop filter level differs: dixie clamps the level to
    /// 0..63 after the segment's adjustment and again after the deltas,
    /// libwebp only after the deltas (PrecomputeFilterStrengths).
    pub level: bool,
    /// Whether a macroblock's inner edges are filtered differs: dixie
    /// filters them if any block (the Y2 block too) had a token other than
    /// an immediate end of block, libwebp if a Y or chroma block has a
    /// coefficient past the first or a nonzero first coefficient (the Y
    /// blocks' taken from the Y2 block's inverse WHT) (ParseResiduals).
    pub inner: bool,
}

impl Notes {
    pub fn lib(&self) -> bool {
        !(self.hidden || self.last_empty || self.eof || self.one_byte || self.ff_start || self.zero_factors || self.absolute || self.wide
            || self.level || self.inner)
    }
}

thread_local! {
    pub static NOTES: RefCell<Notes> = RefCell::new(Notes::default());
}

fn note(f: impl FnOnce(&mut Notes)) {
    NOTES.with(|n| f(&mut n.borrow_mut()));
}

/// A decoded frame: `w` x `h` luma samples, and chroma planes of
/// `(w+1)/2` x `(h+1)/2`, row by row.
pub struct Frame {
    pub w: usize,
    pub h: usize,
    pub y: Vec<u8>,
    pub u: Vec<u8>,
    pub v: Vec<u8>,
}

// ---------------------------------------------------------------------------
// The boolean entropy decoder (20.2, bool_decoder.h).

pub struct Bool<'a> {
    buf: &'a [u8],
    pos: usize,
    range: u32,
    value: u32,
    bit_count: u32,
    /// Bytes the decoder wanted past the end of its buffer (it shifts in
    /// zeros for them).
    pub past: u64,
    /// The partition's real length, and the bits consumed (normalization
    /// shifts): libwebp's reader (VP8GetBit, VP8LoadFinalBytes) sets its
    /// eof when a read starts with every byte loaded and fewer than 8 bits
    /// left in its window, that is with `shifts >= 8 * n - 7`; an empty
    /// partition is at its end from the start (VP8InitBitReader).
    pub n: usize,
    pub shifts: u64,
    pub lib_eof: bool,
    /// Reads so far.
    pub reads: u64,
    /// The buffer starts with 0xff (`Notes::ff_start`).
    pub ff_start: bool,
}

impl<'a> Bool<'a> {
    /// init_bool_decoder: a buffer of fewer than 2 bytes is not read at all.
    pub fn new(buf: &'a [u8]) -> Self {
        let (n, lib_eof, ff_start) = (buf.len(), buf.is_empty(), buf.len() >= 2 && buf[0] == 0xff);
        if buf.len() >= 2 {
            let value = (buf[0] as u32) << 8 | buf[1] as u32;
            Bool { buf, pos: 2, range: 255, value, bit_count: 0, past: 0, n, shifts: 0, lib_eof, reads: 0, ff_start }
        } else {
            Bool { buf: &[], pos: 0, range: 255, value: 0, bit_count: 0, past: 0, n, shifts: 0, lib_eof, reads: 0, ff_start }
        }
    }

    /// bool_get.
    pub fn get(&mut self, prob: u8) -> bool {
        if self.shifts + 7 >= 8 * self.n as u64 {
            self.lib_eof = true;
        }
        self.reads += 1;
        let split = 1 + (((self.range - 1) * prob as u32) >> 8);
        let big = split << 8;
        let bit = if self.value >= big {
            self.range -= split;
            self.value -= big;
            true
        } else {
            self.range = split;
            false
        };
        while self.range < 128 {
            // A u32, as dixie's `unsigned int`: bits shifted out of the top
            // are lost (only possible from a start outside the interval,
            // `Notes::ff_start`).
            self.value <<= 1;
            self.range <<= 1;
            self.shifts += 1;
            self.bit_count += 1;
            if self.bit_count == 8 {
                self.bit_count = 0;
                if self.pos < self.buf.len() {
                    self.value |= self.buf[self.pos] as u32;
                    self.pos += 1;
                } else {
                    self.past += 1;
                }
            }
        }
        bit
    }

    pub fn bit(&mut self) -> bool {
        self.get(128)
    }

    /// bool_get_uint: `n` bits, most significant first.
    pub fn uint(&mut self, n: u32) -> i32 {
        let mut z = 0;
        for i in (0..n).rev() {
            z |= (self.bit() as i32) << i;
        }
        z
    }

    /// bool_get_int: a magnitude of `n` bits, then a sign.
    pub fn int(&mut self, n: u32) -> i32 {
        let z = self.uint(n);
        if self.bit() { -z } else { z }
    }

    /// bool_maybe_get_int: a flag, then (if set) `int(n)`; else 0.
    pub fn maybe_int(&mut self, n: u32) -> i32 {
        if self.bit() { self.int(n) } else { 0 }
    }

    /// bool_read_tree: leaves are stored negated (so a leaf 0 is -0 = 0).
    pub fn tree(&mut self, t: &[i32], p: &[u8]) -> usize {
        let mut i = 0i32;
        loop {
            i = t[(i + self.get(p[(i >> 1) as usize]) as i32) as usize];
            if i <= 0 {
                return (-i) as usize;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Headers (20.4, dixie.c).

// 16x16 luma and 8x8 chroma modes (dixie.h, enum prediction_mode).
pub const DC_PRED: usize = 0;
pub const V_PRED: usize = 1;
pub const H_PRED: usize = 2;
pub const TM_PRED: usize = 3;
pub const B_PRED: usize = 4;
// 4x4 luma subblock modes.
pub const B_DC_PRED: usize = 0;
pub const B_TM_PRED: usize = 1;
pub const B_VE_PRED: usize = 2;
pub const B_HE_PRED: usize = 3;
pub const B_LD_PRED: usize = 4;
pub const B_RD_PRED: usize = 5;
pub const B_VR_PRED: usize = 6;
pub const B_VL_PRED: usize = 7;
pub const B_HD_PRED: usize = 8;
pub const B_HU_PRED: usize = 9;

#[derive(Default, Clone, Debug)]
pub struct Segment {
    pub enabled: bool,
    pub update_map: bool,
    pub update_data: bool,
    pub abs: bool,
    pub tree_probs: [u8; 3],
    pub lf_level: [i32; 4],
    pub quant_idx: [i32; 4],
}

#[derive(Default, Clone, Debug)]
pub struct Filter {
    pub simple: bool,
    pub level: i32,
    pub sharpness: i32,
    pub delta_enabled: bool,
    pub ref_delta: [i32; 4],
    pub mode_delta: [i32; 4],
}

#[derive(Default, Clone, Debug)]
pub struct Quant {
    pub q_index: i32,
    pub y1_dc: i32,
    pub y2_dc: i32,
    pub y2_ac: i32,
    pub uv_dc: i32,
    pub uv_ac: i32,
}

/// Dequantization factors, [Y1, UV, Y2] x [DC, AC] (struct dequant_factors).
pub type Factors = [[i32; 2]; 3];
pub const Y1: usize = 0;
pub const UV: usize = 1;
pub const Y2: usize = 2;

#[derive(Debug)]
pub struct Header {
    pub w: usize,
    pub h: usize,
    /// The frame tag's version: it chooses inter prediction's filters
    /// (dixie's predict init), which a key frame has none of.
    #[allow(dead_code)]
    pub version: u32,
    pub show: bool,
    pub seg: Segment,
    pub filter: Filter,
    pub quant: Quant,
    pub coeff_probs: Vec<u8>,
    pub skip_prob: Option<u8>,
}

fn clamp_q(q: i32) -> usize {
    q.clamp(0, 127) as usize
}

/// dixie's cache leaves a segment's factors 0 (see `factors`).
pub fn zero_factors(q: i32, qh: &Quant) -> bool {
    let delta_update =
        qh.q_index != 0 || qh.y1_dc != 0 || qh.y2_dc != 0 || qh.y2_ac != 0 || qh.uv_dc != 0 || qh.uv_ac != 0;
    q == -1 && !delta_update
}

/// dequant_init, for one segment's quantizer index `q`. dixie keeps the
/// factors of each segment between frames and recomputes them only if the
/// index changed or `delta_update`: its cache starts at index -1 with
/// factors 0 (dequant_global_init, calloc). So a segment whose index is -1
/// in a first frame with `delta_update` clear keeps factors 0: every
/// coefficient dequantizes to 0.
pub fn factors(q: i32, qh: &Quant) -> Factors {
    if zero_factors(q, qh) {
        return [[0; 2]; 3];
    }
    let mut f = [
        [DC_Q[clamp_q(q + qh.y1_dc)], AC_Q[clamp_q(q)]],
        [DC_Q[clamp_q(q + qh.uv_dc)], AC_Q[clamp_q(q + qh.uv_ac)]],
        [DC_Q[clamp_q(q + qh.y2_dc)] * 2, AC_Q[clamp_q(q + qh.y2_ac)] * 155 / 100],
    ];
    if f[Y2][1] < 8 {
        f[Y2][1] = 8;
    }
    if f[UV][0] > 132 {
        f[UV][0] = 132;
    }
    f
}

/// The token partitions (decode_and_init_token_partitions): `rest` is the
/// frame after the first partition. The sizes of all but the last are
/// 3-byte little-endian numbers at its start; the last takes the rest.
fn partitions<'a>(rest: &'a [u8], n: usize) -> Option<Vec<&'a [u8]>> {
    let mut sz = rest.len();
    if sz < 3 * (n - 1) {
        return None;
    }
    sz -= 3 * (n - 1);
    let mut at = 3 * (n - 1);
    let mut parts = Vec::new();
    for i in 0..n {
        let psz = if i < n - 1 {
            rest[3 * i] as usize | (rest[3 * i + 1] as usize) << 8 | (rest[3 * i + 2] as usize) << 16
        } else {
            sz
        };
        if sz < psz {
            return None;
        }
        sz -= psz;
        parts.push(&rest[at..at + psz]);
        at += psz;
    }
    Some(parts)
}

/// vp8_parse_frame_header and the key frame part of decode_frame up to the
/// per-macroblock data: the header, the first partition's reader positioned
/// after it, and the token partitions. None where dixie reports an error.
pub fn header(b: &[u8]) -> Option<(Header, Bool<'_>, Vec<&[u8]>)> {
    if b.len() < 10 {
        return None;
    }
    let raw = b[0] as u32 | (b[1] as u32) << 8 | (b[2] as u32) << 16;
    let key = raw & 1 == 0;
    let version = (raw >> 1) & 3;
    let experimental = (raw >> 3) & 1 == 1;
    let show = (raw >> 4) & 1 == 1;
    let part0 = (raw >> 5) as usize;
    if b.len() <= part0 + if key { 10 } else { 3 } {
        return None;
    }
    if !key {
        return None; // WebP holds key frames only (dixie cannot start from another)
    }
    if b[3] != 0x9d || b[4] != 0x01 || b[5] != 0x2a {
        return None;
    }
    let raw = u32::from_le_bytes([b[6], b[7], b[8], b[9]]);
    let (w, h) = ((raw & 0x3fff) as usize, ((raw >> 16) & 0x3fff) as usize);
    if w == 0 || h == 0 {
        return None;
    }
    if experimental {
        return None;
    }
    let data = &b[10..];
    let mut bd = Bool::new(&data[..part0]);
    // Color space and clamping type: dixie supports neither being set.
    if bd.uint(2) != 0 {
        return None;
    }
    // decode_segmentation_header.
    let mut seg = Segment::default();
    seg.enabled = bd.bit();
    if seg.enabled {
        seg.update_map = bd.bit();
        seg.update_data = bd.bit();
        if seg.update_data {
            seg.abs = bd.bit();
            for i in 0..4 {
                seg.quant_idx[i] = bd.maybe_int(7);
            }
            for i in 0..4 {
                seg.lf_level[i] = bd.maybe_int(6);
            }
        }
        if seg.update_map {
            for i in 0..3 {
                seg.tree_probs[i] = if bd.bit() { bd.uint(8) as u8 } else { 255 };
            }
        }
    }
    // decode_loopfilter_header.
    let mut filter = Filter { simple: bd.bit(), level: bd.uint(6), sharpness: bd.uint(3), ..Filter::default() };
    filter.delta_enabled = bd.bit();
    if filter.delta_enabled && bd.bit() {
        for i in 0..4 {
            filter.ref_delta[i] = bd.maybe_int(6);
        }
        for i in 0..4 {
            filter.mode_delta[i] = bd.maybe_int(6);
        }
    }
    let nparts = 1usize << bd.uint(2);
    let parts = partitions(&data[part0..], nparts)?;
    if parts[nparts - 1].is_empty() {
        note(|n| n.last_empty = true);
    }
    // decode_quantizer_header.
    let quant = Quant {
        q_index: bd.uint(7),
        y1_dc: bd.maybe_int(4),
        y2_dc: bd.maybe_int(4),
        y2_ac: bd.maybe_int(4),
        uv_dc: bd.maybe_int(4),
        uv_ac: bd.maybe_int(4),
    };
    // decode_reference_header: on a key frame, only refresh_entropy is read.
    let _refresh_entropy = bd.bit();
    // decode_entropy_header.
    let mut coeff_probs = DEFAULT_COEFF_PROBS.to_vec();
    for i in 0..coeff_probs.len() {
        if bd.get(COEFF_UPDATE_PROBS[i]) {
            coeff_probs[i] = bd.uint(8) as u8;
        }
    }
    let skip_prob = if bd.bit() { Some(bd.uint(8) as u8) } else { None };
    Some((Header { w, h, version, show, seg, filter, quant, coeff_probs, skip_prob }, bd, parts))
}

// ---------------------------------------------------------------------------
// Per-macroblock modes (20.11, modemv.c: the key frame parts).

#[derive(Clone, Default)]
pub struct Mb {
    pub segment: usize,
    pub skip: bool,
    pub y_mode: usize,
    pub uv_mode: usize,
    /// The 16 subblock modes, if `y_mode == B_PRED`.
    pub b_modes: [usize; 16],
    /// Coefficients, dequantized: 16 Y blocks, 4 U, 4 V, then Y2 (unless
    /// `y_mode == B_PRED`), 16 each in raster order within the block.
    pub coeffs: Vec<i16>,
    /// dixie's eob_mask != 0: some block had a token other than an
    /// immediate end of block.
    pub nonzero: bool,
    /// Each block's final token position (`block`), for `Notes::inner`.
    pub ends: [usize; 25],
}

/// The subblock mode a macroblock that is not B_PRED implies for its
/// neighbours' contexts (above_block_mode, left_block_mode).
fn implied_b_mode(y_mode: usize) -> usize {
    match y_mode {
        DC_PRED => B_DC_PRED,
        V_PRED => B_VE_PRED,
        H_PRED => B_HE_PRED,
        TM_PRED => B_TM_PRED,
        _ => unreachable!("B_PRED has its own subblock modes"),
    }
}

/// The context of subblock `b`: the modes of the subblocks above and to
/// its left. Out of the frame, a macroblock counts as DC_PRED (dixie's
/// calloc'd border).
fn b_context(mbs: &[Mb], mbw: usize, mbx: usize, mby: usize, this: &[usize; 16], b: usize) -> (usize, usize) {
    let above = if b >= 4 {
        this[b - 4]
    } else if mby == 0 {
        B_DC_PRED
    } else {
        let a = &mbs[(mby - 1) * mbw + mbx];
        if a.y_mode == B_PRED { a.b_modes[b + 12] } else { implied_b_mode(a.y_mode) }
    };
    let left = if b & 3 != 0 {
        this[b - 1]
    } else if mbx == 0 {
        B_DC_PRED
    } else {
        let l = &mbs[mby * mbw + mbx - 1];
        if l.y_mode == B_PRED { l.b_modes[b + 3] } else { implied_b_mode(l.y_mode) }
    };
    (above, left)
}

/// vp8_dixie_modemv_process_row over the frame, for a key frame.
fn modes(hd: &Header, bd: &mut Bool, mbw: usize, mbh: usize) -> Vec<Mb> {
    let mut mbs: Vec<Mb> = Vec::with_capacity(mbw * mbh);
    for mby in 0..mbh {
        for mbx in 0..mbw {
            let mut mb = Mb::default();
            if hd.seg.update_map {
                let p = &hd.seg.tree_probs;
                mb.segment = if bd.get(p[0]) { 2 + bd.get(p[2]) as usize } else { bd.get(p[1]) as usize };
            }
            if let Some(p) = hd.skip_prob {
                mb.skip = bd.get(p);
            }
            mb.y_mode = bd.tree(&KF_Y_MODE_TREE, &KF_Y_MODE_PROBS);
            if mb.y_mode == B_PRED {
                for b in 0..16 {
                    let (a, l) = b_context(&mbs, mbw, mbx, mby, &mb.b_modes, b);
                    let p = &KF_B_MODE_PROBS[(a * 10 + l) * 9..(a * 10 + l) * 9 + 9];
                    mb.b_modes[b] = bd.tree(&B_MODE_TREE, p);
                }
            }
            mb.uv_mode = bd.tree(&UV_MODE_TREE, &KF_UV_MODE_PROBS);
            mbs.push(mb);
        }
    }
    mbs
}

// ---------------------------------------------------------------------------
// Tokens (20.16, tokens.c).

const ZIGZAG: [usize; 16] = [0, 1, 4, 8, 5, 2, 3, 6, 9, 12, 13, 10, 7, 11, 14, 15];
const BANDS: [usize; 17] = [0, 1, 2, 3, 6, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 7, 0];
/// The extra bits of DCT_VAL_CATEGORY1..6: the least value and the
/// probabilities of the bits, most significant first.
const CAT_BASE: [i32; 6] = [5, 7, 11, 19, 35, 67];
const CAT_PROBS: [&[u8]; 6] = [
    &[159],
    &[165, 145],
    &[173, 148, 140],
    &[176, 155, 140, 135],
    &[180, 157, 141, 134, 130],
    &[254, 254, 243, 230, 196, 177, 153, 140, 133, 130, 129],
];
/// Which of the 9 entries of a left or above token context each block uses
/// (4 Y, 2 U, 2 V, Y2).
const LEFT_CTX: [usize; 25] = [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8];
const ABOVE_CTX: [usize; 25] = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 4, 5, 6, 7, 6, 7, 8];

/// The 11 probabilities for block type `ty`, coefficient position `c`'s
/// band and context `ctx`.
fn probs(p: &[u8], ty: usize, c: usize, ctx: usize) -> &[u8] {
    let at = ((ty * 8 + BANDS[c]) * 3 + ctx) * 11;
    &p[at..at + 11]
}

/// One block's tokens (the body of decode_mb_tokens, from BLOCK_LOOP to
/// BLOCK_FINISHED): the dequantized coefficients (as dixie, the product is
/// stored in 16 bits) and the final position `c`. A zero token is never
/// followed by an end of block; a block runs to position 15 at most, where
/// it ends without a further end-of-block token and `c` stays 15.
fn block(bd: &mut Bool, p: &[u8], ty: usize, ctx: usize, dqf: [i32; 2], out: &mut [i16]) -> usize {
    let mut c = if ty == 0 { 1 } else { 0 };
    let mut pr = probs(p, ty, c, ctx);
    loop {
        if !bd.get(pr[0]) {
            return c; // end of block
        }
        // Zero tokens.
        while !bd.get(pr[1]) {
            if c == 15 {
                return 15;
            }
            c += 1;
            pr = probs(p, ty, c, 0);
        }
        let v: i32 = if !bd.get(pr[2]) {
            1
        } else if !bd.get(pr[3]) {
            if !bd.get(pr[4]) {
                2
            } else if !bd.get(pr[5]) {
                3
            } else {
                4
            }
        } else {
            let cat = if !bd.get(pr[6]) {
                if !bd.get(pr[7]) { 0 } else { 1 }
            } else if !bd.get(pr[8]) {
                if !bd.get(pr[9]) { 2 } else { 3 }
            } else if !bd.get(pr[10]) {
                4
            } else {
                5
            };
            let n = CAT_PROBS[cat].len();
            let mut val = CAT_BASE[cat];
            for (i, &q) in CAT_PROBS[cat].iter().enumerate() {
                val += (bd.get(q) as i32) << (n - 1 - i);
            }
            val
        };
        let signed = if bd.bit() { -v } else { v };
        out[ZIGZAG[c]] = (signed * dqf[(c > 0) as usize]) as i16;
        if c == 15 {
            return 15;
        }
        c += 1;
        pr = probs(p, ty, c, if v == 1 { 1 } else { 2 });
    }
}

/// vp8_dixie_tokens_process_row over the frame: each macroblock row reads
/// the token partition `row % n`.
fn tokens(hd: &Header, parts: &mut [Bool], mbs: &mut [Mb], mbw: usize, mbh: usize) {
    let qs: Vec<i32> = (0..if hd.seg.enabled { 4 } else { 1 })
        .map(|i| {
            if !hd.seg.enabled {
                hd.quant.q_index
            } else if hd.seg.abs {
                hd.seg.quant_idx[i]
            } else {
                hd.quant.q_index + hd.seg.quant_idx[i]
            }
        })
        .collect();
    let fs: Vec<Factors> = qs.iter().map(|&q| factors(q, &hd.quant)).collect();
    if hd.seg.enabled && !hd.seg.update_data && hd.quant.q_index != 0 {
        note(|n| n.absolute = true);
    }
    let zs: Vec<bool> = qs.iter().map(|&q| zero_factors(q, &hd.quant)).collect();
    let mut above = vec![[0u8; 9]; mbw];
    for mby in 0..mbh {
        let bd = &mut parts[mby % parts.len()];
        let mut left = [0u8; 9];
        for mbx in 0..mbw {
            let mb = &mut mbs[mby * mbw + mbx];
            mb.coeffs = vec![0i16; 25 * 16];
            let a = &mut above[mbx];
            if mb.skip {
                for i in 0..8 {
                    left[i] = 0;
                    a[i] = 0;
                }
                if mb.y_mode != B_PRED {
                    left[8] = 0;
                    a[8] = 0;
                }
                mb.nonzero = false;
                continue;
            }
            let f = fs[mb.segment];
            if zs[mb.segment] {
                note(|n| n.zero_factors = true);
            }
            let mut nonzero = false;
            // (block index, type, factors): Y2 first unless B_PRED, then Y,
            // then U and V.
            let mut order: Vec<(usize, usize, [i32; 2])> = Vec::new();
            if mb.y_mode != B_PRED {
                order.push((24, 1, f[Y2]));
                order.extend((0..16).map(|i| (i, 0, f[Y1])));
            } else {
                order.extend((0..16).map(|i| (i, 3, f[Y1])));
            }
            order.extend((16..24).map(|i| (i, 2, f[UV])));
            for (i, ty, dqf) in order {
                let ctx = (left[LEFT_CTX[i]] + a[ABOVE_CTX[i]]) as usize;
                let c = block(bd, &hd.coeff_probs, ty, ctx, dqf, &mut mb.coeffs[i * 16..i * 16 + 16]);
                mb.ends[i] = c;
                let first = if ty == 0 { 1 } else { 0 };
                let t = (c != first) as u8;
                nonzero |= t == 1;
                left[LEFT_CTX[i]] = t;
                a[ABOVE_CTX[i]] = t;
            }
            mb.nonzero = nonzero;
        }
    }
}

// ---------------------------------------------------------------------------
// Inverse transforms (20.8, idct_add.c). Intermediate results are stored in
// 16 bits, as dixie's `short` arrays.

/// vp8_dixie_walsh.
pub fn iwht(input: &[i16]) -> [i16; 16] {
    let mut o = [0i16; 16];
    for i in 0..4 {
        let (i0, i4, i8, i12) = (input[i] as i32, input[4 + i] as i32, input[8 + i] as i32, input[12 + i] as i32);
        let (a1, b1, c1, d1) = (i0 + i12, i4 + i8, i4 - i8, i0 - i12);
        wide(&[a1, b1, c1, d1, a1 + b1, c1 + d1, a1 - b1, d1 - c1]);
        o[i] = (a1 + b1) as i16;
        o[4 + i] = (c1 + d1) as i16;
        o[8 + i] = (a1 - b1) as i16;
        o[12 + i] = (d1 - c1) as i16;
    }
    let mut r = [0i16; 16];
    for i in 0..4 {
        let s = &o[4 * i..4 * i + 4];
        let (a1, b1, c1, d1) = (
            s[0] as i32 + s[3] as i32,
            s[1] as i32 + s[2] as i32,
            s[1] as i32 - s[2] as i32,
            s[0] as i32 - s[3] as i32,
        );
        wide(&[a1, b1, c1, d1, a1 + b1 + 3, c1 + d1 + 3, a1 - b1 + 3, d1 - c1 + 3]);
        r[4 * i] = ((a1 + b1 + 3) >> 3) as i16;
        r[4 * i + 1] = ((c1 + d1 + 3) >> 3) as i16;
        r[4 * i + 2] = ((a1 - b1 + 3) >> 3) as i16;
        r[4 * i + 3] = ((d1 - c1 + 3) >> 3) as i16;
    }
    r
}

/// Some intermediate value of an inverse transform is outside 16 bits.
fn wide(v: &[i32]) {
    if v.iter().any(|&x| x < -32768 || x > 32767) {
        note(|n| n.wide = true);
    }
}

const C1: i32 = 20091; // cospi8sqrt2minus1
const S1: i32 = 35468; // sinpi8sqrt2

/// vp8_dixie_idct_add: the residual of a 4x4 block added to the prediction
/// in `px` (at `at`, rows `stride` apart), clamped to 0..255.
pub fn idct_add(coeffs: &[i16], px: &mut [u8], at: usize, stride: usize) {
    let mut t = [0i16; 16];
    for i in 0..4 {
        let (i0, i4, i8, i12) = (coeffs[i] as i32, coeffs[4 + i] as i32, coeffs[8 + i] as i32, coeffs[12 + i] as i32);
        let a1 = i0 + i8;
        let b1 = i0 - i8;
        let c1 = ((i4 * S1) >> 16) - (i12 + ((i12 * C1) >> 16));
        let d1 = (i4 + ((i4 * C1) >> 16)) + ((i12 * S1) >> 16);
        wide(&[a1, b1, c1, d1, a1 + d1, a1 - d1, b1 + c1, b1 - c1]);
        t[i] = (a1 + d1) as i16;
        t[12 + i] = (a1 - d1) as i16;
        t[4 + i] = (b1 + c1) as i16;
        t[8 + i] = (b1 - c1) as i16;
    }
    for i in 0..4 {
        let s = &t[4 * i..4 * i + 4];
        let (s0, s1, s2, s3) = (s[0] as i32, s[1] as i32, s[2] as i32, s[3] as i32);
        let a1 = s0 + s2;
        let b1 = s0 - s2;
        let c1 = ((s1 * S1) >> 16) - (s3 + ((s3 * C1) >> 16));
        let d1 = (s1 + ((s1 * C1) >> 16)) + ((s3 * S1) >> 16);
        wide(&[a1, b1, c1, d1, a1 + d1 + 4, a1 - d1 + 4, b1 + c1 + 4, b1 - c1 + 4]);
        let row = at + i * stride;
        let add = |p: u8, r: i32| (p as i32 + r).clamp(0, 255) as u8;
        px[row] = add(px[row], (a1 + d1 + 4) >> 3);
        px[row + 3] = add(px[row + 3], (a1 - d1 + 4) >> 3);
        px[row + 1] = add(px[row + 1], (b1 + c1 + 4) >> 3);
        px[row + 2] = add(px[row + 2], (b1 - c1 + 4) >> 3);
    }
}

// ---------------------------------------------------------------------------
// Intra prediction (20.14, predict.c).

/// A plane of whole macroblocks.
pub struct Plane {
    pub w: usize,
    pub px: Vec<u8>,
}

impl Plane {
    fn at(&self, x: usize, y: usize) -> u8 {
        self.px[y * self.w + x]
    }
}

/// What a predictor reads around an `n` x `n` block at (`x`, `y`): the row
/// above (`above[0..n]`, and for 4x4 subblocks the 4 pixels above-right,
/// `above[n..n+4]`), the column to the left, and the pixel above-left.
///
/// Outside the frame (dixie's border), the row above is 127, the column to
/// the left 129, and the pixel above-left 127 in the first row, else 129 in
/// the first column (fixup_left, fixup_above, and the 127 dixie writes above
/// the top left macroblock).
struct Edge {
    above: [u8; 20],
    left: [u8; 16],
    above_left: u8,
}

fn edge(p: &Plane, x: usize, y: usize, n: usize) -> Edge {
    let mut e = Edge { above: [127; 20], left: [129; 16], above_left: 127 };
    if y > 0 {
        for k in 0..n {
            e.above[k] = p.at(x + k, y - 1);
        }
    }
    if x > 0 {
        for k in 0..n {
            e.left[k] = p.at(x - 1, y + k);
        }
    }
    e.above_left = if y == 0 {
        127
    } else if x == 0 {
        129
    } else {
        p.at(x - 1, y - 1)
    };
    e
}

/// predict_dc_nxn, with the edges dixie gives DC_PRED: out of the frame,
/// the column to the left copies the row above and the row above copies
/// the column to the left (fixup_left, fixup_above), so a block on one
/// edge averages the other; the top left block averages 127s and 129s.
fn dc(p: &Plane, x: usize, y: usize, n: usize) -> u8 {
    let e = edge(p, x, y, n);
    let (mut above, mut left) = (e.above, e.left);
    if x == 0 && y > 0 {
        left[..n].copy_from_slice(&above[..n]);
    }
    if y == 0 && x > 0 {
        above[..n].copy_from_slice(&left[..n]);
    }
    let sum: u32 = (0..n).map(|k| above[k] as u32 + left[k] as u32).sum();
    let shift = n.trailing_zeros() + 1;
    ((sum + (n as u32)) >> shift) as u8
}

/// predict_{dc,v,h,tm}_nxn into the `n` x `n` block at (x, y).
fn predict_mb(p: &mut Plane, x: usize, y: usize, n: usize, mode: usize) {
    let e = edge(p, x, y, n);
    let d = if mode == DC_PRED { dc(p, x, y, n) } else { 0 };
    for i in 0..n {
        for j in 0..n {
            p.px[(y + i) * p.w + x + j] = match mode {
                DC_PRED => d,
                V_PRED => e.above[j],
                H_PRED => e.left[i],
                TM_PRED => (e.left[i] as i32 + e.above[j] as i32 - e.above_left as i32).clamp(0, 255) as u8,
                _ => unreachable!("a 16x16 or 8x8 mode"),
            };
        }
    }
}

/// The 4 pixels above-right of subblock `b` of the macroblock at (mbx,
/// mby). Subblocks in the right column (3, 7, 11, 15) all read the ones
/// above-right of subblock 3, from the macroblock row above (copy_down);
/// for the last macroblock of a row these are its last pixel above,
/// repeated (dixie extends each row by 4 pixels), and in the first
/// macroblock row they are 127. Other subblocks read the row above them.
fn above_right(p: &Plane, mbx: usize, mby: usize, b: usize) -> [u8; 4] {
    let (bx, by) = (b & 3, b >> 2);
    let (x, y) = (mbx * 16 + bx * 4, mby * 16 + by * 4);
    if bx < 3 && by > 0 {
        return [p.at(x + 4, y - 1), p.at(x + 5, y - 1), p.at(x + 6, y - 1), p.at(x + 7, y - 1)];
    }
    if mby == 0 {
        return [127; 4];
    }
    let row = mby * 16 - 1;
    let x = if bx < 3 { x + 4 } else { mbx * 16 + 16 };
    if x >= p.w {
        return [p.at(p.w - 1, row); 4];
    }
    [p.at(x, row), p.at(x + 1, row), p.at(x + 2, row), p.at(x + 3, row)]
}

/// The ten 4x4 predictors (predict_*_4x4): `a` is the row above with the
/// pixel above-left first (a[0] = above-left, a[1..9] = above and
/// above-right), `l` the column to the left.
fn predict_4x4(mode: usize, a: &[i32; 9], l: &[i32; 4]) -> [u8; 16] {
    let t = |k: usize| a[k + 1]; // above[k], k in -1..8
    let p = a[0]; // above[-1]
    let avg3 = |x: i32, y: i32, z: i32| ((x + 2 * y + z + 2) >> 2) as u8;
    let avg2 = |x: i32, y: i32| ((x + y + 1) >> 1) as u8;
    let mut o = [0u8; 16];
    let mut set = |r: usize, c: usize, v: u8| o[r * 4 + c] = v;
    match mode {
        B_DC_PRED => {
            let s: i32 = (0..4).map(|k| t(k) + l[k]).sum();
            let v = ((s + 4) >> 3) as u8;
            for r in 0..4 {
                for c in 0..4 {
                    set(r, c, v);
                }
            }
        }
        B_TM_PRED => {
            for r in 0..4 {
                for c in 0..4 {
                    set(r, c, (l[r] + t(c) - p).clamp(0, 255) as u8);
                }
            }
        }
        B_VE_PRED => {
            for c in 0..4 {
                let v = avg3(a[c], a[c + 1], a[c + 2]); // above[c-1], above[c], above[c+1]
                for r in 0..4 {
                    set(r, c, v);
                }
            }
        }
        B_HE_PRED => {
            let v = [avg3(p, l[0], l[1]), avg3(l[0], l[1], l[2]), avg3(l[1], l[2], l[3]), avg3(l[2], l[3], l[3])];
            for r in 0..4 {
                for c in 0..4 {
                    set(r, c, v[r]);
                }
            }
        }
        B_LD_PRED => {
            // pred_k = avg3(above[k], above[k+1], above[k+2]); pred6 uses above[7] twice.
            let pk = |k: usize| if k < 6 { avg3(t(k), t(k + 1), t(k + 2)) } else { avg3(t(6), t(7), t(7)) };
            for r in 0..4 {
                for c in 0..4 {
                    set(r, c, pk(r + c));
                }
            }
        }
        B_RD_PRED => {
            // Edge e[0..9] = l[3], l[2], l[1], l[0], above[-1], above[0..4]; pixel (r, c) = avg3 around e[3 - r + c + 1].
            let e = [l[3], l[2], l[1], l[0], p, t(0), t(1), t(2), t(3)];
            for r in 0..4 {
                for c in 0..4 {
                    let k = 4 - r + c;
                    set(r, c, avg3(e[k - 1], e[k], e[k + 1]));
                }
            }
        }
        B_VR_PRED => {
            let v = [
                [avg2(p, t(0)), avg2(t(0), t(1)), avg2(t(1), t(2)), avg2(t(2), t(3))],
                [avg3(l[0], p, t(0)), avg3(p, t(0), t(1)), avg3(t(0), t(1), t(2)), avg3(t(1), t(2), t(3))],
                [avg3(l[1], l[0], p), avg2(p, t(0)), avg2(t(0), t(1)), avg2(t(1), t(2))],
                [avg3(l[2], l[1], l[0]), avg3(l[0], p, t(0)), avg3(p, t(0), t(1)), avg3(t(0), t(1), t(2))],
            ];
            for r in 0..4 {
                for c in 0..4 {
                    set(r, c, v[r][c]);
                }
            }
        }
        B_VL_PRED => {
            let v = [
                [avg2(t(0), t(1)), avg2(t(1), t(2)), avg2(t(2), t(3)), avg2(t(3), t(4))],
                [avg3(t(0), t(1), t(2)), avg3(t(1), t(2), t(3)), avg3(t(2), t(3), t(4)), avg3(t(3), t(4), t(5))],
                [avg2(t(1), t(2)), avg2(t(2), t(3)), avg2(t(3), t(4)), avg3(t(4), t(5), t(6))],
                [avg3(t(1), t(2), t(3)), avg3(t(2), t(3), t(4)), avg3(t(3), t(4), t(5)), avg3(t(5), t(6), t(7))],
            ];
            for r in 0..4 {
                for c in 0..4 {
                    set(r, c, v[r][c]);
                }
            }
        }
        B_HD_PRED => {
            let v = [
                [avg2(l[0], p), avg3(l[0], p, t(0)), avg3(p, t(0), t(1)), avg3(t(0), t(1), t(2))],
                [avg2(l[1], l[0]), avg3(l[1], l[0], p), avg2(l[0], p), avg3(l[0], p, t(0))],
                [avg2(l[2], l[1]), avg3(l[2], l[1], l[0]), avg2(l[1], l[0]), avg3(l[1], l[0], p)],
                [avg2(l[3], l[2]), avg3(l[3], l[2], l[1]), avg2(l[2], l[1]), avg3(l[2], l[1], l[0])],
            ];
            for r in 0..4 {
                for c in 0..4 {
                    set(r, c, v[r][c]);
                }
            }
        }
        B_HU_PRED => {
            let l3 = l[3] as u8;
            let v = [
                [avg2(l[0], l[1]), avg3(l[0], l[1], l[2]), avg2(l[1], l[2]), avg3(l[1], l[2], l[3])],
                [avg2(l[1], l[2]), avg3(l[1], l[2], l[3]), avg2(l[2], l[3]), avg3(l[2], l[3], l[3])],
                [avg2(l[2], l[3]), avg3(l[2], l[3], l[3]), l3, l3],
                [l3, l3, l3, l3],
            ];
            for r in 0..4 {
                for c in 0..4 {
                    set(r, c, v[r][c]);
                }
            }
        }
        _ => unreachable!("a subblock mode"),
    }
    o
}

/// b_pred: each subblock predicted from the pixels reconstructed so far,
/// then its residual added.
fn predict_b(p: &mut Plane, mb: &Mb, mbx: usize, mby: usize) {
    for b in 0..16 {
        let (x, y) = (mbx * 16 + (b & 3) * 4, mby * 16 + (b >> 2) * 4);
        let e = edge(p, x, y, 4);
        let ar = above_right(p, mbx, mby, b);
        let mut a = [0i32; 9];
        a[0] = e.above_left as i32;
        for k in 0..4 {
            a[1 + k] = e.above[k] as i32;
            a[5 + k] = ar[k] as i32;
        }
        let l = [e.left[0] as i32, e.left[1] as i32, e.left[2] as i32, e.left[3] as i32];
        let o = predict_4x4(mb.b_modes[b], &a, &l);
        for r in 0..4 {
            for c in 0..4 {
                p.px[(y + r) * p.w + x + c] = o[r * 4 + c];
            }
        }
        idct_add(&mb.coeffs[b * 16..b * 16 + 16], &mut p.px, y * p.w + x, p.w);
    }
}

/// vp8_dixie_predict_process_row for one intra macroblock.
fn reconstruct(yp: &mut Plane, up: &mut Plane, vp: &mut Plane, mb: &Mb, mbx: usize, mby: usize) {
    if mb.y_mode == B_PRED {
        predict_b(yp, mb, mbx, mby);
    } else {
        let (x, y) = (mbx * 16, mby * 16);
        predict_mb(yp, x, y, 16, mb.y_mode);
        // fixup_dc_coeffs: the second-order block gives each Y block's DC.
        let dcs = iwht(&mb.coeffs[24 * 16..25 * 16]);
        for b in 0..16 {
            let mut c = [0i16; 16];
            c.copy_from_slice(&mb.coeffs[b * 16..b * 16 + 16]);
            c[0] = dcs[b];
            idct_add(&c, &mut yp.px, (y + (b >> 2) * 4) * yp.w + x + (b & 3) * 4, yp.w);
        }
    }
    let (x, y) = (mbx * 8, mby * 8);
    for (k, p) in [(16, up), (20, vp)] {
        predict_mb(p, x, y, 8, mb.uv_mode);
        for b in 0..4 {
            let at = (y + (b >> 1) * 4) * p.w + x + (b & 1) * 4;
            idct_add(&mb.coeffs[(k + b) * 16..(k + b) * 16 + 16], &mut p.px, at, p.w);
        }
    }
}

// ---------------------------------------------------------------------------
// The loop filter (20.6, dixie_loopfilter.c). Pixels are addressed by an
// index into the plane and a step across the edge: p3..p0 are at
// at - 4*step..at - step, q0..q3 at at..at + 3*step.

fn s8(x: i32) -> i32 {
    x.clamp(-128, 127)
}

fn u8c(x: i32) -> u8 {
    x.clamp(0, 255) as u8
}

struct Px<'a> {
    px: &'a mut [u8],
    at: usize,
    step: usize,
}

impl Px<'_> {
    /// Pixel k across the edge: k = -4..-1 is p3..p0, k = 0..3 is q0..q3.
    fn g(&self, k: isize) -> i32 {
        self.px[(self.at as isize + k * self.step as isize) as usize] as i32
    }
    fn s(&mut self, k: isize, v: u8) {
        self.px[(self.at as isize + k * self.step as isize) as usize] = v;
    }
    fn hev(&self, t: i32) -> bool {
        (self.g(-2) - self.g(-1)).abs() > t || (self.g(1) - self.g(0)).abs() > t
    }
    fn simple_threshold(&self, limit: i32) -> bool {
        (self.g(-1) - self.g(0)).abs() * 2 + ((self.g(-2) - self.g(1)).abs() >> 1) <= limit
    }
    fn normal_threshold(&self, e: i32, i: i32) -> bool {
        self.simple_threshold(2 * e + i)
            && (self.g(-4) - self.g(-3)).abs() <= i
            && (self.g(-3) - self.g(-2)).abs() <= i
            && (self.g(-2) - self.g(-1)).abs() <= i
            && (self.g(3) - self.g(2)).abs() <= i
            && (self.g(2) - self.g(1)).abs() <= i
            && (self.g(1) - self.g(0)).abs() <= i
    }
    fn common(&mut self, outer: bool) {
        let (p1, p0, q0, q1) = (self.g(-2), self.g(-1), self.g(0), self.g(1));
        let mut a = 3 * (q0 - p0);
        if outer {
            a += s8(p1 - q1);
        }
        a = s8(a);
        let f1 = (if a + 4 > 127 { 127 } else { a + 4 }) >> 3;
        let f2 = (if a + 3 > 127 { 127 } else { a + 3 }) >> 3;
        self.s(-1, u8c(p0 + f2));
        self.s(0, u8c(q0 - f1));
        if !outer {
            let a = (f1 + 1) >> 1;
            self.s(-2, u8c(p1 + a));
            self.s(1, u8c(q1 - a));
        }
    }
    fn mb_edge(&mut self) {
        let (p2, p1, p0, q0, q1, q2) = (self.g(-3), self.g(-2), self.g(-1), self.g(0), self.g(1), self.g(2));
        let w = s8(s8(p1 - q1) + 3 * (q0 - p0));
        let a = (27 * w + 63) >> 7;
        self.s(-1, u8c(p0 + a));
        self.s(0, u8c(q0 - a));
        let a = (18 * w + 63) >> 7;
        self.s(-2, u8c(p1 + a));
        self.s(1, u8c(q1 - a));
        let a = (9 * w + 63) >> 7;
        self.s(-3, u8c(p2 + a));
        self.s(2, u8c(q2 - a));
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Mb,
    Sub,
    Simple,
}

/// Filter `n` pixels along an edge: starting at index `at`, moving `along`
/// between them, `across` across the edge.
fn edge_filter(px: &mut [u8], at: usize, along: usize, across: usize, n: usize, kind: Kind, e: i32, i: i32, hev: i32) {
    for k in 0..n {
        let mut p = Px { px: &mut *px, at: at + k * along, step: across };
        match kind {
            Kind::Simple => {
                if p.simple_threshold(e) {
                    p.common(true);
                }
            }
            Kind::Mb => {
                if p.normal_threshold(e, i) {
                    if p.hev(hev) {
                        p.common(true);
                    } else {
                        p.mb_edge();
                    }
                }
            }
            Kind::Sub => {
                if p.normal_threshold(e, i) {
                    let h = p.hev(hev);
                    p.common(h);
                }
            }
        }
    }
}

/// calculate_filter_parameters for a key frame macroblock: the edge limit
/// (the filter level), the interior limit and the high edge variance
/// threshold.
fn filter_params(hd: &Header, mb: &Mb) -> (i32, i32, i32) {
    let f = &hd.filter;
    let mut level = f.level;
    if hd.seg.enabled {
        level = if hd.seg.abs { hd.seg.lf_level[mb.segment] } else { level + hd.seg.lf_level[mb.segment] };
    }
    level = level.clamp(0, 63);
    if f.delta_enabled {
        level += f.ref_delta[0]; // the intra frame
        if mb.y_mode == B_PRED {
            level += f.mode_delta[0];
        }
    }
    level = level.clamp(0, 63);
    let mut interior = level;
    if f.sharpness != 0 {
        interior >>= if f.sharpness > 4 { 2 } else { 1 };
        if interior > 9 - f.sharpness {
            interior = 9 - f.sharpness;
        }
    }
    if interior < 1 {
        interior = 1;
    }
    let hev = (level >= 15) as i32 + (level >= 40) as i32;
    (level, interior, hev)
}

/// libwebp's filter level for a macroblock (PrecomputeFilterStrengths),
/// with its segment values absolute unless the frame's segment data says
/// otherwise (`Notes::absolute`).
fn lib_level(hd: &Header, mb: &Mb) -> i32 {
    let f = &hd.filter;
    let abs = hd.seg.abs || !hd.seg.update_data;
    let mut level = if hd.seg.enabled {
        hd.seg.lf_level[mb.segment] + if abs { 0 } else { f.level }
    } else {
        f.level
    };
    if f.delta_enabled {
        level += f.ref_delta[0];
        if mb.y_mode == B_PRED {
            level += f.mode_delta[0];
        }
    }
    level.clamp(0, 63)
}

/// Whether libwebp filters a macroblock's inner edges (VP8DecodeMB,
/// ParseResiduals): if it is B_PRED, or a Y or chroma block has a
/// coefficient past the first, or a nonzero first coefficient (for the Y
/// blocks of other modes, from the inverse WHT). A skipped macroblock has
/// none.
fn lib_inner(mb: &Mb) -> bool {
    if mb.y_mode == B_PRED {
        return true;
    }
    if mb.skip {
        return false;
    }
    let dcs = iwht(&mb.coeffs[24 * 16..25 * 16]);
    (0..16).any(|b| mb.ends[b] > 1 || dcs[b] != 0) || (16..24).any(|b| mb.ends[b] > 1 || mb.coeffs[b * 16] != 0)
}

/// vp8_dixie_loopfilter_process_row over the frame, in macroblock order.
fn loop_filter(hd: &Header, mbs: &[Mb], mbw: usize, mbh: usize, yp: &mut Plane, up: &mut Plane, vp: &mut Plane) {
    if hd.filter.level == 0 {
        return;
    }
    for mby in 0..mbh {
        for mbx in 0..mbw {
            let mb = &mbs[mby * mbw + mbx];
            let (e, i, hev) = filter_params(hd, mb);
            let inner = mb.nonzero || mb.y_mode == B_PRED;
            if lib_level(hd, mb) != e {
                note(|n| n.level = true);
            }
            if e > 0 && lib_inner(mb) != inner {
                note(|n| n.inner = true);
            }
            if e == 0 {
                continue;
            }
            let (yw, cw) = (yp.w, up.w);
            let y0 = mby * 16 * yw + mbx * 16;
            let c0 = mby * 8 * cw + mbx * 8;
            if hd.filter.simple {
                let (mbl, bl) = ((e + 2) * 2 + i, e * 2 + i);
                if mbx > 0 {
                    edge_filter(&mut yp.px, y0, yw, 1, 16, Kind::Simple, mbl, 0, 0);
                }
                if inner {
                    for k in [4, 8, 12] {
                        edge_filter(&mut yp.px, y0 + k, yw, 1, 16, Kind::Simple, bl, 0, 0);
                    }
                }
                if mby > 0 {
                    edge_filter(&mut yp.px, y0, 1, yw, 16, Kind::Simple, mbl, 0, 0);
                }
                if inner {
                    for k in [4, 8, 12] {
                        edge_filter(&mut yp.px, y0 + k * yw, 1, yw, 16, Kind::Simple, bl, 0, 0);
                    }
                }
                continue;
            }
            if mbx > 0 {
                edge_filter(&mut yp.px, y0, yw, 1, 16, Kind::Mb, e + 2, i, hev);
                edge_filter(&mut up.px, c0, cw, 1, 8, Kind::Mb, e + 2, i, hev);
                edge_filter(&mut vp.px, c0, cw, 1, 8, Kind::Mb, e + 2, i, hev);
            }
            if inner {
                for k in [4, 8, 12] {
                    edge_filter(&mut yp.px, y0 + k, yw, 1, 16, Kind::Sub, e, i, hev);
                }
                edge_filter(&mut up.px, c0 + 4, cw, 1, 8, Kind::Sub, e, i, hev);
                edge_filter(&mut vp.px, c0 + 4, cw, 1, 8, Kind::Sub, e, i, hev);
            }
            if mby > 0 {
                edge_filter(&mut yp.px, y0, 1, yw, 16, Kind::Mb, e + 2, i, hev);
                edge_filter(&mut up.px, c0, 1, cw, 8, Kind::Mb, e + 2, i, hev);
                edge_filter(&mut vp.px, c0, 1, cw, 8, Kind::Mb, e + 2, i, hev);
            }
            if inner {
                for k in [4, 8, 12] {
                    edge_filter(&mut yp.px, y0 + k * yw, 1, yw, 16, Kind::Sub, e, i, hev);
                }
                edge_filter(&mut up.px, c0 + 4 * cw, 1, cw, 8, Kind::Sub, e, i, hev);
                edge_filter(&mut vp.px, c0 + 4 * cw, 1, cw, 8, Kind::Sub, e, i, hev);
            }
        }
    }
}

// ---------------------------------------------------------------------------

fn crop(p: &Plane, w: usize, h: usize) -> Vec<u8> {
    let mut o = Vec::with_capacity(w * h);
    for y in 0..h {
        o.extend_from_slice(&p.px[y * p.w..y * p.w + w]);
    }
    o
}

/// Decode a VP8 key frame, as RFC 6386's reference decoder does; None where
/// it reports an error. With the header's parse, the modes and the tokens.
pub fn vp8_full(b: &[u8]) -> Option<(Frame, Header, Vec<Mb>)> {
    let (hd, mut bd, parts) = header(b)?;
    if !hd.show {
        note(|n| n.hidden = true);
    }
    let (mbw, mbh) = (hd.w.div_ceil(16), hd.h.div_ceil(16));
    let mut mbs = modes(&hd, &mut bd, mbw, mbh);
    if bd.lib_eof {
        note(|n| n.eof = true);
    }
    if bd.n == 1 && bd.reads > 0 {
        note(|n| n.one_byte = true);
    }
    if bd.ff_start {
        note(|n| n.ff_start = true);
    }
    let mut tbd: Vec<Bool> = parts.iter().map(|p| Bool::new(p)).collect();
    tokens(&hd, &mut tbd, &mut mbs, mbw, mbh);
    // The token partitions some row reads.
    for p in tbd.iter().take(mbh) {
        if p.lib_eof {
            note(|n| n.eof = true);
        }
        if p.n == 1 && p.reads > 0 {
            note(|n| n.one_byte = true);
        }
        if p.ff_start {
            note(|n| n.ff_start = true);
        }
    }
    let mut yp = Plane { w: mbw * 16, px: vec![0; mbw * mbh * 256] };
    let mut up = Plane { w: mbw * 8, px: vec![0; mbw * mbh * 64] };
    let mut vp = Plane { w: mbw * 8, px: vec![0; mbw * mbh * 64] };
    for mby in 0..mbh {
        for mbx in 0..mbw {
            reconstruct(&mut yp, &mut up, &mut vp, &mbs[mby * mbw + mbx], mbx, mby);
        }
    }
    loop_filter(&hd, &mbs, mbw, mbh, &mut yp, &mut up, &mut vp);
    let (cw, ch) = (hd.w.div_ceil(2), hd.h.div_ceil(2));
    let f = Frame { w: hd.w, h: hd.h, y: crop(&yp, hd.w, hd.h), u: crop(&up, cw, ch), v: crop(&vp, cw, ch) };
    Some((f, hd, mbs))
}

pub fn vp8(b: &[u8]) -> Option<Frame> {
    vp8_full(b).map(|(f, _, _)| f)
}

/// `vp8`, and the `lib` flag with the notes it is made of.
pub fn vp8_lib(b: &[u8]) -> Option<(Frame, bool, Notes)> {
    NOTES.with(|n| *n.borrow_mut() = Notes::default());
    let f = vp8(b)?;
    let notes = NOTES.with(|n| n.borrow().clone());
    Some((f, notes.lib(), notes))
}
