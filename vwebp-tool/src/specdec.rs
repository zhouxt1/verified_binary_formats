//! The WebP lossless bitstream (RFC 9649 section 3) as an executable
//! specification: a decoding function written the way the Verus spec is
//! (every step a function of the bits and a position, no shared state), run
//! against libwebp before any proof was written. `vwebp/src/spec.rs` is its
//! Verus form, function by function (`read_group` there is `read_codes`,
//! one pixel step is `pix_step`, and each inverse transform is its own
//! function).
//!
//! Where the RFC does not say what a decoder does, this follows libwebp
//! 1.6.0 (`src/dec/vp8l_dec.c`, `src/utils/huffman_utils.c`,
//! `src/dsp/lossless.c`), and each such place is marked `LIBWEBP:`. Where
//! libwebp accepts a stream the RFC's text rules out, the result's `strict`
//! flag is false (`RFC:` marks those).
//!
//! Integers are u64; bit positions are u64 offsets into the LSB-first bits
//! of the input (RFC 9649 3.2).

use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

/// Coverage counters, printed by `vwebp-tool` when VW_COVER is set.
pub const COVER: [&str; 30] = [
    "simple code 1 symbol", "simple code 2 symbols", "simple code first 8 bits",
    "simple code symbol dropped", "simple code duplicate", "normal code",
    "max_symbol given", "repeat 16", "repeat 16 before a nonzero", "repeat 17", "repeat 18",
    "single-symbol normal code", "single-symbol code len != 1", "cl code single symbol",
    "color cache", "color cache hit", "meta prefix codes", "unused prefix group",
    "backward ref", "distance code <= 120", "distance clamped to 1", "overlapping copy",
    "predictor transform", "color transform", "subtract green", "color indexing",
    "pixel bundling", "palette index past size", "predictor mode 14/15", "predictor green >= 16",
];
pub static HITS: [AtomicU64; 30] = [const { AtomicU64::new(0) }; 30];
fn hit(i: usize) {
    HITS[i].fetch_add(1, Relaxed);
}

/// With VW_TRACE set, the codes read and where decoding stops, on stderr.
fn trace() -> bool {
    static T: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *T.get_or_init(|| std::env::var_os("VW_TRACE").is_some())
}

pub struct Bits<'a> {
    pub buf: &'a [u8],
}

impl<'a> Bits<'a> {
    pub fn len(&self) -> u64 {
        8 * self.buf.len() as u64
    }
    fn bit(&self, p: u64) -> u64 {
        ((self.buf[(p / 8) as usize] >> (p % 8)) & 1) as u64
    }
    /// `ReadBits(n)` at `p`: the first bit the least significant (3.2).
    pub fn getbits(&self, p: u64, n: u64) -> Option<u64> {
        if p + n > self.len() {
            return None;
        }
        let mut v = 0u64;
        for j in 0..n {
            v |= self.bit(p + j) << j;
        }
        Some(v)
    }
    /// `l` bits at `p`, the first the most significant: how a prefix code
    /// is read (as in DEFLATE; libwebp's tables are indexed by reversed codes).
    fn codebits(&self, p: u64, l: u64) -> u64 {
        let mut v = 0u64;
        for j in 0..l {
            v = 2 * v + self.bit(p + j);
        }
        v
    }
}

// ------------------------------------------------------------ prefix codes

pub const MAXBITS: u64 = 15;

/// A canonical prefix code (3.7.1), from its lengths. `count`, `first`
/// and `sorted` are `bl_count`, `next_code` and the symbols by (length,
/// symbol), computed once (the one liberty taken with the spec, which
/// recomputes them per symbol).
#[derive(Clone)]
pub struct Code {
    pub lens: Vec<u8>,
    count: [u64; 16],
    first: [u64; 16],
    start: [usize; 16],
    sorted: Vec<u16>,
    single: Option<u64>,
}

impl Code {
    pub fn new(lens: Vec<u8>) -> Code {
        let mut count = [0u64; 16];
        let mut first = [0u64; 16];
        let mut start = [0usize; 16];
        for l in 1..16 {
            count[l] = bl_count(&lens, l as u64);
            first[l] = next_code(&lens, l as u64);
        }
        let mut sorted = Vec::new();
        for l in 1..16 {
            start[l] = sorted.len();
            for (s, &x) in lens.iter().enumerate() {
                if x as usize == l {
                    sorted.push(s as u16);
                }
            }
        }
        let single = single(&lens);
        Code { lens, count, first, start, sorted, single }
    }
}

fn bl_count(lens: &[u8], l: u64) -> u64 {
    lens.iter().filter(|&&x| x as u64 == l).count() as u64
}

fn next_code(lens: &[u8], l: u64) -> u64 {
    // DEFLATE's (RFC 1951 3.2.2): codes of length l start where length l-1's end, doubled.
    let mut code = 0u64;
    for k in 1..l {
        code = (code + bl_count(lens, k)) << 1;
    }
    code
}

fn nnz(lens: &[u8]) -> u64 {
    lens.iter().filter(|&&x| x != 0).count() as u64
}

/// The lengths are a code a decoder accepts: `Some(strict)`, or `None`.
///
/// RFC 3.7.2.1: "The described tree must be a complete binary tree. A
/// single leaf node is considered a complete binary tree ... marked with
/// the length of 1". LIBWEBP (BuildHuffmanTable): all zeros is refused; a
/// single symbol of any length is accepted, and decodes with no bits; two
/// or more symbols must be complete (Kraft sum exactly 1).
pub fn code_ok(lens: &[u8]) -> Option<bool> {
    let n = nnz(lens);
    if n == 0 {
        return None;
    }
    if n == 1 {
        let l = *lens.iter().find(|&&x| x != 0).unwrap();
        if l != 1 {
            hit(12);
        }
        return Some(l == 1); // RFC: a single leaf has length 1
    }
    let kraft: u64 = lens.iter().filter(|&&x| x != 0).map(|&x| 1u64 << (MAXBITS - x as u64)).sum();
    if kraft == 1 << MAXBITS { Some(true) } else { None }
}

/// The one symbol of a single-symbol code.
fn single(lens: &[u8]) -> Option<u64> {
    if nnz(lens) == 1 { lens.iter().position(|&x| x != 0).map(|s| s as u64) } else { None }
}

/// Read one symbol at `p` (3.7.2.3): a single-symbol code reads no bits;
/// otherwise the shortest length whose code the next bits are.
pub fn decode_sym(c: &Code, b: &Bits, p: u64) -> Option<(u64, u64)> {
    if let Some(s) = c.single {
        return Some((s, p));
    }
    for l in 1..=MAXBITS {
        if p + l > b.len() {
            return None;
        }
        let v = b.codebits(p, l);
        let (first, cnt) = (c.first[l as usize], c.count[l as usize]);
        if v >= first && v < first + cnt {
            // the (v - first)th symbol of length l
            let s = c.sorted[c.start[l as usize] + (v - first) as usize];
            return Some((s as u64, p + l));
        }
    }
    None
}

pub const CL_ORDER: [usize; 19] = [17, 18, 0, 1, 2, 3, 4, 5, 16, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];

/// The code lengths of a normal code (3.7.2.1.2), after the code length
/// code: at most `max_symbol` tokens, a repeat counting as one (LIBWEBP:
/// ReadHuffmanCodeLengths; the RFC says "used to read up to max_symbol code
/// lengths"), until `asize` lengths are set; the rest are 0.
fn read_lens(cl: &Code, b: &Bits, mut p: u64, asize: u64, mut max_symbol: u64) -> Option<(Vec<u8>, u64)> {
    let mut lens = vec![0u8; asize as usize];
    let mut sym = 0u64;
    let mut prev = 8u8;
    let mut seen_nz = false;
    while sym < asize {
        if max_symbol == 0 {
            break;
        }
        max_symbol -= 1;
        let (c, q) = decode_sym(cl, b, p)?;
        p = q;
        if c < 16 {
            lens[sym as usize] = c as u8;
            sym += 1;
            if c != 0 {
                prev = c as u8;
                seen_nz = true;
            }
        } else {
            let (eb, off) = [(2, 3), (3, 3), (7, 11)][(c - 16) as usize];
            let rep = b.getbits(p, eb)? + off;
            p += eb;
            if sym + rep > asize {
                return None; // LIBWEBP: a repeat past the alphabet
            }
            let v = if c == 16 {
                hit(7);
                if !seen_nz {
                    hit(8);
                }
                prev
            } else {
                hit(if c == 17 { 9 } else { 10 });
                0
            };
            for _ in 0..rep {
                lens[sym as usize] = v;
                sym += 1;
            }
        }
    }
    Some((lens, p))
}

/// One prefix code of an alphabet of `asize` symbols (3.7.2.1).
pub fn read_code(b: &Bits, p: u64, asize: u64) -> Option<(Code, u64, bool)> {
    let r = read_code_(b, p, asize);
    if trace() {
        match &r {
            Some((c, q, _)) => eprintln!("code@{} asize {} -> {:?} @{}", p, asize,
                c.lens.iter().enumerate().filter(|(_, &l)| l != 0).map(|(s, &l)| (s, l)).collect::<Vec<_>>(), q),
            None => eprintln!("code@{} asize {} -> FAIL", p, asize),
        }
    }
    r
}

fn read_code_(b: &Bits, mut p: u64, asize: u64) -> Option<(Code, u64, bool)> {
    let mut strict = true;
    let simple = b.getbits(p, 1)?;
    p += 1;
    let lens = if simple == 1 {
        let nsym = b.getbits(p, 1)? + 1;
        let first8 = b.getbits(p + 1, 1)?;
        p += 2;
        let nb = if first8 == 1 { 8 } else { 1 };
        let s0 = b.getbits(p, nb)?;
        p += nb;
        hit(if nsym == 1 { 0 } else { 1 });
        if first8 == 1 {
            hit(2);
        }
        let mut lens = vec![0u8; asize as usize];
        let mut syms = vec![s0];
        if nsym == 2 {
            let s1 = b.getbits(p, 8)?;
            p += 8;
            if s1 == s0 {
                hit(4);
            }
            syms.push(s1);
        }
        for s in syms {
            if s < asize {
                lens[s as usize] = 1;
            } else {
                // LIBWEBP: a symbol outside the alphabet is dropped. RFC:
                // code_lengths[symbol] = 1 has no such entry.
                hit(3);
                strict = false;
            }
        }
        lens
    } else {
        hit(5);
        let n = b.getbits(p, 4)? + 4;
        p += 4;
        let mut cll = vec![0u8; 19];
        for i in 0..n {
            cll[CL_ORDER[i as usize]] = b.getbits(p, 3)? as u8;
            p += 3;
        }
        // the code length code is a prefix code like any other
        strict &= code_ok(&cll)?;
        if nnz(&cll) == 1 {
            hit(13);
        }
        let cl = Code::new(cll);
        let use_len = b.getbits(p, 1)?;
        p += 1;
        let max_symbol = if use_len == 1 {
            hit(6);
            let nb = 2 + 2 * b.getbits(p, 3)?;
            p += 3;
            let m = 2 + b.getbits(p, nb)?;
            p += nb;
            if m > asize {
                return None; // RFC: "the bitstream is invalid"
            }
            m
        } else {
            asize
        };
        let (lens, q) = read_lens(&cl, b, p, asize, max_symbol)?;
        p = q;
        if nnz(&lens) == 1 {
            hit(11);
        }
        lens
    };
    strict &= code_ok(&lens)?;
    Some((Code::new(lens), p, strict))
}

/// A prefix code group (3.7.2): green (with lengths and cache indexes),
/// red, blue, alpha, distance.
pub fn read_group(b: &Bits, mut p: u64, cache_bits: u64) -> Option<(Vec<Code>, u64, bool)> {
    let cache = if cache_bits > 0 { 1u64 << cache_bits } else { 0 };
    let sizes = [256 + 24 + cache, 256, 256, 256, 40];
    let mut g = Vec::new();
    let mut strict = true;
    for s in sizes {
        let (c, q, st) = read_code(b, p, s)?;
        g.push(c);
        p = q;
        strict &= st;
    }
    Some((g, p, strict))
}

// -------------------------------------------------------------- image data

/// LZ77 prefix coding (3.6.2.2): a value from its prefix symbol and extra bits.
fn prefix_value(b: &Bits, p: u64, s: u64) -> Option<(u64, u64)> {
    if s < 4 {
        return Some((s + 1, p));
    }
    let eb = (s - 2) >> 1;
    let off = (2 + (s & 1)) << eb;
    Some((off + b.getbits(p, eb)? + 1, p + eb))
}

/// Figure 20: distance codes 1..120 as (xi, yi).
pub const DIST_MAP: [(i64, i64); 120] = [
    (0, 1), (1, 0), (1, 1), (-1, 1), (0, 2), (2, 0), (1, 2), (-1, 2), (2, 1), (-2, 1), (2, 2), (-2, 2),
    (0, 3), (3, 0), (1, 3), (-1, 3), (3, 1), (-3, 1), (2, 3), (-2, 3), (3, 2), (-3, 2), (0, 4), (4, 0),
    (1, 4), (-1, 4), (4, 1), (-4, 1), (3, 3), (-3, 3), (2, 4), (-2, 4), (4, 2), (-4, 2), (0, 5), (3, 4),
    (-3, 4), (4, 3), (-4, 3), (5, 0), (1, 5), (-1, 5), (5, 1), (-5, 1), (2, 5), (-2, 5), (5, 2), (-5, 2),
    (4, 4), (-4, 4), (3, 5), (-3, 5), (5, 3), (-5, 3), (0, 6), (6, 0), (1, 6), (-1, 6), (6, 1), (-6, 1),
    (2, 6), (-2, 6), (6, 2), (-6, 2), (4, 5), (-4, 5), (5, 4), (-5, 4), (3, 6), (-3, 6), (6, 3), (-6, 3),
    (0, 7), (7, 0), (1, 7), (-1, 7), (5, 5), (-5, 5), (7, 1), (-7, 1), (4, 6), (-4, 6), (6, 4), (-6, 4),
    (2, 7), (-2, 7), (7, 2), (-7, 2), (3, 7), (-3, 7), (7, 3), (-7, 3), (5, 6), (-5, 6), (6, 5), (-6, 5),
    (8, 0), (4, 7), (-4, 7), (7, 4), (-7, 4), (8, 1), (8, 2), (6, 6), (-6, 6), (8, 3), (5, 7), (-5, 7),
    (7, 5), (-7, 5), (8, 4), (6, 7), (-6, 7), (7, 6), (-7, 6), (8, 5), (7, 7), (-7, 7), (8, 6), (8, 7),
];

/// 3.6.2.2.1: a distance code as a distance in scan-line order.
pub fn plane_dist(dcode: u64, w: u64) -> u64 {
    if dcode > 120 {
        return dcode - 120;
    }
    hit(19);
    let (xi, yi) = DIST_MAP[(dcode - 1) as usize];
    let d = xi + yi * w as i64;
    if d < 1 {
        hit(20);
        1
    } else {
        d as u64
    }
}

/// The color cache's slot for a color (3.6.2.3). LIBWEBP: the product is
/// taken mod 2^32 (VP8LHashPix), which the RFC's C expression leaves open.
pub fn cache_key(c: u32, bits: u64) -> usize {
    (c.wrapping_mul(0x1e35a7bd) >> (32 - bits)) as usize
}

/// Where the prefix code groups come from: one group, or an entropy image
/// of `bits`-sized tiles, `ew` tiles wide (3.7.2.2).
pub enum Meta {
    One,
    Tiles { bits: u64, ew: u64, img: Vec<u32> },
}

fn group_at(m: &Meta, x: u64, y: u64) -> usize {
    match m {
        Meta::One => 0,
        Meta::Tiles { bits, ew, img } => ((img[((y >> bits) * ew + (x >> bits)) as usize] >> 8) & 0xffff) as usize,
    }
}

/// The entropy-coded pixels of a `w` x `h` image (3.6.2, 3.7.2.3).
pub fn decode_pixels(
    b: &Bits, mut p: u64, w: u64, h: u64, cache_bits: u64, groups: &[Vec<Code>], meta: &Meta,
) -> Option<(Vec<u32>, u64)> {
    let total = w * h;
    let mut px: Vec<u32> = Vec::new();
    let mut cache = vec![0u32; if cache_bits > 0 { 1 << cache_bits } else { 0 }];
    let put = |px: &mut Vec<u32>, cache: &mut Vec<u32>, c: u32| {
        px.push(c);
        if cache_bits > 0 {
            cache[cache_key(c, cache_bits)] = c;
        }
    };
    while (px.len() as u64) < total {
        let i = px.len() as u64;
        if trace() && p + 15 > b.len() {
            eprintln!("pixel {} of {} ({}x{}) @{} of {} bits", i, total, w, h, p, b.len());
        }
        let g = &groups[group_at(meta, i % w, i / w)];
        let (s, q) = decode_sym(&g[0], b, p)?;
        p = q;
        if s < 256 {
            let (r, q) = decode_sym(&g[1], b, p)?;
            let (bl, q) = decode_sym(&g[2], b, q)?;
            let (a, q) = decode_sym(&g[3], b, q)?;
            p = q;
            put(&mut px, &mut cache, ((a as u32) << 24) | ((r as u32) << 16) | ((s as u32) << 8) | bl as u32);
        } else if s < 256 + 24 {
            hit(18);
            let (len, q) = prefix_value(b, p, s - 256)?;
            let (ds, q) = decode_sym(&g[4], b, q)?;
            let (dcode, q) = prefix_value(b, q, ds)?;
            p = q;
            let d = plane_dist(dcode, w);
            // LIBWEBP (DecodeImageData): a copy from before the first pixel
            // or past the last is an error; the RFC does not say.
            if d > i || len > total - i {
                if trace() {
                    eprintln!("copy at pixel {} of {} ({}x{}): len {} dist {} (code {}) @{}", i, total, w, h, len, d, dcode, p);
                }
                return None;
            }
            if d < len {
                hit(21);
            }
            for _ in 0..len {
                let c = px[px.len() - d as usize];
                put(&mut px, &mut cache, c);
            }
        } else {
            hit(15);
            let c = cache[(s - 256 - 24) as usize];
            put(&mut px, &mut cache, c);
        }
    }
    Some((px, p))
}

/// color-cache-info (3.8.3): 0, or 1 and 4 bits in 1..=11.
fn read_cache_bits(b: &Bits, p: u64) -> Option<(u64, u64)> {
    if b.getbits(p, 1)? == 0 {
        return Some((0, p + 1));
    }
    let cb = b.getbits(p + 1, 4)?;
    if !(1..=11).contains(&cb) {
        return None; // RFC 3.6.2.3: MUST indicate a corrupted bitstream
    }
    hit(14);
    Some((cb, p + 5))
}

/// An entropy-coded image (3.8.3): the sub-resolution images and the color
/// table. Its own color cache; one prefix code group.
pub fn entropy_coded_image(b: &Bits, p: u64, w: u64, h: u64) -> Option<(Vec<u32>, u64, bool)> {
    let (cb, p) = read_cache_bits(b, p)?;
    let (g, p, strict) = read_group(b, p, cb)?;
    let (px, p) = decode_pixels(b, p, w, h, cb, &[g], &Meta::One)?;
    Some((px, p, strict))
}

/// The spatially-coded image (3.8.3): the ARGB image, with meta prefix codes.
pub fn spatially_coded_image(b: &Bits, p: u64, w: u64, h: u64) -> Option<(Vec<u32>, u64, bool)> {
    let (cb, mut p) = read_cache_bits(b, p)?;
    let mut strict = true;
    let meta = if b.getbits(p, 1)? == 1 {
        hit(16);
        let bits = b.getbits(p + 1, 3)? + 2;
        let ew = w.div_ceil(1 << bits);
        let eh = h.div_ceil(1 << bits);
        let (img, q, st) = entropy_coded_image(b, p + 4, ew, eh)?;
        p = q;
        strict &= st;
        Meta::Tiles { bits, ew, img }
    } else {
        p += 1;
        Meta::One
    };
    // 3.7.2.2.2: as many groups as the largest meta prefix code + 1; every
    // one is read, and must be valid, whether a tile uses it or not
    // (LIBWEBP reads unused ones with no table, and checks them the same).
    let ngroups = match &meta {
        Meta::One => 1,
        Meta::Tiles { img, .. } => img.iter().map(|&v| ((v >> 8) & 0xffff) as usize).max().unwrap() + 1,
    };
    if let Meta::Tiles { img, .. } = &meta {
        let mut used = vec![false; ngroups];
        for &v in img {
            used[((v >> 8) & 0xffff) as usize] = true;
        }
        if used.iter().any(|&u| !u) {
            hit(17);
        }
    }
    let mut groups = Vec::new();
    for _ in 0..ngroups {
        let (g, q, st) = read_group(b, p, cb)?;
        groups.push(g);
        p = q;
        strict &= st;
    }
    let (px, p) = decode_pixels(b, p, w, h, cb, &groups, &meta)?;
    Some((px, p, strict))
}

// -------------------------------------------------------------- transforms

pub enum Transform {
    /// size bits, the image's width then, the predictor image
    Predictor(u64, u64, Vec<u32>),
    /// size bits, the image's width then, the color transform image
    Color(u64, u64, Vec<u32>),
    SubtractGreen,
    /// width bits, the image's width before bundling, the color table
    /// (with deltas undone, padded with 0 to 2^(8 >> width bits) entries),
    /// and its size
    ColorIndexing(u64, u64, Vec<u32>, u64),
}

/// Per-channel sum mod 256.
pub fn add_pixels(a: u32, b: u32) -> u32 {
    let mut r = 0u32;
    for k in 0..4 {
        let s = (((a >> (8 * k)) & 0xff) + ((b >> (8 * k)) & 0xff)) & 0xff;
        r |= s << (8 * k);
    }
    r
}

fn ch(c: u32, k: u32) -> i64 {
    ((c >> (8 * k)) & 0xff) as i64
}

fn per_channel(f: impl Fn(u32) -> i64) -> u32 {
    let mut r = 0u32;
    for k in 0..4 {
        r |= ((f(k) as u32) & 0xff) << (8 * k);
    }
    r
}

fn average2(a: u32, b: u32) -> u32 {
    per_channel(|k| (ch(a, k) + ch(b, k)) / 2)
}

fn select(l: u32, t: u32, tl: u32) -> u32 {
    let mut pl = 0;
    let mut pt = 0;
    for k in 0..4 {
        let pred = ch(l, k) + ch(t, k) - ch(tl, k);
        pl += (pred - ch(l, k)).abs();
        pt += (pred - ch(t, k)).abs();
    }
    if pl < pt { l } else { t }
}

fn clamp(a: i64) -> i64 {
    a.clamp(0, 255)
}

/// C's `/`: truncates toward zero (i64 `/` in Rust does too; the Verus spec
/// must not use int's `/`, which floors).
fn clamp_add_subtract_half(a: u32, b: u32) -> u32 {
    per_channel(|k| clamp(ch(a, k) + (ch(a, k) - ch(b, k)) / 2))
}

/// Table 2. LIBWEBP: the mode is the green value's low 4 bits
/// (`(green >> 8) & 0xf` of the pixel), and modes 14 and 15 are mode 0
/// (VP8LPredictorsAdd[14..16], "padding security sentinels"); the RFC has
/// only the 14 modes.
pub fn predict(mode: u64, l: u32, t: u32, tr: u32, tl: u32) -> u32 {
    match mode {
        1 => l,
        2 => t,
        3 => tr,
        4 => tl,
        5 => average2(average2(l, tr), t),
        6 => average2(l, tl),
        7 => average2(l, t),
        8 => average2(tl, t),
        9 => average2(t, tr),
        10 => average2(average2(l, tl), average2(t, tr)),
        11 => select(l, t, tl),
        12 => per_channel(|k| clamp(ch(l, k) + ch(t, k) - ch(tl, k))),
        13 => clamp_add_subtract_half(average2(l, t), tl),
        _ => 0xff000000,
    }
}

fn inv_predictor(bits: u64, w: u64, img: &[u32], px: &[u32]) -> Vec<u32> {
    let h = px.len() as u64 / w;
    let tw = w.div_ceil(1 << bits);
    let mut out = vec![0u32; px.len()];
    for y in 0..h {
        for x in 0..w {
            let i = (y * w + x) as usize;
            let pred = if y == 0 && x == 0 {
                0xff000000
            } else if y == 0 {
                out[i - 1]
            } else if x == 0 {
                out[i - w as usize]
            } else {
                let g = (img[((y >> bits) * tw + (x >> bits)) as usize] >> 8) & 0xff;
                if g >= 16 {
                    hit(29);
                }
                let mode = (g & 0xf) as u64;
                if mode >= 14 {
                    hit(28);
                }
                let up = i - w as usize;
                // the rightmost column's TR is the current row's first pixel,
                // which in scan-line order is the pixel after T (3.5.1)
                predict(mode, out[i - 1], out[up], out[up + 1], out[up - 1])
            };
            out[i] = add_pixels(px[i], pred);
        }
    }
    out
}

fn delta(t: u32, c: u32) -> i64 {
    ((t as u8 as i8 as i64) * (c as u8 as i8 as i64)) >> 5
}

fn inv_color(bits: u64, w: u64, img: &[u32], px: &[u32]) -> Vec<u32> {
    let tw = w.div_ceil(1 << bits);
    px.iter()
        .enumerate()
        .map(|(i, &c)| {
            let (x, y) = (i as u64 % w, i as u64 / w);
            let e = img[((y >> bits) * tw + (x >> bits)) as usize];
            // 3.5.2: blue is green_to_red, green is green_to_blue, red is red_to_blue
            let (g2r, g2b, r2b) = (e & 0xff, (e >> 8) & 0xff, (e >> 16) & 0xff);
            let (g, r, bl) = ((c >> 8) & 0xff, (c >> 16) & 0xff, c & 0xff);
            let nr = ((r as i64 + delta(g2r, g)) & 0xff) as u32;
            let nb = ((bl as i64 + delta(g2b, g) + delta(r2b, nr)) & 0xff) as u32;
            (c & 0xff00ff00) | (nr << 16) | nb
        })
        .collect()
}

fn inv_subtract_green(px: &[u32]) -> Vec<u32> {
    px.iter()
        .map(|&c| {
            let g = (c >> 8) & 0xff;
            let r = (((c >> 16) & 0xff) + g) & 0xff;
            let b = ((c & 0xff) + g) & 0xff;
            (c & 0xff00ff00) | (r << 16) | b
        })
        .collect()
}

fn inv_color_indexing(wb: u64, w: u64, pal: &[u32], n: u64, px: &[u32], h: u64) -> Vec<u32> {
    let iw = w.div_ceil(1 << wb);
    let mut out = Vec::with_capacity((w * h) as usize);
    for y in 0..h {
        for x in 0..w {
            let g = ((px[(y * iw + (x >> wb)) as usize] >> 8) & 0xff) as u64;
            let idx = if wb == 0 {
                g
            } else {
                let nb = 8 >> wb;
                (g >> ((x & ((1 << wb) - 1)) * nb)) & ((1 << nb) - 1)
            };
            if idx >= n {
                hit(27);
            }
            out.push(pal[idx as usize]);
        }
    }
    out
}

/// The transforms (3.5, 3.8.2): each type at most once (LIBWEBP refuses a
/// repeat; RFC "allowed to be used only once"). Returns them in bitstream
/// order and the width the image data has after them.
pub fn read_transforms(b: &Bits, mut p: u64, mut w: u64, h: u64) -> Option<(Vec<Transform>, u64, u64, bool)> {
    let mut ts = Vec::new();
    let mut seen = [false; 4];
    let mut strict = true;
    while b.getbits(p, 1)? == 1 {
        let ty = b.getbits(p + 1, 2)?;
        p += 3;
        if seen[ty as usize] {
            return None;
        }
        seen[ty as usize] = true;
        match ty {
            0 | 1 => {
                let bits = b.getbits(p, 3)? + 2;
                let (img, q, st) = entropy_coded_image(b, p + 3, w.div_ceil(1 << bits), h.div_ceil(1 << bits))?;
                p = q;
                strict &= st;
                if ty == 0 {
                    hit(22);
                    ts.push(Transform::Predictor(bits, w, img));
                } else {
                    hit(23);
                    ts.push(Transform::Color(bits, w, img));
                }
            }
            2 => {
                hit(24);
                ts.push(Transform::SubtractGreen);
            }
            _ => {
                hit(25);
                let n = b.getbits(p, 8)? + 1;
                let wb = if n > 16 { 0 } else if n > 4 { 1 } else if n > 2 { 2 } else { 3 };
                if wb > 0 {
                    hit(26);
                }
                let (deltas, q, st) = entropy_coded_image(b, p + 8, n, 1)?;
                p = q;
                strict &= st;
                // 3.5.4: the table is subtraction-coded; entries past it are
                // transparent black ("should be set to 0x00000000")
                let mut pal = vec![0u32; 1 << (8 >> wb)];
                let mut prev = 0u32;
                for (k, &d) in deltas.iter().enumerate() {
                    prev = add_pixels(prev, d);
                    pal[k] = prev;
                }
                ts.push(Transform::ColorIndexing(wb, w, pal, n));
                w = w.div_ceil(1 << wb);
            }
        }
    }
    Some((ts, w, p + 1, strict))
}

pub struct Image {
    pub w: u64,
    pub h: u64,
    pub alpha_hint: bool,
    pub px: Vec<u32>,
}

/// A VP8L bitstream (3.4 on): the signature byte 0x2f, the header, the
/// transforms, the image data, the inverse transforms last one first.
/// Returns the image, the bits read, and the strict flag.
pub fn vp8l(buf: &[u8]) -> Option<(Image, u64, bool)> {
    let b = Bits { buf };
    if b.getbits(0, 8)? != 0x2f {
        return None;
    }
    let w = b.getbits(8, 14)? + 1;
    let h = b.getbits(22, 14)? + 1;
    let alpha = b.getbits(36, 1)?;
    if b.getbits(37, 3)? != 0 {
        return None; // version_number MUST be 0
    }
    let (px, p, st) = image_stream(&b, 40, w, h)?;
    Some((Image { w, h, alpha_hint: alpha == 1, px }, p, st))
}

/// The image-stream of a `w` x `h` image from bit `p` on (3.6 on): the
/// transforms, the image data, the inverse transforms last one first. A
/// VP8L bitstream has one after its header; an ALPH chunk's lossless
/// alpha is one on its own, of the image's size (RFC 9649 2.7.1.2).
/// Returns the pixels, the bit after the stream, and the strict flag.
pub fn image_stream(b: &Bits, p: u64, w: u64, h: u64) -> Option<(Vec<u32>, u64, bool)> {
    let (ts, dw, p, st1) = read_transforms(b, p, w, h)?;
    let (mut px, p, st2) = spatially_coded_image(b, p, dw, h)?;
    for t in ts.iter().rev() {
        px = match t {
            Transform::Predictor(bits, tw, img) => inv_predictor(*bits, *tw, img, &px),
            Transform::Color(bits, tw, img) => inv_color(*bits, *tw, img, &px),
            Transform::SubtractGreen => inv_subtract_green(&px),
            Transform::ColorIndexing(wb, tw, pal, n) => inv_color_indexing(*wb, *tw, pal, *n, &px, h),
        };
    }
    Some((px, p, st1 && st2))
}
