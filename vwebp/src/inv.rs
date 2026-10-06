//! The inverse transforms (RFC 9649 3.5) and the pixel arithmetic they use,
//! each proved to compute its spec function.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
#[cfg(verus_keep_ghost)] // proof-only: erased from a plain build
use crate::code::lemma_shl1;
use crate::pix::pixel_x;
use crate::spec::*;

verus! {

// ------------------------------------------------------ channel arithmetic

#[inline(always)]
pub fn alpha_x(c: u32) -> (r: i64) ensures r == alpha(c), 0 <= r < 256,
{
    proof { assert(c >> 24u32 < 256) by (bit_vector); }
    (c >> 24u32) as i64
}
#[inline(always)]
pub fn red_x(c: u32) -> (r: i64) ensures r == red(c), 0 <= r < 256,
{
    proof { assert((c >> 16u32) & 0xffu32 < 256) by (bit_vector); }
    ((c >> 16u32) & 0xffu32) as i64
}
#[inline(always)]
pub fn green_x(c: u32) -> (r: i64) ensures r == green(c), 0 <= r < 256,
{
    proof { assert((c >> 8u32) & 0xffu32 < 256) by (bit_vector); }
    ((c >> 8u32) & 0xffu32) as i64
}
#[inline(always)]
pub fn blue_x(c: u32) -> (r: i64) ensures r == blue(c), 0 <= r < 256,
{
    proof { assert(c & 0xffu32 < 256) by (bit_vector); }
    (c & 0xffu32) as i64
}

/// `x mod 256` (Euclidean, as the spec's `%`) of a channel sum in range.
pub fn byte_x(x: i64) -> (r: u32)
    requires -4096 <= x <= 4096,
    ensures r == byte(x as int), r < 256,
{
    proof {
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(16, x as int, 256);
    }
    ((x + 4096) % 256) as u32
}

/// `argb` of channel values in range.
pub fn argb_x(a: i64, r: i64, g: i64, b: i64) -> (c: u32)
    requires -4096 <= a <= 4096, -4096 <= r <= 4096, -4096 <= g <= 4096, -4096 <= b <= 4096,
    ensures c == argb(a as int, r as int, g as int, b as int),
{
    let (a8, r8, g8, b8) = (byte_x(a), byte_x(r), byte_x(g), byte_x(b));
    let c = pixel_x(a8, r8, g8, b8);
    proof {
        assert(byte(a8 as int) == a8 && byte(r8 as int) == r8 && byte(g8 as int) == g8 && byte(b8 as int) == b8);
    }
    c
}

/// A channel sum below 1024, mod 256, is its low byte.
proof fn lemma_byte_lo(x: u32)
    requires x < 1024,
    ensures byte(x as int) == x & 0xffu32,
{
    assert(x & 0xffu32 == x % 256) by (bit_vector);
}

/// `add_pixels`, a byte at a time in two lanes (alpha and green, red and
/// blue), as libwebp's `VP8LAddPixels`.
#[inline(always)]
pub fn add_pixels_x(a: u32, b: u32) -> (r: u32)
    ensures r == add_pixels(a, b),
{
    let ag: u64 = ((a & 0xff00ff00u32) as u64 + (b & 0xff00ff00u32) as u64) & 0xff00ff00u64;
    let rb: u64 = ((a & 0x00ff00ffu32) as u64 + (b & 0x00ff00ffu32) as u64) & 0x00ff00ffu64;
    let r = (ag | rb) as u32;
    proof {
        let aa: u32 = ((a >> 24u32) + (b >> 24u32)) as u32;
        let rr: u32 = (((a >> 16u32) & 0xffu32) + ((b >> 16u32) & 0xffu32)) as u32;
        let gg: u32 = (((a >> 8u32) & 0xffu32) + ((b >> 8u32) & 0xffu32)) as u32;
        let bb: u32 = ((a & 0xffu32) + (b & 0xffu32)) as u32;
        assert(a >> 24u32 < 256 && b >> 24u32 < 256) by (bit_vector);
        assert((a >> 16u32) & 0xffu32 < 256 && (b >> 16u32) & 0xffu32 < 256) by (bit_vector);
        assert((a >> 8u32) & 0xffu32 < 256 && (b >> 8u32) & 0xffu32 < 256) by (bit_vector);
        assert(a & 0xffu32 < 256 && b & 0xffu32 < 256) by (bit_vector);
        lemma_byte_lo(aa);
        lemma_byte_lo(rr);
        lemma_byte_lo(gg);
        lemma_byte_lo(bb);
        assert(r == ((aa & 0xffu32) << 24u32) | ((rr & 0xffu32) << 16u32) | ((gg & 0xffu32) << 8u32) | (bb & 0xffu32))
            by (bit_vector)
            requires
                ag == (((a & 0xff00ff00u32) as u64 + (b & 0xff00ff00u32) as u64) as u64) & 0xff00ff00u64,
                rb == (((a & 0x00ff00ffu32) as u64 + (b & 0x00ff00ffu32) as u64) as u64) & 0x00ff00ffu64,
                r == (ag | rb) as u32,
                aa == ((a >> 24u32) + (b >> 24u32)) as u32,
                rr == (((a >> 16u32) & 0xffu32) + ((b >> 16u32) & 0xffu32)) as u32,
                gg == (((a >> 8u32) & 0xffu32) + ((b >> 8u32) & 0xffu32)) as u32,
                bb == ((a & 0xffu32) + (b & 0xffu32)) as u32;
    }
    r
}

/// `average2`, as libwebp's `Average2`: half the XOR without each byte's
/// low bit, plus the AND.
#[inline(always)]
pub fn average2_x(a: u32, b: u32) -> (r: u32)
    ensures r == average2(a, b),
{
    let r = ((((a ^ b) & 0xfefefefeu32) >> 1u32) as u64 + (a & b) as u64) as u32;
    proof {
        let aa: u32 = (((a >> 24u32) + (b >> 24u32)) as u32) / 2;
        let rr: u32 = ((((a >> 16u32) & 0xffu32) + ((b >> 16u32) & 0xffu32)) as u32) / 2;
        let gg: u32 = ((((a >> 8u32) & 0xffu32) + ((b >> 8u32) & 0xffu32)) as u32) / 2;
        let bb: u32 = (((a & 0xffu32) + (b & 0xffu32)) as u32) / 2;
        assert(a >> 24u32 < 256 && b >> 24u32 < 256) by (bit_vector);
        assert((a >> 16u32) & 0xffu32 < 256 && (b >> 16u32) & 0xffu32 < 256) by (bit_vector);
        assert((a >> 8u32) & 0xffu32 < 256 && (b >> 8u32) & 0xffu32 < 256) by (bit_vector);
        assert(a & 0xffu32 < 256 && b & 0xffu32 < 256) by (bit_vector);
        lemma_byte_lo(aa);
        lemma_byte_lo(rr);
        lemma_byte_lo(gg);
        lemma_byte_lo(bb);
        assert(r == ((aa & 0xffu32) << 24u32) | ((rr & 0xffu32) << 16u32) | ((gg & 0xffu32) << 8u32) | (bb & 0xffu32))
            by (bit_vector)
            requires
                r == (((((a ^ b) & 0xfefefefeu32) >> 1u32) as u64 + (a & b) as u64) as u64) as u32,
                aa == (((a >> 24u32) + (b >> 24u32)) as u32) / 2,
                rr == ((((a >> 16u32) & 0xffu32) + ((b >> 16u32) & 0xffu32)) as u32) / 2,
                gg == ((((a >> 8u32) & 0xffu32) + ((b >> 8u32) & 0xffu32)) as u32) / 2,
                bb == (((a & 0xffu32) + (b & 0xffu32)) as u32) / 2;
    }
    r
}

#[inline(always)]
fn abs_x(x: i64) -> (r: i64)
    requires -1024 <= x <= 1024,
    ensures r == abs(x as int),
{
    if x < 0 { -x } else { x }
}

/// `Select`'s distance: the sum over the channels of |a - b|.
pub open spec fn sad(a: u32, b: u32) -> int {
    abs(alpha(a) - alpha(b)) + abs(red(a) - red(b)) + abs(green(a) - green(b)) + abs(blue(a) - blue(b))
}

#[inline(always)]
pub fn sad_x(a: u32, b: u32) -> (r: u32)
    ensures r as int == sad(a, b), r <= 1020,
{
    (abs_x(alpha_x(a) - alpha_x(b)) + abs_x(red_x(a) - red_x(b))
        + abs_x(green_x(a) - green_x(b)) + abs_x(blue_x(a) - blue_x(b))) as u32
}

#[inline(always)]
pub fn select_x(l: u32, t: u32, tl: u32) -> (r: u32)
    ensures r == select(l, t, tl),
{
    let pl = abs_x(alpha_x(t) - alpha_x(tl)) + abs_x(red_x(t) - red_x(tl))
        + abs_x(green_x(t) - green_x(tl)) + abs_x(blue_x(t) - blue_x(tl));
    let pt = abs_x(alpha_x(l) - alpha_x(tl)) + abs_x(red_x(l) - red_x(tl))
        + abs_x(green_x(l) - green_x(tl)) + abs_x(blue_x(l) - blue_x(tl));
    if pl < pt { l } else { t }
}

#[inline(always)]
fn clamp_x(a: i64) -> (r: i64)
    ensures r == clamp(a as int), 0 <= r <= 255,
{
    if a < 0 { 0 } else if a > 255 { 255 } else { a }
}

#[inline(always)]
fn cdiv2_x(x: i64) -> (r: i64)
    requires -1024 <= x <= 1024,
    ensures r == cdiv2(x as int), -512 <= r <= 512,
{
    if x >= 0 { x / 2 } else { -((-x) / 2) }
}

#[inline(always)]
pub fn clamp_add_subtract_full_x(a: u32, b: u32, c: u32) -> (r: u32)
    ensures r == clamp_add_subtract_full(a, b, c),
{
    let aa = clamp_x(alpha_x(a) + alpha_x(b) - alpha_x(c));
    let rr = clamp_x(red_x(a) + red_x(b) - red_x(c));
    let gg = clamp_x(green_x(a) + green_x(b) - green_x(c));
    let bb = clamp_x(blue_x(a) + blue_x(b) - blue_x(c));
    pixel_x(aa as u32, rr as u32, gg as u32, bb as u32)
}

#[inline(always)]
fn cash_x(a: i64, b: i64) -> (r: i64)
    requires 0 <= a < 256, 0 <= b < 256,
    ensures r == cash(a as int, b as int), 0 <= r <= 255,
{
    clamp_x(a + cdiv2_x(a - b))
}

#[inline(always)]
pub fn clamp_add_subtract_half_x(a: u32, b: u32) -> (r: u32)
    ensures r == clamp_add_subtract_half(a, b),
{
    let aa = cash_x(alpha_x(a), alpha_x(b));
    let rr = cash_x(red_x(a), red_x(b));
    let gg = cash_x(green_x(a), green_x(b));
    let bb = cash_x(blue_x(a), blue_x(b));
    pixel_x(aa as u32, rr as u32, gg as u32, bb as u32)
}

#[inline(always)]
pub fn predict_x(mode: i64, l: u32, t: u32, tr: u32, tl: u32) -> (r: u32)
    ensures r == predict(mode as int, l, t, tr, tl),
{
    if mode == 1 { l }
    else if mode == 2 { t }
    else if mode == 3 { tr }
    else if mode == 4 { tl }
    else if mode == 5 { average2_x(average2_x(l, tr), t) }
    else if mode == 6 { average2_x(l, tl) }
    else if mode == 7 { average2_x(l, t) }
    else if mode == 8 { average2_x(tl, t) }
    else if mode == 9 { average2_x(t, tr) }
    else if mode == 10 { average2_x(average2_x(l, tl), average2_x(t, tr)) }
    else if mode == 11 { select_x(l, t, tl) }
    else if mode == 12 { clamp_add_subtract_full_x(l, t, tl) }
    else if mode == 13 { clamp_add_subtract_half_x(average2_x(l, t), tl) }
    else { 0xff000000u32 }
}

fn sbyte_x(v: i64) -> (r: i64)
    requires 0 <= v < 256,
    ensures r == sbyte(v as int), -128 <= r < 128,
{
    if v >= 128 { v - 256 } else { v }
}

/// `ct_delta`: the product's floor over 32, computed on a nonnegative number.
fn ct_delta_x(t: i64, c: i64) -> (r: i64)
    requires 0 <= t < 256, 0 <= c < 256,
    ensures r == ct_delta(t as int, c as int), -512 <= r <= 512,
{
    let st = sbyte_x(t);
    let sc = sbyte_x(c);
    proof {
        assert(-16384 <= st * sc <= 16384) by (nonlinear_arith) requires -128 <= st < 128, -128 <= sc < 128;
    }
    let x = st * sc;
    let r = (x + 16384) / 32 - 512;
    proof {
        vstd::arithmetic::div_mod::lemma_hoist_over_denominator(x as int, 512, 32);
        assert((x as int + 16384) / 32 == (x as int) / 32 + 512);
        assert((x as int) / 32 >= -512 && (x as int) / 32 <= 512) by (nonlinear_arith) requires -16384 <= x <= 16384;
    }
    r
}

/// A signed byte, from a byte.
#[inline(always)]
fn sb32(v: u32) -> (r: i32)
    requires v < 256,
    ensures r as int == sbyte(v as int), -128 <= r < 128,
{
    if v >= 128 { v as i32 - 256 } else { v as i32 }
}

/// A tile element's multipliers as signed bytes: green to red, green to
/// blue, red to blue.
#[inline(always)]
pub fn ct_mults(e: u32) -> (r: (i32, i32, i32))
    ensures r.0 as int == sbyte(blue(e)), r.1 as int == sbyte(green(e)), r.2 as int == sbyte(red(e)),
        -128 <= r.0 < 128, -128 <= r.1 < 128, -128 <= r.2 < 128,
{
    proof { assert(e & 0xffu32 < 256 && (e >> 8u32) & 0xffu32 < 256 && (e >> 16u32) & 0xffu32 < 256) by (bit_vector); }
    (sb32(e & 0xffu32), sb32((e >> 8u32) & 0xffu32), sb32((e >> 16u32) & 0xffu32))
}

/// `ColorTransformDelta` of signed bytes: the product's floor over 32.
#[inline(always)]
fn ctd(st: i32, sc: i32) -> (r: i32)
    requires -128 <= st < 128, -128 <= sc < 128,
    ensures r as int == (st as int * sc as int) / 32, -512 <= r <= 512,
{
    proof {
        assert(-16384 <= st * sc <= 16384) by (nonlinear_arith) requires -128 <= st < 128, -128 <= sc < 128;
    }
    let x = st * sc;
    let u = ((x + 16384) as u32) >> 5u32;
    proof {
        vstd::bits::lemma_u32_shr_is_div((x + 16384) as u32, 5);
        assert(vstd::arithmetic::power2::pow2(5) == 32) by { vstd::arithmetic::power2::lemma2_to64(); }
        vstd::arithmetic::div_mod::lemma_hoist_over_denominator(x as int, 512, 32);
        assert((x as int + 16384) / 32 == (x as int) / 32 + 512);
        assert((x as int) / 32 >= -512 && (x as int) / 32 <= 512) by (nonlinear_arith) requires -16384 <= x <= 16384;
    }
    u as i32 - 512
}

/// `v mod 256` of `v >= -1024`, as a byte of `v + 1024`.
proof fn lemma_mod_byte(v: int)
    requires -1024 <= v <= 4096,
    ensures ((v + 1024) as u32) & 0xffu32 == v % 256,
{
    let u = (v + 1024) as u32;
    assert(u & 0xffu32 == u % 256) by (bit_vector);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(4, v, 256);
}

/// `inv_color_px` with the element's multipliers given.
#[inline(always)]
pub fn inv_color_fast(c: u32, g2r: i32, g2b: i32, r2b: i32, Ghost(e): Ghost<u32>) -> (r: u32)
    requires g2r as int == sbyte(blue(e)), g2b as int == sbyte(green(e)), r2b as int == sbyte(red(e)),
        -128 <= g2r < 128, -128 <= g2b < 128, -128 <= r2b < 128,
    ensures r == inv_color_px(c, e),
{
    proof { assert((c >> 8u32) & 0xffu32 < 256 && (c >> 16u32) & 0xffu32 < 256 && c & 0xffu32 < 256) by (bit_vector); }
    let gu = (c >> 8u32) & 0xffu32;
    let sg = sb32(gu);
    let red = ((c >> 16u32) & 0xffu32) as i32;
    let blue = (c & 0xffu32) as i32;
    let d1 = ctd(g2r, sg);
    let nr = ((red + d1 + 1024) as u32) & 0xffu32;
    proof { lemma_mod_byte(red + d1); assert(nr < 256) by (bit_vector) requires nr == ((red + d1 + 1024) as u32) & 0xffu32; }
    let snr = sb32(nr);
    let d2 = ctd(g2b, sg);
    let d3 = ctd(r2b, snr);
    let nb = ((blue + d2 + d3 + 1024) as u32) & 0xffu32;
    proof { lemma_mod_byte(blue + d2 + d3); assert(nb < 256) by (bit_vector) requires nb == ((blue + d2 + d3 + 1024) as u32) & 0xffu32; }
    let r = (c & 0xff00ff00u32) | (nr << 16u32) | nb;
    proof {
        let aa: u32 = c >> 24u32;
        assert(aa < 256) by (bit_vector) requires aa == c >> 24u32;
        lemma_byte_lo(aa);
        lemma_byte_lo(gu);
        lemma_byte_lo(nr);
        lemma_byte_lo(nb);
        assert(nr & 0xffu32 == nr && nb & 0xffu32 == nb) by (bit_vector) requires nr < 256, nb < 256;
        assert(r == ((aa & 0xffu32) << 24u32) | ((nr & 0xffu32) << 16u32) | ((gu & 0xffu32) << 8u32) | (nb & 0xffu32))
            by (bit_vector)
            requires r == (c & 0xff00ff00u32) | (nr << 16u32) | nb, aa == c >> 24u32, gu == (c >> 8u32) & 0xffu32,
                nr < 256, nb < 256;
    }
    r
}

pub fn inv_color_px_x(c: u32, e: u32) -> (r: u32)
    ensures r == inv_color_px(c, e),
{
    let g = green_x(c);
    let nr0 = red_x(c) + ct_delta_x(blue_x(e), g);
    let nr = (nr0 + 4096) % 256;
    proof { vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(16, nr0 as int, 256); }
    let nb = blue_x(c) + ct_delta_x(green_x(e), g) + ct_delta_x(red_x(e), nr);
    argb_x(alpha_x(c), nr, g, nb)
}

// ------------------------------------------------------- whole images

/// A sub-resolution image of `2^bits` tiles covers an image `w` x `h`.
pub open spec fn tiles_wf(img: Seq<u32>, bits: nat, w: nat, h: nat) -> bool {
    img.len() == div_round_up(w, p2(bits)) * div_round_up(h, p2(bits))
}

/// `x >> bits` is `x / 2^bits`.
pub proof fn lemma_shr_div(x: u64, bits: u64)
    requires bits < 64,
    ensures (x >> bits) as nat == x as nat / p2(bits as nat),
{
    vstd::bits::lemma_u64_shr_is_div(x, bits);
    vbits::prim_read::lemma_p2_eq_pow2(bits as nat);
}

/// The tile size `2^bits` and the number of tiles in a row, by shifts.
pub fn tile_dims(bits: u64, w: usize) -> (r: (usize, usize))
    requires 2 <= bits <= 9, 1 <= w <= 16384,
    ensures r.0 as nat == p2(bits as nat), r.1 as nat == div_round_up(w as nat, p2(bits as nat)),
        4 <= r.0 <= 512, r.0 == (1u64 << bits), 1 <= r.1 <= 16384,
{
    let t: usize = (1u64 << bits) as usize;
    proof {
        lemma_shl1(bits);
        vbits::prim_read::lemma_p2_mono(bits as nat, 9);
        vbits::prim_read::lemma_p2_mono(2, bits as nat);
        assert(p2(9) == 512 && p2(2) == 4) by { reveal_with_fuel(p2, 10); }
    }
    let tw = (((w + t - 1) as u64) >> bits) as usize;
    proof {
        lemma_shr_div((w + t - 1) as u64, bits);
        assert((w + t - 1) as nat / (t as nat) >= 1) by (nonlinear_arith) requires w >= 1, t >= 1;
        assert((w + t - 1) as nat / (t as nat) <= w) by (nonlinear_arith) requires w >= 1, t >= 1;
    }
    (t, tw)
}

/// Stepping to `x + 1` inside a tile keeps the tile.
pub proof fn lemma_same_tile(x: u64, bits: u64, t: u64)
    requires 1 <= bits <= 9, t == (1u64 << bits), x < 0x1_0000, ((x + 1) as u64) & ((t - 1) as u64) != 0,
    ensures ((x + 1) as u64) >> bits == x >> bits,
{
    assert(((x + 1) as u64) >> bits == x >> bits) by (bit_vector)
        requires 1 <= bits <= 9, t == (1u64 << bits), x < 0x1_0000, ((x + 1) as u64) & ((t - 1) as u64) != 0;
}

/// The same pixel with green added to red and blue (`AddGreenToBlueAndRed`),
/// two channels at once.
#[inline(always)]
pub fn sub_green_px(c: u32) -> (r: u32)
    ensures r == argb(alpha(c), red(c) + green(c), green(c), blue(c) + green(c)),
{
    let g = (c >> 8u32) & 0xffu32;
    let rb: u64 = (((c & 0x00ff00ffu32) as u64 + ((g << 16u32) | g) as u64) as u64) & 0x00ff00ffu64;
    let r = (c & 0xff00ff00u32) | (rb as u32);
    proof {
        let aa: u32 = c >> 24u32;
        let rr: u32 = (((c >> 16u32) & 0xffu32) + g) as u32;
        let bb: u32 = ((c & 0xffu32) + g) as u32;
        assert(c >> 24u32 < 256 && (c >> 16u32) & 0xffu32 < 256 && g < 256 && c & 0xffu32 < 256) by (bit_vector)
            requires g == (c >> 8u32) & 0xffu32;
        assert(rr as int == red(c) + green(c) && bb as int == blue(c) + green(c) && aa as int == alpha(c));
        lemma_byte_lo(aa);
        lemma_byte_lo(rr);
        lemma_byte_lo(g);
        lemma_byte_lo(bb);
        assert(r == ((aa & 0xffu32) << 24u32) | ((rr & 0xffu32) << 16u32) | ((g & 0xffu32) << 8u32) | (bb & 0xffu32))
            by (bit_vector)
            requires
                g == (c >> 8u32) & 0xffu32,
                rb == (((c & 0x00ff00ffu32) as u64 + ((g << 16u32) | g) as u64) as u64) & 0x00ff00ffu64,
                r == (c & 0xff00ff00u32) | (rb as u32),
                aa == c >> 24u32,
                rr == (((c >> 16u32) & 0xffu32) + g) as u32,
                bb == ((c & 0xffu32) + g) as u32;
    }
    r
}

/// `inv_subtract_green`, in place.
pub fn inv_subtract_green_x(px: &mut Vec<u32>)
    ensures final(px)@ == inv_subtract_green(old(px)@),
{
    let ghost px0 = px@;
    let n = px.len();
    let mut i: usize = 0;
    #[cfg(target_arch = "x86_64")]
    while n - i >= 4
        invariant
            n == px@.len(), n == px0.len(), i <= n,
            forall|k: int| 0 <= k < i ==> #[trigger] px@[k] == inv_subtract_green(px0)[k],
            forall|k: int| i <= k < n ==> #[trigger] px@[k] == px0[k],
        decreases n - i,
    {
        let v = vsimd::x86::loadu_u32(px.as_slice(), i);
        let r = crate::invx::sub_green4(v);
        let ghost pre = px@;
        vsimd::x86::storeu_u32(px, i, r);
        proof {
            assert forall|k: int| 0 <= k < i + 4 implies #[trigger] px@[k] == inv_subtract_green(px0)[k] by {
                if k >= i {
                    let j = k - i;
                    crate::invx::lemma_sg_lane(vsimd::x86::v8(v), vsimd::x86::v8(r), pre[k], j);
                }
            }
        }
        i = i + 4;
    }
    while i < n
        invariant
            n == px@.len(), n == px0.len(), i <= n,
            forall|k: int| 0 <= k < i ==> #[trigger] px@[k] == inv_subtract_green(px0)[k],
            forall|k: int| i <= k < n ==> #[trigger] px@[k] == px0[k],
        decreases n - i,
    {
        let c = vsimd::mem::get(px.as_slice(), i);
        vsimd::mem::vset(px, i, sub_green_px(c));
        i = i + 1;
    }
    proof { assert(px@ =~= inv_subtract_green(px0)); }
}

/// `inv_color`, for an image `w` x `h`, in place, a row at a time; each
/// tile's element is read at its first column.
pub fn inv_color_x(bits: u64, w: usize, h: usize, img: &Vec<u32>, px: &mut Vec<u32>)
    requires 2 <= bits <= 9, 1 <= w <= 16384, 1 <= h <= 16384, old(px)@.len() == w * h,
        tiles_wf(img@, bits as nat, w as nat, h as nat),
    ensures final(px)@ == inv_color(bits as nat, w as nat, img@, old(px)@),
{
    #[cfg(target_arch = "x86_64")]
    crate::invx::inv_color_sse2(bits, w, h, img, px);
    #[cfg(not(target_arch = "x86_64"))]
    inv_color_scalar_x(bits, w, h, img, px);
}

/// The same, one pixel at a time.
pub fn inv_color_scalar_x(bits: u64, w: usize, h: usize, img: &Vec<u32>, px: &mut Vec<u32>)
    requires 2 <= bits <= 9, 1 <= w <= 16384, 1 <= h <= 16384, old(px)@.len() == w * h,
        tiles_wf(img@, bits as nat, w as nat, h as nat),
    ensures final(px)@ == inv_color(bits as nat, w as nat, img@, old(px)@),
{
    let ghost px0 = px@;
    let ghost f = inv_color(bits as nat, w as nat, img@, px0);
    proof { assert(w * h <= 0x1000_0000) by (nonlinear_arith) requires w <= 16384, h <= 16384; }
    let n = px.len();
    let (t, tw) = tile_dims(bits, w);
    let mut y: usize = 0;
    let mut row: usize = 0;
    while y < h
        invariant
            2 <= bits <= 9, 1 <= w <= 16384, 1 <= h <= 16384, n == w * h, n <= 0x1000_0000, px@.len() == n,
            px0.len() == n, f == inv_color(bits as nat, w as nat, img@, px0), f.len() == n,
            tiles_wf(img@, bits as nat, w as nat, h as nat),
            t as nat == p2(bits as nat), tw as nat == div_round_up(w as nat, p2(bits as nat)), t == (1u64 << bits),
            4 <= t <= 512, 1 <= tw <= 16384,
            y <= h, row == y * w,
            forall|k: int| 0 <= k < row ==> #[trigger] px@[k] == f[k],
            forall|k: int| row <= k < n ==> #[trigger] px@[k] == px0[k],
        decreases h - y,
    {
        proof {
            assert(row + w <= n) by (nonlinear_arith) requires row == y * w, y < h, n == w * h;
        }
        let ty = ((y as u64) >> bits) as usize;
        proof {
            lemma_shr_div(y as u64, bits);
            crate::pix::lemma_tile_in(w as nat, h as nat, bits as nat, 0, y as nat);
            assert(ty * tw + tw <= img@.len()) by (nonlinear_arith)
                requires ty < div_round_up(h as nat, p2(bits as nat)), img@.len() == tw * div_round_up(h as nat, p2(bits as nat));
            assert(ty <= y) by (nonlinear_arith) requires ty == y as nat / p2(bits as nat), p2(bits as nat) >= 1;
            assert(ty * tw + tw <= 16384 * 16384 + 16384) by (nonlinear_arith) requires ty < 16384, tw <= 16384;
        }
        let trow = ty * tw;
        let mut x: usize = 0;
        let mut e: u32 = 0;
        let mut g2r: i32 = 0;
        let mut g2b: i32 = 0;
        let mut r2b: i32 = 0;
        proof {
            assert(0u64 & ((t - 1) as u64) == 0) by (bit_vector);
            assert(0u32 & 0xffu32 == 0 && (0u32 >> 8u32) & 0xffu32 == 0 && (0u32 >> 16u32) & 0xffu32 == 0) by (bit_vector);
        }
        while x < w
            invariant
                2 <= bits <= 9, 1 <= w <= 16384, 1 <= h <= 16384, n == w * h, px@.len() == n,
                px0.len() == n, f == inv_color(bits as nat, w as nat, img@, px0), f.len() == n,
                tiles_wf(img@, bits as nat, w as nat, h as nat),
                t as nat == p2(bits as nat), tw as nat == div_round_up(w as nat, p2(bits as nat)), t == (1u64 << bits),
                4 <= t <= 512, 1 <= tw <= 16384,
                y < h, row == y * w, row + w <= n, x <= w, ty as nat == y as nat / p2(bits as nat), trow == ty * tw,
                trow + tw <= img@.len(), trow + tw <= 16384 * 16384 + 16384,
                x < w && (x as u64) & ((t - 1) as u64) != 0 ==> e == tile(img@, bits as nat, w as nat, x as nat, y as nat),
                g2r as int == sbyte(blue(e)), g2b as int == sbyte(green(e)), r2b as int == sbyte(red(e)),
                -128 <= g2r < 128, -128 <= g2b < 128, -128 <= r2b < 128,
                forall|k: int| 0 <= k < row + x ==> #[trigger] px@[k] == f[k],
                forall|k: int| row + x <= k < n ==> #[trigger] px@[k] == px0[k],
            decreases w - x,
        {
            if (x as u64) & ((t - 1) as u64) == 0 {
                proof {
                    lemma_shr_div(x as u64, bits);
                    crate::pix::lemma_tile_in(w as nat, h as nat, bits as nat, x as nat, y as nat);
                }
                let tx = ((x as u64) >> bits) as usize;
                e = img[trow + tx];
                let m = ct_mults(e);
                g2r = m.0;
                g2b = m.1;
                r2b = m.2;
            }
            let i = row + x;
            proof {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(i as int, w as int, y as int, x as int);
                assert(f[i as int] == inv_color_px(px0[i as int], tile(img@, bits as nat, w as nat, x as nat, y as nat)));
            }
            let c = vsimd::mem::get(px.as_slice(), i);
            vsimd::mem::vset(px, i, inv_color_fast(c, g2r, g2b, r2b, Ghost(e)));
            x = x + 1;
            proof {
                if x < w && (x as u64) & ((t - 1) as u64) != 0 {
                    lemma_same_tile((x - 1) as u64, bits, t as u64);
                    lemma_shr_div(x as u64, bits);
                    lemma_shr_div((x - 1) as u64, bits);
                }
            }
        }
        proof { assert(row + w == (y + 1) * w) by (nonlinear_arith) requires row == y * w; }
        row = row + w;
        y = y + 1;
    }
    proof {
        assert(row == n) by (nonlinear_arith) requires row == y * w, y == h, n == w * h;
        assert(px@ =~= f);
    }
}

/// One pixel of the inverse predictor, in place: pixel `i` is the stream's
/// pixel plus its prediction `pr` from the pixels before it.
#[inline(always)]
fn pred_px(px: &mut Vec<u32>, i: usize, pr: u32, Ghost(bits): Ghost<nat>, Ghost(w): Ghost<nat>,
           Ghost(img): Ghost<Seq<u32>>, Ghost(px0): Ghost<Seq<u32>>, Ghost(target): Ghost<Seq<u32>>) -> (c: u32)
    requires
        i < old(px)@.len(), old(px)@.len() == px0.len(),
        forall|k: int| i <= k < px0.len() ==> #[trigger] old(px)@[k] == px0[k],
        pr == prediction(bits, w, img, old(px)@.take(i as int), i as int),
        inv_predictor(bits, w, img, px0, old(px)@.take(i as int)) == target,
    ensures
        final(px)@.len() == px0.len(), final(px)@ == old(px)@.update(i as int, c),
        forall|k: int| i + 1 <= k < px0.len() ==> #[trigger] final(px)@[k] == px0[k],
        inv_predictor(bits, w, img, px0, final(px)@.take(i + 1)) == target,
{
    let ghost out = px@.take(i as int);
    let c = add_pixels_x(vsimd::mem::get(px.as_slice(), i), pr);
    vsimd::mem::vset(px, i, c);
    proof {
        assert(px@.take(i + 1) =~= out.push(c));
        assert(out.len() == i);
    }
    c
}

/// The prediction of a pixel off the top row and left column.
pub proof fn lemma_prediction_at(bits: nat, w: nat, img: Seq<u32>, out: Seq<u32>, i: int, x: nat, y: nat, mode: int)
    requires 1 <= x < w, 1 <= y, i == y * w + x, out.len() == i,
        green(tile(img, bits, w, x, y)) % 16 == mode,
    ensures prediction(bits, w, img, out, i) == predict(mode, out[i - 1], out[i - w], out[i - w + 1], out[i - w - 1]),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(i, w as int, y as int, x as int);
}

/// The pixels `x0..x1` of row `y >= 1` (`x0 >= 1`), all of whose tiles
/// have the mode `mode`.
#[inline(always)]
pub fn pred_run(mode: i64, px: &mut Vec<u32>, y: usize, row: usize, x0: usize, x1: usize, w: usize,
            Ghost(bits): Ghost<nat>, Ghost(img): Ghost<Seq<u32>>, Ghost(px0): Ghost<Seq<u32>>, Ghost(target): Ghost<Seq<u32>>)
    requires
        1 <= y, row == y * w, 1 <= x0 <= x1 <= w, w <= 16384, old(px)@.len() == px0.len(), row + w <= px0.len(),
        px0.len() <= 0x1000_0000,
        forall|k: int| row + x0 <= k < px0.len() ==> #[trigger] old(px)@[k] == px0[k],
        inv_predictor(bits, w as nat, img, px0, old(px)@.take(row + x0)) == target,
        forall|x: int| x0 <= x < x1 ==> #[trigger] green(tile(img, bits, w as nat, x as nat, y as nat)) % 16 == mode,
    ensures
        final(px)@.len() == px0.len(),
        forall|k: int| row + x1 <= k < px0.len() ==> #[trigger] final(px)@[k] == px0[k],
        inv_predictor(bits, w as nat, img, px0, final(px)@.take(row + x1)) == target,
{
    let mut i = row + x0;
    let end = row + x1;
    proof { assert(i >= 1) by (nonlinear_arith) requires i >= row + 1; }
    let mut l = vsimd::mem::get(px.as_slice(), i - 1);
    proof { assert(i >= w + 1) by (nonlinear_arith) requires i >= row + 1, row == y * w, y >= 1; }
    // the row above, carried along: T and TL
    let mut t = vsimd::mem::get(px.as_slice(), i - w);
    let mut tl = vsimd::mem::get(px.as_slice(), i - w - 1);
    while i < end
        invariant
            1 <= y, row == y * w, 1 <= x0 <= x1 <= w, px@.len() == px0.len(), row + w <= px0.len(), px0.len() <= 0x1000_0000,
            row + x0 <= i <= end, end == row + x1, i >= 1, l == px@[i - 1], i >= w + 1,
            t == px@[i - w], tl == px@[i - w - 1],
            forall|k: int| i <= k < px0.len() ==> #[trigger] px@[k] == px0[k],
            inv_predictor(bits, w as nat, img, px0, px@.take(i as int)) == target,
            forall|x: int| x0 <= x < x1 ==> #[trigger] green(tile(img, bits, w as nat, x as nat, y as nat)) % 16 == mode,
        decreases end - i,
    {
        proof {
            assert(i >= w + 1) by (nonlinear_arith) requires i >= row + 1, row == y * w, y >= 1;
        }
        let tr = vsimd::mem::get(px.as_slice(), i - w + 1);
        let pr = predict_x(mode, l, t, tr, tl);
        proof {
            let x = (i - row) as int;
            let out = px@.take(i as int);
            assert(green(tile(img, bits, w as nat, x as nat, y as nat)) % 16 == mode);
            lemma_prediction_at(bits, w as nat, img, out, i as int, x as nat, y as nat, mode as int);
            assert(out[i - 1] == l && out[i - w] == t && out[i - w + 1] == tr && out[i - w - 1] == tl);
        }
        l = pred_px(px, i, pr, Ghost(bits), Ghost(w as nat), Ghost(img), Ghost(px0), Ghost(target));
        tl = t;
        t = tr;
        i = i + 1;
    }
}

/// Mode 11 (Select) on pixels `x0..x1` of row `y >= 1` (`x0 >= 1`): first
/// each pixel's distance between T and TL, which the row above fixes, into
/// `pl`; then the pixels in order, each comparing it with L's.
fn pred_run11(px: &mut Vec<u32>, pl: &mut Vec<u32>, y: usize, row: usize, x0: usize, x1: usize, w: usize,
              Ghost(bits): Ghost<nat>, Ghost(img): Ghost<Seq<u32>>, Ghost(px0): Ghost<Seq<u32>>, Ghost(target): Ghost<Seq<u32>>)
    requires
        1 <= y, row == y * w, 1 <= x0 <= x1 <= w, w <= 16384, old(px)@.len() == px0.len(), row + w <= px0.len(),
        px0.len() <= 0x1000_0000, old(pl)@.len() == w + 4,
        forall|k: int| row + x0 <= k < px0.len() ==> #[trigger] old(px)@[k] == px0[k],
        inv_predictor(bits, w as nat, img, px0, old(px)@.take(row + x0)) == target,
        forall|x: int| x0 <= x < x1 ==> #[trigger] green(tile(img, bits, w as nat, x as nat, y as nat)) % 16 == 11,
    ensures
        final(px)@.len() == px0.len(), final(pl)@.len() == w + 4,
        forall|k: int| row + x1 <= k < px0.len() ==> #[trigger] final(px)@[k] == px0[k],
        inv_predictor(bits, w as nat, img, px0, final(px)@.take(row + x1)) == target,
{
    let ghost pre = px@;
    proof { assert(row >= w) by (nonlinear_arith) requires row == y * w, y >= 1; }
    let up = row - w;
    fill_sad(px, pl, up, x0, x1, w);
    let mut i = row + x0;
    let end = row + x1;
    let mut l = vsimd::mem::get(px.as_slice(), i - 1);
    let mut t = vsimd::mem::get(px.as_slice(), i - w);
    let mut tl = vsimd::mem::get(px.as_slice(), i - w - 1);
    while i < end
        invariant
            1 <= y, row == y * w, 1 <= x0 <= x1 <= w, px@.len() == px0.len(), row + w <= px0.len(), px0.len() <= 0x1000_0000,
            row + x0 <= i <= end, end == row + x1, i >= 1, l == px@[i - 1], i >= w + 1, up == row - w,
            t == px@[i - w], tl == px@[i - w - 1], pl@.len() == w + 4, pre.len() == px0.len(),
            forall|k: int| 0 <= k < row + x0 ==> #[trigger] px@[k] == pre[k],
            forall|x: int| x0 <= x < x1 ==> #[trigger] pl@[x] as int == sad(pre[up + x], pre[up + x - 1]),
            forall|k: int| i <= k < px0.len() ==> #[trigger] px@[k] == px0[k],
            inv_predictor(bits, w as nat, img, px0, px@.take(i as int)) == target,
            forall|x: int| x0 <= x < x1 ==> #[trigger] green(tile(img, bits, w as nat, x as nat, y as nat)) % 16 == 11,
        decreases end - i,
    {
        let tr = vsimd::mem::get(px.as_slice(), i - w + 1);
        let x = i - row;
        let a = vsimd::mem::get(pl.as_slice(), x);
        // both sums at once, off the chain through L; then the choice
        let src = vsimd::mem::get(px.as_slice(), i);
        let cl = add_pixels_x(src, l);
        let ct = add_pixels_x(src, t);
        let pr = if a < sad_x(l, tl) { l } else { t };
        let c = if a < sad_x(l, tl) { cl } else { ct };
        proof {
            let out = px@.take(i as int);
            let xi = x as int;
            assert(x0 <= xi < x1);
            assert(green(tile(img, bits, w as nat, xi as nat, y as nat)) % 16 == 11);
            lemma_prediction_at(bits, w as nat, img, out, i as int, x as nat, y as nat, 11);
            assert(out[i - 1] == l && out[i - w] == t && out[i - w + 1] == tr && out[i - w - 1] == tl);
            assert(pre[up + x] == t && pre[up + x - 1] == tl);
            assert(pr == select(l, t, tl));
            assert(c == add_pixels(px0[i as int], pr));
        }
        let ghost before = px@;
        vsimd::mem::vset(px, i, c);
        proof {
            assert(px@.take(i as int) =~= before.take(i as int));
            lemma_pred_step(bits, w as nat, img, px0, px@, i as int);
        }
        l = c;
        tl = t;
        t = tr;
        i = i + 1;
    }
}

/// `pl[x]` for `x0 <= x < x1`: the distance between pixel `up + x` and the
/// one before it.
fn fill_sad(px: &Vec<u32>, pl: &mut Vec<u32>, up: usize, x0: usize, x1: usize, w: usize)
    requires 1 <= x0 <= x1 <= w, up + w <= px@.len(), old(pl)@.len() == w + 4, w <= 16384, px@.len() <= 0x1000_0000,
    ensures final(pl)@.len() == w + 4,
        forall|x: int| x0 <= x < x1 ==> #[trigger] final(pl)@[x] as int == sad(px@[up + x], px@[up + x - 1]),
{
    #[cfg(target_arch = "x86_64")]
    let mut x = crate::invx::fill_sad4(px, pl, up, x0, x1, w);
    #[cfg(not(target_arch = "x86_64"))]
    let mut x = x0;
    while x < x1
        invariant 1 <= x0 <= x <= x1 <= w, up + w <= px@.len(), pl@.len() == w + 4, px@.len() <= 0x1000_0000,
            forall|xx: int| x0 <= xx < x ==> #[trigger] pl@[xx] as int == sad(px@[up + xx], px@[up + xx - 1]),
        decreases x1 - x,
    {
        let a = vsimd::mem::get(px.as_slice(), up + x);
        let b = vsimd::mem::get(px.as_slice(), up + x - 1);
        vsimd::mem::vset(pl, x, sad_x(a, b));
        x = x + 1;
    }
}

/// Modes 0, 2, 3 and 4 (black, T, TR, TL: nothing from the left) four
/// pixels at a time where there are four (x86-64), else one at a time.
#[inline(always)]
fn pred_run_up(mode: i64, px: &mut Vec<u32>, y: usize, row: usize, x0: usize, x1: usize, w: usize,
               Ghost(bits): Ghost<nat>, Ghost(img): Ghost<Seq<u32>>, Ghost(px0): Ghost<Seq<u32>>, Ghost(target): Ghost<Seq<u32>>)
    requires
        mode == 0 || mode == 2 || mode == 3 || mode == 4,
        1 <= y, row == y * w, 1 <= x0 <= x1 <= w, w <= 16384, old(px)@.len() == px0.len(), row + w <= px0.len(),
        px0.len() <= 0x1000_0000,
        forall|k: int| row + x0 <= k < px0.len() ==> #[trigger] old(px)@[k] == px0[k],
        inv_predictor(bits, w as nat, img, px0, old(px)@.take(row + x0)) == target,
        forall|x: int| x0 <= x < x1 ==> #[trigger] green(tile(img, bits, w as nat, x as nat, y as nat)) % 16 == mode,
    ensures
        final(px)@.len() == px0.len(),
        forall|k: int| row + x1 <= k < px0.len() ==> #[trigger] final(px)@[k] == px0[k],
        inv_predictor(bits, w as nat, img, px0, final(px)@.take(row + x1)) == target,
{
    #[cfg(target_arch = "x86_64")]
    let x = crate::invx::pred_up4(mode, px, y, row, x0, x1, w, Ghost(bits), Ghost(img), Ghost(px0), Ghost(target));
    #[cfg(not(target_arch = "x86_64"))]
    let x = x0;
    pred_run(mode, px, y, row, x, x1, w, Ghost(bits), Ghost(img), Ghost(px0), Ghost(target));
}

/// One pixel of the inverse predictor, as a fact about a sequence.
pub proof fn lemma_pred_step(bits: nat, w: nat, img: Seq<u32>, px0: Seq<u32>, s: Seq<u32>, j: int)
    requires 0 <= j < px0.len(), j < s.len(),
        s[j] == add_pixels(px0[j], prediction(bits, w, img, s.take(j), j)),
    ensures inv_predictor(bits, w, img, px0, s.take(j)) == inv_predictor(bits, w, img, px0, s.take(j + 1)),
{
    assert(s.take(j).push(s[j]) =~= s.take(j + 1));
}

/// `inv_predictor`, for an image `w` x `h`, in place: the first pixel, the
/// top row, then each row's first pixel and its tiles, each run with its
/// mode fixed.
pub fn inv_predictor_x(bits: u64, w: usize, h: usize, img: &Vec<u32>, px: &mut Vec<u32>)
    requires 2 <= bits <= 9, 1 <= w <= 16384, 1 <= h <= 16384, old(px)@.len() == w * h,
        tiles_wf(img@, bits as nat, w as nat, h as nat),
    ensures final(px)@ == inv_predictor(bits as nat, w as nat, img@, old(px)@, Seq::empty()), final(px)@.len() == w * h,
{
    let ghost px0 = px@;
    let ghost gb = bits as nat;
    let ghost gw = w as nat;
    let ghost target = inv_predictor(gb, gw, img@, px0, Seq::empty());
    proof {
        assert(w * h <= 0x1000_0000) by (nonlinear_arith) requires w <= 16384, h <= 16384;
        assert(px@.take(0) =~= Seq::<u32>::empty());
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(0, w as int, 0, 0);
    }
    let n = px.len();
    proof { assert(n >= 1) by (nonlinear_arith) requires n == w * h, w >= 1, h >= 1; }
    pred_px(px, 0, 0xff000000u32, Ghost(gb), Ghost(gw), Ghost(img@), Ghost(px0), Ghost(target));
    let mut i: usize = 1;
    while i < w
        invariant
            1 <= w <= 16384, 1 <= h <= 16384, n == w * h, px@.len() == n, px0.len() == n, 1 <= i <= w,
            gb == bits, gw == w,
            forall|k: int| i <= k < n ==> #[trigger] px@[k] == px0[k],
            inv_predictor(gb, gw, img@, px0, px@.take(i as int)) == target,
        decreases w - i,
    {
        proof {
            assert(w <= n) by (nonlinear_arith) requires n == w * h, h >= 1;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(i as int, w as int, 0, i as int);
        }
        let pr = px[i - 1];
        pred_px(px, i, pr, Ghost(gb), Ghost(gw), Ghost(img@), Ghost(px0), Ghost(target));
        i = i + 1;
    }
    let (t, tw) = tile_dims(bits, w);
    let mut pl: Vec<u32> = vec![0u32; w + 4];
    let mut y: usize = 1;
    let mut row: usize = w;
    while y < h
        invariant
            2 <= bits <= 9, 1 <= w <= 16384, 1 <= h <= 16384, n == w * h, n <= 0x1000_0000, px@.len() == n, px0.len() == n,
            gb == bits, gw == w,
            tiles_wf(img@, bits as nat, w as nat, h as nat),
            t as nat == p2(bits as nat), tw as nat == div_round_up(w as nat, p2(bits as nat)), t == (1u64 << bits),
            4 <= t <= 512, 1 <= tw <= 16384,
            1 <= y <= h, row == y * w, pl@.len() == w + 4,
            forall|k: int| row <= k < n ==> #[trigger] px@[k] == px0[k],
            inv_predictor(gb, gw, img@, px0, px@.take(row as int)) == target,
        decreases h - y,
    {
        proof {
            assert(row + w <= n) by (nonlinear_arith) requires row == y * w, y < h, n == w * h;
            assert(row >= w) by (nonlinear_arith) requires row == y * w, y >= 1;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(row as int, w as int, y as int, 0);
        }
        let pr = px[row - w];
        pred_px(px, row, pr, Ghost(gb), Ghost(gw), Ghost(img@), Ghost(px0), Ghost(target));
        let ty = ((y as u64) >> bits) as usize;
        proof {
            lemma_shr_div(y as u64, bits);
            crate::pix::lemma_tile_in(w as nat, h as nat, bits as nat, 0, y as nat);
            assert(ty * tw + tw <= img@.len()) by (nonlinear_arith)
                requires ty < div_round_up(h as nat, p2(bits as nat)), img@.len() == tw * div_round_up(h as nat, p2(bits as nat));
            assert(ty <= y) by (nonlinear_arith) requires ty == y as nat / p2(bits as nat), p2(bits as nat) >= 1;
            assert(ty * tw + tw <= 16384 * 16384 + 16384) by (nonlinear_arith) requires ty < 16384, tw <= 16384;
        }
        let trow = ty * tw;
        let mut tx: usize = 0;
        let mut x0: usize = 1;
        while tx < tw && x0 < w
            invariant
                2 <= bits <= 9, 1 <= w <= 16384, 1 <= h <= 16384, n == w * h, px@.len() == n, px0.len() == n,
                gb == bits, gw == w,
                tiles_wf(img@, bits as nat, w as nat, h as nat),
                t as nat == p2(bits as nat), tw as nat == div_round_up(w as nat, p2(bits as nat)), t == (1u64 << bits),
                4 <= t <= 512, 1 <= tw <= 16384,
                1 <= y < h, row == y * w, row + w <= n, pl@.len() == w + 4, n <= 0x1000_0000, ty as nat == y as nat / p2(bits as nat), trow == ty * tw,
                trow + tw <= img@.len(), trow + tw <= 16384 * 16384 + 16384, tx <= tw,
                1 <= x0 <= w, tx >= 1 && x0 < w ==> x0 == tx * t, tx == 0 ==> x0 == 1, tx >= 1 ==> x0 <= tx * t,
                forall|k: int| row + x0 <= k < n ==> #[trigger] px@[k] == px0[k],
                inv_predictor(gb, gw, img@, px0, px@.take(row + x0)) == target,
            decreases tw - tx,
        {
            let e = img[trow + tx];
            let mode = ((e >> 8u32) & 0xfu32) as i64;
            proof {
                assert((tx + 1) * t == tx * t + t) by (nonlinear_arith);
                assert((tx + 1) * t <= 16385 * 512) by (nonlinear_arith) requires tx < 16384, t <= 512;
            }
            let x1 = if (tx + 1) * t < w { (tx + 1) * t } else { w };
            proof {
                assert(mode == green(e) % 16) by (bit_vector) requires mode == ((e >> 8u32) & 0xfu32);
                assert forall|x: int| x0 <= x < x1 implies
                    #[trigger] green(tile(img@, gb, w as nat, x as nat, y as nat)) % 16 == mode by {
                    assert(x as nat / (t as nat) == tx) by (nonlinear_arith)
                        requires tx * t <= x < (tx + 1) * t, t >= 1, x >= 0;
                    assert(tile(img@, gb, w as nat, x as nat, y as nat) == e);
                }
            }
            match mode {
                1 => pred_run(1, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                2 => pred_run_up(2, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                3 => pred_run_up(3, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                4 => pred_run_up(4, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                5 => pred_run(5, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                6 => pred_run(6, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                7 => pred_run(7, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                8 => pred_run(8, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                9 => pred_run(9, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                10 => pred_run(10, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                11 => pred_run11(px, &mut pl, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                12 => pred_run(12, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                13 => pred_run(13, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                0 => pred_run_up(0, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
                _ => pred_run(mode, px, y, row, x0, x1, w, Ghost(gb), Ghost(img@), Ghost(px0), Ghost(target)),
            }
            tx = tx + 1;
            x0 = x1;
        }
        proof {
            // the tiles cover the row
            if x0 < w {
                assert(tx == tw);
                assert(tw * t >= w) by (nonlinear_arith)
                    requires tw == (w + t - 1) as nat / (t as nat), t >= 1, w >= 1;
                assert(false);
            }
        }
        proof { assert(row + w == (y + 1) * w) by (nonlinear_arith) requires row == y * w; }
        row = row + w;
        y = y + 1;
    }
    proof {
        assert(row == n) by (nonlinear_arith) requires row == y * w, y == h, n == w * h;
        assert(px@.take(n as int) =~= px@);
        assert(inv_predictor(gb, gw, img@, px0, px@) == px@);
    }
}

/// `color_index`: the index of pixel (x, y) in the bundled pixels `px`,
/// `iw` of them to a row.
#[inline(always)]
fn color_index_x(wb: u64, w: usize, h: usize, iw: usize, px: &Vec<u32>, x: usize, y: usize, rowin: usize) -> (r: usize)
    requires wb <= 3, 1 <= w <= 16384, 1 <= h <= 16384, x < w, y < h,
        iw as nat == div_round_up(w as nat, p2(wb as nat)), rowin == y * iw,
        px@.len() == div_round_up(w as nat, p2(wb as nat)) * h,
    ensures r as int == color_index(wb as nat, w as nat, px@, x as nat, y as nat), r < 256,
        (r as nat) < p2((8nat / p2(wb as nat)) as nat),
{
    let t: usize = (1u64 << wb) as usize;
    proof {
        lemma_shl1(wb);
        reveal_with_fuel(p2, 9);
        crate::pix::lemma_tile_in(w as nat, h as nat, wb as nat, x as nat, 0);
        assert(x / t < div_round_up(w as nat, p2(wb as nat)));
        lemma_shr_div(x as u64, wb);
    }
    let xq = ((x as u64) >> wb) as usize;
    proof {
        assert(iw <= w) by (nonlinear_arith) requires iw == (w + t - 1) as nat / (t as nat), t >= 1, w >= 1;
        assert(iw * h <= 16384 * 16384) by (nonlinear_arith) requires iw <= 16384, h <= 16384;
        assert(y * iw + xq < iw * h) by (nonlinear_arith) requires y < h, xq < iw;
        assert(iw * h == px@.len());
    }
    let c = vsimd::mem::get(px.as_slice(), rowin + xq);
    let g = ((c >> 8u32) & 0xffu32) as u64;
    proof { assert(g == green(px@[rowin + xq])); }
    if wb == 0 {
        proof { reveal_with_fuel(p2, 9); let one = p2(0); assert(one == 1);
            assert(8nat / one == 8) by (nonlinear_arith) requires one == 1; assert(p2(8) == 256);
            assert(g < 256) by (bit_vector) requires g == ((c >> 8u32) & 0xffu32) as u64; }
        return g as usize;
    }
    let nb: u64 = 8 >> wb;
    let xr: u64 = (x as u64) & ((t - 1) as u64);
    proof {
        assert(1 <= nb <= 4) by (bit_vector) requires nb == 8u64 >> wb, 1 <= wb <= 3;
        assert(t <= 8);
        assert(xr == (x as u64) % (t as u64)) by (bit_vector) requires xr == (x as u64) & ((t - 1) as u64), t == (1u64 << wb), wb <= 3;
        assert(xr * nb <= 32) by (nonlinear_arith) requires xr < t, t <= 8, nb <= 4;
    }
    let sh: u64 = xr * nb;
    proof { lemma_shl1(nb); vbits::bitspec::lemma_p2_pos(nb as nat); }
    let mask: u64 = (1u64 << nb) - 1;
    let r = (g >> sh) & mask;
    proof {
        assert(nb as nat == 8nat / p2(wb as nat)) by {
            assert(nb == 8u64 / (1u64 << wb)) by (bit_vector) requires nb == 8u64 >> wb, wb <= 3;
        }
        assert(sh < 8) by (nonlinear_arith) requires sh == xr * nb, xr < t, t == p2(wb as nat),
            nb == 8nat / p2(wb as nat), 1 <= wb <= 3, p2(1) == 2, p2(2) == 4, p2(3) == 8;
        lemma_shl1(sh);
        lemma_shl1(nb);
        vstd::bits::lemma_u64_shr_is_div(g, sh);
        vbits::prim_read::lemma_p2_eq_pow2(sh as nat);
        assert(mask == (1u64 << nb) - 1);
        assert(((g >> sh) & mask) == (g >> sh) % (1u64 << nb)) by (bit_vector)
            requires mask == (1u64 << nb) - 1, nb <= 4;
        assert((g >> sh) % (1u64 << nb) < (1u64 << nb));
        assert(nb <= 4);
        vbits::prim_read::lemma_p2_mono(nb as nat, 4);
    }
    r as usize
}

/// `inv_color_indexing`: the image `w` x `h` from its bundled pixels, a row
/// at a time.
pub fn inv_color_indexing_x(wb: u64, w: usize, h: usize, pal: &Vec<u32>, px: &Vec<u32>) -> (r: Vec<u32>)
    requires wb <= 3, 1 <= w <= 16384, 1 <= h <= 16384,
        px@.len() == div_round_up(w as nat, p2(wb as nat)) * h,
        pal@.len() == p2((8nat / p2(wb as nat)) as nat),
    ensures r@ == inv_color_indexing(wb as nat, w as nat, h as nat, pal@, px@),
{
    let ghost f = inv_color_indexing(wb as nat, w as nat, h as nat, pal@, px@);
    proof { assert(w * h <= 0x1000_0000) by (nonlinear_arith) requires w <= 16384, h <= 16384; }
    let n = w * h;
    let t: usize = (1u64 << wb) as usize;
    proof {
        lemma_shl1(wb);
        reveal_with_fuel(p2, 9);
        assert(t <= 8);
    }
    let iw = (((w + t - 1) as u64) >> wb) as usize;
    proof {
        lemma_shr_div((w + t - 1) as u64, wb);
        assert((w + t - 1) as nat / (t as nat) <= w) by (nonlinear_arith) requires w >= 1, t >= 1;
    }
    let mut out: Vec<u32> = vec![0u32; n];
    let mut y: usize = 0;
    let mut rowin: usize = 0;
    proof { assert(iw * h <= 16384 * 16384) by (nonlinear_arith) requires iw <= 16384, h <= 16384; }
    while y < h
        invariant
            n == w * h, wb <= 3, 1 <= w <= 16384, 1 <= h <= 16384,
            px@.len() == div_round_up(w as nat, p2(wb as nat)) * h,
            pal@.len() == p2((8nat / p2(wb as nat)) as nat),
            iw as nat == div_round_up(w as nat, p2(wb as nat)), iw <= w,
            f == inv_color_indexing(wb as nat, w as nat, h as nat, pal@, px@), f.len() == n,
            p2(0) == 1, p2(1) == 2, p2(2) == 4, p2(3) == 8, p2(8) == 256,
            y <= h, rowin == y * iw, out@.len() == n, rowin <= iw * h, iw * h <= 16384 * 16384,
            forall|k: int| 0 <= k < y * w ==> #[trigger] out@[k] == f[k],
        decreases h - y,
    {
        let mut x: usize = 0;
        proof { assert(y * w + w <= n) by (nonlinear_arith) requires y < h, n == w * h; }
        while x < w
            invariant
                n == w * h, wb <= 3, 1 <= w <= 16384, 1 <= h <= 16384,
                px@.len() == div_round_up(w as nat, p2(wb as nat)) * h,
                pal@.len() == p2((8nat / p2(wb as nat)) as nat),
                iw as nat == div_round_up(w as nat, p2(wb as nat)), iw <= w,
                f == inv_color_indexing(wb as nat, w as nat, h as nat, pal@, px@), f.len() == n,
                p2(0) == 1, p2(1) == 2, p2(2) == 4, p2(3) == 8, p2(8) == 256,
                y < h, rowin == y * iw, x <= w, out@.len() == n, y * w + w <= n,
                forall|k: int| 0 <= k < y * w + x ==> #[trigger] out@[k] == f[k],
            decreases w - x,
        {
            let k = color_index_x(wb, w, h, iw, px, x, y, rowin);
            proof {
                let i = y * w + x;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(i as int, w as int, y as int, x as int);
                assert(f[i as int] == pal@[color_index(wb as nat, w as nat, px@, x as nat, y as nat)]);
            }
            vsimd::mem::vset(&mut out, y * w + x, vsimd::mem::get(pal.as_slice(), k));
            x = x + 1;
        }
        proof {
            assert(y * w + w == (y + 1) * w) by (nonlinear_arith);
            assert(rowin + iw == (y + 1) * iw) by (nonlinear_arith) requires rowin == y * iw;
            assert((y + 1) * iw <= iw * h) by (nonlinear_arith) requires y < h;
        }
        y = y + 1;
        rowin = rowin + iw;
    }
    proof {
        assert(y * w == n) by (nonlinear_arith) requires y == h, n == w * h;
        assert(out@ =~= f);
    }
    out
}

} // verus!
