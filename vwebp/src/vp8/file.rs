//! Lossy WebP files, verified: `webp_lossy_x` computes `fspec::webp_lossy`.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::lsb::lbits;
use crate::cspec::*;
use crate::riff::*;
use crate::code::*;
use crate::img::*;
use crate::tr::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::spec::{read_transforms, spatially_coded_image, inverses, green};
use super::fspec::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use super::spec::vp8;
use super::spec::Frame;
use super::dec::*;

verus! {

pub enum LossyX {
    NotLossy,
    Image { frame: FrameX, alpha: Option<Vec<u8>>, lib: bool },
}

/// The file's image is `l`: the frame's buffers hold its frame, and the alpha.
pub open spec fn lossy_is(x: &LossyX, l: Lossy) -> bool {
    match (x, l) {
        (LossyX::NotLossy, Lossy::NotLossy) => true,
        (LossyX::Image { frame, alpha, lib }, Lossy::Image { frame: f, alpha: a, lib: l2 }) =>
            frame.is(f) && *lib == l2 && match (alpha, a) {
                (None, None) => true,
                (Some(v), Some(s)) => v@ == s,
                _ => false,
            },
        _ => false,
    }
}

/// `last_alph`, as the payload's bounds in `body`.
pub fn last_alph_x(body: &[u8], i0: usize, stop: usize) -> (r: Option<(usize, usize)>)
    requires body@.len() <= 0xffff_ffff,
    ensures match last_alph(body@, i0 as int, stop as int, None) {
        None => r.is_none(),
        Some(d) => r.is_some() && r.unwrap().0 <= r.unwrap().1 <= body@.len() && body@.subrange(r.unwrap().0 as int, r.unwrap().1 as int) == d,
    },
{
    let ghost target = last_alph(body@, i0 as int, stop as int, None);
    let mut i = i0;
    let mut acc: Option<(usize, usize)> = None;
    loop
        invariant
            body@.len() <= 0xffff_ffff, target == last_alph(body@, i0 as int, stop as int, None),
            match acc { None => true, Some((a, e)) => a <= e <= body@.len() },
            last_alph(body@, i as int, stop as int, match acc { None => None, Some((a, e)) => Some(body@.subrange(a as int, e as int)) }) == target,
        decreases stop - i,
    {
        if i >= stop {
            return acc;
        }
        let (cc, a, e) = match chunk_at_x(body, i) { None => return acc, Some(x) => x };
        proof { lemma_fourccs(); }
        if cc == 0x4850_4c41 {
            acc = Some((a, e));
        }
        let pe = if e % 2 == 1 { e + 1 } else { e };
        if pe <= i || pe > stop {
            return acc;
        }
        i = pe;
    }
}

/// `unfilter`, of a `w` x `h` plane.
fn unfilter_x(method: u8, x: &Vec<u8>, w: usize, h: usize) -> (r: Vec<u8>)
    requires method <= 3, 1 <= w <= 16384, 1 <= h <= 16384, x@.len() == w * h,
    ensures r@ == unfilter(method as nat, x@, w as nat, Seq::empty()), r@.len() == w * h,
{
    proof { assert(w * h <= 16384 * 16384) by (nonlinear_arith) requires w <= 16384, h <= 16384; }
    let n = w * h;
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    let mut c: usize = 0;
    let mut row: usize = 0;
    while i < n
        invariant
            method <= 3, 1 <= w <= 16384, 1 <= h <= 16384, n == w * h, x@.len() == n, i <= n, out@.len() == i,
            c < w, i == row * w + c,
            unfilter(method as nat, x@, w as nat, out@) == unfilter(method as nat, x@, w as nat, Seq::empty()),
        decreases n - i,
    {
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(i as int, w as int, row as int, c as int);
            if row > 0 { assert(i >= w + c) by (nonlinear_arith) requires i == row * w + c, row >= 1; }
        }
        let pred: i32 = if method == 0 || i == 0 { 0 }
            else if c == 0 { out[i - w] as i32 }
            else if row == 0 { out[i - 1] as i32 }
            else if method == 1 { out[i - 1] as i32 }
            else if method == 2 { out[i - w] as i32 }
            else {
                let g = out[i - 1] as i32 + out[i - w] as i32 - out[i - w - 1] as i32;
                if g < 0 { 0 } else if g > 255 { 255 } else { g }
            };
        out.push(((pred + x[i] as i32) % 256) as u8);
        let ghost (i0, c0, r0) = (i, c, row);
        i = i + 1;
        if c + 1 == w { c = 0; row = row + 1; } else { c = c + 1; }
        proof {
            if c0 + 1 == w {
                assert(i == row * w + c) by (nonlinear_arith) requires i == i0 + 1, i0 == r0 * w + c0, c0 + 1 == w, row == r0 + 1, c == 0;
            }
        }
    }
    out
}

/// `alph`.
fn alph_x(d: &[u8], w: usize, h: usize) -> (r: Option<(Vec<u8>, bool)>)
    requires d@.len() <= 0xffff_ffff, 1 <= w <= 16384, 1 <= h <= 16384,
    ensures match alph(d@, w as nat, h as nat) {
        None => r.is_none(),
        Some((a, l)) => r.is_some() && r.unwrap().0@ == a && r.unwrap().1 == l,
    },
{
    if d.len() < 1 {
        return None;
    }
    let hdr = d[0];
    let method = hdr % 4;
    let filter = (hdr / 4) % 4;
    let pre = (hdr / 16) % 4;
    let rsv = hdr / 64;
    proof { assert(w * h <= 16384 * 16384) by (nonlinear_arith) requires w <= 16384, h <= 16384; }
    let (x, st): (Vec<u8>, bool) = if method == 0 {
        if d.len() - 1 < w * h {
            return None;
        }
        let mut v: Vec<u8> = Vec::with_capacity(w * h);
        let mut k: usize = 0;
        while k < w * h
            invariant k <= w * h, d@.len() >= 1 + w * h, v@.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] v@[j] == d@[1 + j],
            decreases w * h - k,
        {
            v.push(d[1 + k]);
            k = k + 1;
        }
        proof { assert(v@ =~= d@.subrange(1, (1 + w * h) as int)); }
        (v, true)
    } else if method == 1 {
        let bs = vstd::slice::slice_subrange(d, 1, d.len());
        let (ts, dw, p, st) = match read_transforms_x(bs, 0, w, h) { None => return None, Some(t) => t };
        let (px, _q, st2) = match spatially_coded_image_x(bs, p, dw, h) { None => return None, Some(t) => t };
        let full = inverses_x(&ts, w, h, px);
        let n = w * h;
        let mut g: Vec<u8> = Vec::with_capacity(n);
        let mut k: usize = 0;
        while k < n
            invariant n == w * h, k <= n, full@.len() == n, g@.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] g@[j] == green(full@[j]) as u8,
            decreases n - k,
        {
            let c = full[k];
            let v32 = (c >> 8u32) & 0xffu32;
            proof { assert(v32 < 256) by (bit_vector) requires v32 == (c >> 8u32) & 0xffu32; }
            let v = v32 as u8;
            g.push(v);
            k = k + 1;
        }
        proof { assert(g@ =~= Seq::new((w * h) as nat, |k: int| green(full@[k]) as u8)); }
        (g, st && st2)
    } else {
        return None;
    };
    let out = unfilter_x(filter, &x, w, h);
    Some((out, rsv == 0 && pre <= 1 && st))
}

pub open spec fn opt(ach: Option<&[u8]>) -> Option<Seq<u8>> { match ach { None => None, Some(d) => Some(d@) } }

/// `lossy_image`.
pub fn lossy_image_x(frame: &[u8], ach: Option<&[u8]>, cw: u64, ch: u64, lib: bool, max_pixels: u64) -> (r: Result<LossyX, Error>)
    requires match ach { None => true, Some(d) => d@.len() <= 0xffff_ffff },
    ensures match r {
        Ok(x) => lossy_image(frame@, opt(ach), cw as nat, ch as nat, lib) is Some
            && lossy_is(&x, lossy_image(frame@, opt(ach), cw as nat, ch as nat, lib).unwrap()),
        Err(Error::Bad) => lossy_image(frame@, opt(ach), cw as nat, ch as nat, lib) is None,
        Err(Error::TooBig) => true,
    },
{
    let f = match vp8_x(frame, max_pixels) { Err(e) => return Err(e), Ok(f) => f };
    if cw != 0 && (f.w as u64 != cw || f.h as u64 != ch) {
        return Err(Error::Bad);
    }
    match ach {
        None => Ok(LossyX::Image { frame: f, alpha: None, lib }),
        Some(d) => match alph_x(d, f.w, f.h) {
            None => Err(Error::Bad),
            Some((a, al)) => Ok(LossyX::Image { frame: f, alpha: Some(a), lib: lib && al }),
        },
    }
}

/// `lossy_extended`, for a VP8X payload at `body[a..e]`.
fn lossy_extended_x(body: &[u8], a: usize, e: usize, max_pixels: u64) -> (r: Result<LossyX, Error>)
    requires body@.len() <= 0xffff_ffff, a + 10 <= e <= body@.len(),
    ensures match r {
        Ok(x) => lossy_extended(body@, a as int, e as int) is Some && lossy_is(&x, lossy_extended(body@, a as int, e as int).unwrap()),
        Err(Error::Bad) => lossy_extended(body@, a as int, e as int) is None,
        Err(Error::TooBig) => true,
    },
{
    proof { lemma_fourccs(); }
    let flags = body[a];
    let cw = le24_x(body, a + 4) + 1;
    let ch = le24_x(body, a + 7) + 1;
    let lib_x = e - a == 10;
    proof { assert(cw * ch <= 0x100_0000 * 0x100_0000) by (nonlinear_arith) requires cw <= 0x100_0000, ch <= 0x100_0000; }
    if cw * ch > 0xffff_ffff {
        return Err(Error::Bad);
    }
    if flags & 2 == 2 {
        return Ok(LossyX::NotLossy);
    }
    let pe = if e % 2 == 1 { e + 1 } else { e };
    let (cc2, a2, e2) = match find_image_x(body, pe) { None => return Err(Error::Bad), Some(x) => x };
    if cc2 != 0x2038_5056 {
        return Ok(LossyX::NotLossy);
    }
    let frame = vstd::slice::slice_subrange(body, a2, e2);
    let pe2 = if e2 % 2 == 1 { e2 + 1 } else { e2 };
    proof { assert(a2 >= 8) by { reveal_find_image_start(body@, pe as int); } }
    let al = last_alph_x(body, pe, a2 - 8);
    let ach: Option<&[u8]> = match al { None => None, Some((x0, x1)) => Some(vstd::slice::slice_subrange(body, x0, x1)) };
    lossy_image_x(frame, ach, cw, ch, lib_x && pe2 <= body.len(), max_pixels)
}

/// An image chunk's payload starts after its header.
pub proof fn reveal_find_image_start(body: Seq<u8>, i: int)
    requires find_image(body, i) is Some,
    ensures find_image(body, i).unwrap().1 >= 8,
    decreases body.len() - i,
{
    match chunk_at(body, i) {
        None => {},
        Some((cc, a, e)) => {
            if !(cc == cc_vp8l() || cc == cc_vp8()) && !(padded(e) > body.len() || padded(e) <= i) {
                reveal_find_image_start(body, padded(e));
            }
        },
    }
}

/// `lossy_body`.
fn lossy_body_x(body: &[u8], max_pixels: u64) -> (r: Result<LossyX, Error>)
    requires body@.len() <= 0xffff_ffff,
    ensures match r {
        Ok(x) => lossy_body(body@) is Some && lossy_is(&x, lossy_body(body@).unwrap()),
        Err(Error::Bad) => lossy_body(body@) is None,
        Err(Error::TooBig) => true,
    },
{
    proof { lemma_fourccs(); }
    let (cc, a, e) = match chunk_at_x(body, 0) { None => return Err(Error::Bad), Some(x) => x };
    if cc == 0x4c38_5056 {
        Ok(LossyX::NotLossy)
    } else if cc == 0x2038_5056 {
        lossy_image_x(vstd::slice::slice_subrange(body, a, e), None, 0, 0, true, max_pixels)
    } else if cc != 0x5838_5056 || e - a < 10 {
        Err(Error::Bad)
    } else {
        lossy_extended_x(body, a, e, max_pixels)
    }
}

/// Decode a lossy WebP file (`webp_lossy`): its frame and alpha, or that
/// it is not a lossy image, refusing a frame of more than `max_pixels`.
pub fn webp_lossy_x(f: &[u8], max_pixels: u64) -> (r: Result<LossyX, Error>)
    ensures match r {
        Ok(x) => webp_lossy(f@) is Some && lossy_is(&x, webp_lossy(f@).unwrap()),
        Err(Error::Bad) => webp_lossy(f@) is None,
        Err(Error::TooBig) => true,
    },
{
    proof { lemma_fourccs(); }
    if f.len() < 12 || le32_x(f, 0) != 0x4646_4952 || le32_x(f, 8) != 0x5042_4557 {
        return Err(Error::Bad);
    }
    let rs = le32_x(f, 4);
    if rs < 12 || rs > 0xffff_fff6 || 8 + rs > f.len() as u64 {
        return Err(Error::Bad);
    }
    let body = vstd::slice::slice_subrange(f, 12, 8 + rs as usize);
    lossy_body_x(body, max_pixels)
}

} // verus!
