//! Entropy-coded images and the spatially-coded image (RFC 9649 3.6.2.3,
//! 3.7.2.2, 3.8.3), proved to compute their spec functions.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
use vbits::lsb::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::getbits;
use crate::code::*;
use crate::pix::*;
use crate::spec::*;

verus! {

/// `read_cache_bits`.
pub fn read_cache_bits_x(buf: &[u8], pos: usize) -> (r: Option<(u64, usize)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(),
    ensures
        match r {
            Some((cb, q)) => read_cache_bits(lbits(buf@), pos as int) == Some((cb as nat, q as int))
                && cb <= 11 && q <= 8 * buf.len(),
            None => read_cache_bits(lbits(buf@), pos as int) is None,
        },
{
    let x = match getbits_x(buf, pos, 1) { None => return None, Some(x) => x };
    if x == 0 {
        return Some((0, pos + 1));
    }
    let cb = match getbits_x(buf, pos + 1, 4) { None => return None, Some(v) => v };
    if 1 <= cb && cb <= 11 { Some((cb, pos + 5)) } else { None }
}

/// `div_round_up(n, 2^bits)`.
pub fn div_round_up_x(n: usize, bits: u64) -> (r: usize)
    requires n <= 16384, bits <= 9,
    ensures r as nat == div_round_up(n as nat, p2(bits as nat)), r <= n + 1, n >= 1 ==> 1 <= r <= n,
{
    proof { lemma_shl1(bits); vbits::prim_read::lemma_p2_mono(bits as nat, 9); vbits::bitspec::lemma_p2_pos(bits as nat); }
    let t = (1u64 << bits) as usize;
    proof {
        assert(p2(9) == 512) by { reveal_with_fuel(p2, 10); }
        assert((n + t - 1) / (t as int) <= n + 1) by (nonlinear_arith) requires t >= 1, n >= 0;
        assert(n >= 1 ==> (n + t - 1) / (t as int) <= n) by (nonlinear_arith) requires t >= 1;
        assert(n >= 1 ==> (n + t - 1) / (t as int) >= 1) by (nonlinear_arith) requires t >= 1;
    }
    (n + t - 1) / t
}

/// An entropy-coded image of `w` x `h`: `entropy_coded_image`.
pub fn entropy_coded_image_x(buf: &[u8], pos: usize, w: usize, h: usize) -> (r: Option<(Vec<u32>, usize, bool)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), 1 <= w <= 16384, 1 <= h <= 16384,
    ensures
        match r {
            Some((px, q, st)) => entropy_coded_image(lbits(buf@), pos as int, w as nat, h as nat) == Some((px@, q as int, st))
                && px@.len() == w * h && q <= 8 * buf.len(),
            None => entropy_coded_image(lbits(buf@), pos as int, w as nat, h as nat) is None,
        },
{
    let (cb, q) = match read_cache_bits_x(buf, pos) { None => return None, Some(x) => x };
    let (g, q2, st) = match read_group_x(buf, q, cb) { None => return None, Some(x) => x };
    let ghost gv = codes_view(g@);
    let gs = vec![g];
    let m = MetaX::One;
    proof {
        assert(groups_view(gs@) =~= seq![gv]);
        assert(gs_wf(gs@, cb as nat));
    }
    match decode_pixels_x(buf, q2, w, h, cb, &gs, &m) {
        None => None,
        Some((px, q3)) => Some((px, q3, st)),
    }
}

/// `max_meta` of a whole entropy image, and that it bounds every meta code.
fn max_meta_x(img: &Vec<u32>) -> (r: usize)
    ensures
        r as int == max_meta(img@, img@.len() as int), r <= 0xffff,
        forall|k: int| 0 <= k < img@.len() ==> #[trigger] meta_code(img@[k]) <= r,
{
    let n = img.len();
    let mut m: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            n == img@.len(), i <= n, m as int == max_meta(img@, i as int), m <= 0xffff,
            forall|k: int| 0 <= k < i ==> #[trigger] meta_code(img@[k]) <= m,
        decreases n - i,
    {
        let c = ((img[i] >> 8u32) & 0xffffu32) as usize;
        proof {
            let x = img@[i as int];
            assert(((x >> 8u32) & 0xffffu32) <= 0xffff) by (bit_vector);
        }
        if c > m {
            m = c;
        }
        i = i + 1;
    }
    m
}

/// The meta prefix codes of `spatially_coded_image`, after its use_meta bit.
pub open spec fn meta_hdr(b: Seq<bool>, q: int, w: nat, h: nat, use_meta: nat) -> Option<(Meta, nat, int, bool)> {
    if use_meta == 0 {
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
    }
}

fn meta_hdr_x(buf: &[u8], q: usize, w: usize, h: usize, use_meta: u64) -> (r: Option<(MetaX, usize, usize, bool)>)
    requires buf_ok(buf@), q + 1 <= 8 * buf.len(), 1 <= w <= 16384, 1 <= h <= 16384,
    ensures
        match r {
            Some((m, ng, q2, st)) => meta_hdr(lbits(buf@), q as int, w as nat, h as nat, use_meta as nat)
                    == Some((meta_view(&m), ng as nat, q2 as int, st))
                && meta_wf(&m, w as nat, h as nat, ng as nat) && q2 <= 8 * buf.len() && ng <= 0x10000,
            None => meta_hdr(lbits(buf@), q as int, w as nat, h as nat, use_meta as nat) is None,
        },
{
    if use_meta == 0 {
        return Some((MetaX::One, 1usize, q + 1, true));
    }
    let pb = match getbits_x(buf, q + 1, 3) { None => return None, Some(x) => x };
    proof { lemma_p2_consts(); }
    let bits = pb + 2;
    let ew = div_round_up_x(w, bits);
    let eh = div_round_up_x(h, bits);
    let (img, q2, st) = match entropy_coded_image_x(buf, q + 4, ew, eh) { None => return None, Some(x) => x };
    let mx = max_meta_x(&img);
    proof {
        assert forall|k: int| 0 <= k < img@.len() implies #[trigger] meta_code(img@[k]) < mx + 1 by {}
    }
    Some((MetaX::Tiles { bits, ew, img }, mx + 1, q2, st))
}

/// The spatially-coded image of `w` x `h`: `spatially_coded_image`.
pub fn spatially_coded_image_x(buf: &[u8], pos: usize, w: usize, h: usize) -> (r: Option<(Vec<u32>, usize, bool)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), 1 <= w <= 16384, 1 <= h <= 16384,
    ensures
        match r {
            Some((px, q, st)) => spatially_coded_image(lbits(buf@), pos as int, w as nat, h as nat) == Some((px@, q as int, st))
                && px@.len() == w * h && q <= 8 * buf.len(),
            None => spatially_coded_image(lbits(buf@), pos as int, w as nat, h as nat) is None,
        },
{
    let (cb, q) = match read_cache_bits_x(buf, pos) { None => return None, Some(x) => x };
    let use_meta = match getbits_x(buf, q, 1) { None => return None, Some(x) => x };
    let (m, ngroups, q2, st) = match meta_hdr_x(buf, q, w, h, use_meta) { None => return None, Some(x) => x };
    let (gs, q3, st2) = match read_groups_x(buf, q2, cb, ngroups) { None => return None, Some(x) => x };
    match decode_pixels_x(buf, q3, w, h, cb, &gs, &m) {
        None => None,
        Some((px, q4)) => Some((px, q4, st && st2)),
    }
}

} // verus!
