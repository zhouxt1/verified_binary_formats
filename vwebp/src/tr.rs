//! Reading the transforms (RFC 9649 3.5, 3.8.2), proved to compute
//! `read_transforms`, and applying their inverses, last one first.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
use vbits::lsb::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::getbits;
use crate::code::*;
use crate::img::*;
use crate::inv::*;
use crate::spec::*;

verus! {

pub enum TrX {
    Predictor { bits: u64, w: usize, img: Vec<u32> },
    Color { bits: u64, w: usize, img: Vec<u32> },
    SubtractGreen,
    ColorIndexing { wb: u64, w: usize, pal: Vec<u32> },
}

pub open spec fn tr_view(t: &TrX) -> Tr {
    match t {
        TrX::Predictor { bits, w, img } => Tr::Predictor { bits: *bits as nat, w: *w as nat, img: img@ },
        TrX::Color { bits, w, img } => Tr::Color { bits: *bits as nat, w: *w as nat, img: img@ },
        TrX::SubtractGreen => Tr::SubtractGreen,
        TrX::ColorIndexing { wb, w, pal } => Tr::ColorIndexing { wb: *wb as nat, w: *w as nat, pal: pal@ },
    }
}

pub open spec fn trs_view(v: Seq<TrX>) -> Seq<Tr> {
    Seq::new(v.len(), |k: int| tr_view(&v[k]))
}

/// The image's width after transform `t`, from `w` before it.
pub open spec fn out_w(t: &TrX, w: nat) -> nat {
    match t {
        TrX::ColorIndexing { wb, .. } => div_round_up(w, p2(*wb as nat)),
        _ => w,
    }
}

/// The width before the `k`-th transform, from `w0` before the first.
pub open spec fn wid(v: Seq<TrX>, w0: nat, k: int) -> nat
    decreases k,
{
    if k <= 0 { w0 } else { out_w(&v[k - 1], wid(v, w0, k - 1)) }
}

/// What the inverse of `t` needs, for an image `w` (before `t`) by `h`.
pub open spec fn tr_ok(t: &TrX, w: nat, h: nat) -> bool {
    &&& 1 <= w <= 16384
    &&& match t {
        TrX::Predictor { bits, w: tw, img } => 2 <= *bits <= 9 && *tw as nat == w && tiles_wf(img@, *bits as nat, w, h),
        TrX::Color { bits, w: tw, img } => 2 <= *bits <= 9 && *tw as nat == w && tiles_wf(img@, *bits as nat, w, h),
        TrX::SubtractGreen => true,
        TrX::ColorIndexing { wb, w: tw, pal } => *wb <= 3 && *tw as nat == w && pal@.len() == p2((8nat / p2(*wb as nat)) as nat),
    }
}

pub open spec fn trs_wf(v: Seq<TrX>, w0: nat, h: nat) -> bool {
    forall|k: int| 0 <= k < v.len() ==> #[trigger] tr_ok(&v[k], wid(v, w0, k), h)
}

proof fn lemma_wid_push(v: Seq<TrX>, x: TrX, w0: nat, k: int)
    requires 0 <= k <= v.len(),
    ensures wid(v.push(x), w0, k) == wid(v, w0, k),
    decreases k,
{
    if k > 0 {
        lemma_wid_push(v, x, w0, k - 1);
        assert(v.push(x)[k - 1] == v[k - 1]);
    }
}

proof fn lemma_seen_push(ts: Seq<Tr>, x: Tr, ty: nat)
    ensures seen(ts.push(x), ty) == (seen(ts, ty) || tr_type(x) == ty),
{
    if seen(ts, ty) {
        let k = choose|k: int| 0 <= k < ts.len() && tr_type(#[trigger] ts[k]) == ty;
        assert(ts.push(x)[k] == ts[k]);
    }
    if tr_type(x) == ty {
        assert(ts.push(x)[ts.len() as int] == x);
    }
    if seen(ts.push(x), ty) {
        let k = choose|k: int| 0 <= k < ts.push(x).len() && tr_type(#[trigger] ts.push(x)[k]) == ty;
        if k < ts.len() { assert(ts.push(x)[k] == ts[k]); }
    }
}

/// The color table: `palette`.
fn palette_x(deltas: &Vec<u32>, wb: u64) -> (r: Vec<u32>)
    requires wb <= 3, deltas@.len() >= 1,
    ensures r@ == palette(deltas@, wb as nat), r@.len() == p2((8nat / p2(wb as nat)) as nat),
{
    let nb: u64 = 8 >> wb;
    proof {
        reveal_with_fuel(p2, 9);
        assert(nb as nat == 8nat / p2(wb as nat)) by {
            assert(nb == 8u64 / (1u64 << wb)) by (bit_vector) requires nb == 8u64 >> wb, wb <= 3;
            lemma_shl1(wb);
        }
        assert(nb <= 8) by (bit_vector) requires nb == 8u64 >> wb;
        lemma_shl1(nb);
        vbits::prim_read::lemma_p2_mono(nb as nat, 8);
    }
    let size = (1u64 << nb) as usize;
    let n = deltas.len();
    let mut pal: Vec<u32> = Vec::with_capacity(size);
    let mut prev: u32 = 0;
    let mut k: usize = 0;
    while k < size
        invariant
            size as nat == p2(nb as nat), nb as nat == 8nat / p2(wb as nat), n == deltas@.len(), n >= 1,
            k <= size, pal@.len() == k,
            k >= 1 && k <= n ==> prev == palette_at(deltas@, k - 1),
            forall|j: int| 0 <= j < k ==> #[trigger] pal@[j] == palette(deltas@, wb as nat)[j],
        decreases size - k,
    {
        if k < n {
            if k == 0 {
                prev = deltas[0];
            } else {
                prev = add_pixels_x(prev, deltas[k]);
            }
            pal.push(prev);
        } else {
            pal.push(0);
        }
        k = k + 1;
    }
    proof { assert(pal@ =~= palette(deltas@, wb as nat)); }
    pal
}

/// Table 3.
fn width_bits_x(n: u64) -> (r: u64)
    ensures r as nat == width_bits(n as nat), r <= 3,
{
    if n > 16 { 0 } else if n > 4 { 1 } else if n > 2 { 2 } else { 3 }
}

/// The transforms: `read_transforms` from none, for an image `w` x `h`.
pub fn read_transforms_x(buf: &[u8], pos: usize, w: usize, h: usize) -> (r: Option<(Vec<TrX>, usize, usize, bool)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), 1 <= w <= 16384, 1 <= h <= 16384,
    ensures
        match r {
            Some((v, dw, q, st)) => read_transforms(lbits(buf@), pos as int, w as nat, h as nat, Seq::empty(), true)
                    == Some((trs_view(v@), dw as nat, q as int, st))
                && trs_wf(v@, w as nat, h as nat) && dw as nat == wid(v@, w as nat, v@.len() as int)
                && 1 <= dw <= 16384 && q <= 8 * buf.len(),
            None => read_transforms(lbits(buf@), pos as int, w as nat, h as nat, Seq::empty(), true) is None,
        },
{
    let ghost b = lbits(buf@);
    let ghost target = read_transforms(b, pos as int, w as nat, h as nat, Seq::empty(), true);
    let mut v: Vec<TrX> = Vec::new();
    let mut seen_x: [bool; 4] = [false; 4];
    let mut cw = w;
    let mut p = pos;
    let mut st = true;
    proof { assert(trs_view(v@) =~= Seq::<Tr>::empty()); }
    loop
        invariant
            buf_ok(buf@), p <= 8 * buf.len(), b == lbits(buf@), 1 <= w <= 16384, 1 <= h <= 16384,
            1 <= cw <= 16384, v@.len() <= 4,
            read_transforms(b, p as int, cw as nat, h as nat, trs_view(v@), st) == target,
            target == read_transforms(lbits(buf@), pos as int, w as nat, h as nat, Seq::empty(), true),
            trs_wf(v@, w as nat, h as nat), cw as nat == wid(v@, w as nat, v@.len() as int),
            forall|t: int| 0 <= t < 4 ==> #[trigger] seen_x[t] == seen(trs_view(v@), t as nat),
        decreases 4 - v@.len(),
    {
        proof { assert(trs_view(v@).len() == v@.len()); }
        let more = match getbits_x(buf, p, 1) { None => return None, Some(x) => x };
        if more == 0 {
            return Some((v, cw, p + 1, st));
        }
        if v.len() >= 4 {
            return None;
        }
        let ty = match getbits_x(buf, p + 1, 2) { None => return None, Some(x) => x };
        proof { lemma_p2_consts(); }
        if seen_x[ty as usize] {
            return None;
        }
        let ghost v0 = v@;
        let t: TrX;
        let mut nw = cw;
        if ty == 2 {
            t = TrX::SubtractGreen;
            p = p + 3;
        } else if ty == 3 {
            let n1 = match getbits_x(buf, p + 3, 8) { None => return None, Some(x) => x };
            let n = n1 + 1;
            let wb = width_bits_x(n);
            let (deltas, q, st2) = match entropy_coded_image_x(buf, p + 11, n as usize, 1) { None => return None, Some(x) => x };
            let pal = palette_x(&deltas, wb);
            nw = div_round_up_x(cw, wb);
            t = TrX::ColorIndexing { wb, w: cw, pal };
            p = q;
            st = st && st2;
        } else {
            let sb = match getbits_x(buf, p + 3, 3) { None => return None, Some(x) => x };
            let bits = sb + 2;
            let tw = div_round_up_x(cw, bits);
            let th = div_round_up_x(h, bits);
            let (img, q, st2) = match entropy_coded_image_x(buf, p + 6, tw, th) { None => return None, Some(x) => x };
            t = if ty == 0 { TrX::Predictor { bits, w: cw, img } } else { TrX::Color { bits, w: cw, img } };
            p = q;
            st = st && st2;
        }
        v.push(t);
        proof {
            assert(trs_view(v@) =~= trs_view(v0).push(tr_view(&t)));
            assert forall|u: int| 0 <= u < 4 implies #[trigger] seen_x[u] == seen(trs_view(v0), u as nat) by {}
            lemma_wid_push(v0, t, w as nat, v0.len() as int);
            assert forall|k: int| 0 <= k < v@.len() implies #[trigger] tr_ok(&v@[k], wid(v@, w as nat, k), h as nat) by {
                lemma_wid_push(v0, t, w as nat, k);
                if k < v0.len() { assert(v@[k] == v0[k]); }
            }
            assert(wid(v@, w as nat, v@.len() as int) == out_w(&t, wid(v0, w as nat, v0.len() as int)));
        }
        let ghost seen_old = seen_x;
        seen_x[ty as usize] = true;
        proof {
            assert forall|u: int| 0 <= u < 4 implies #[trigger] seen_x[u] == seen(trs_view(v@), u as nat) by {
                lemma_seen_push(trs_view(v0), tr_view(&t), u as nat);
            }
        }
        cw = nw;
    }
}

/// The inverses of all the transforms, last one first: `inverses`, from
/// the image data `dw` wide.
pub fn inverses_x(v: &Vec<TrX>, w0: usize, h: usize, px: Vec<u32>) -> (r: Vec<u32>)
    requires 1 <= w0 <= 16384, 1 <= h <= 16384, trs_wf(v@, w0 as nat, h as nat),
        px@.len() == wid(v@, w0 as nat, v@.len() as int) * h,
    ensures r@ == inverses(trs_view(v@), v@.len() as int, h as nat, px@), r@.len() == w0 * h,
{
    let ghost ts = trs_view(v@);
    let ghost target = inverses(ts, v@.len() as int, h as nat, px@);
    let mut k = v.len();
    let mut cur = px;
    while k > 0
        invariant
            1 <= w0 <= 16384, 1 <= h <= 16384, trs_wf(v@, w0 as nat, h as nat), ts == trs_view(v@),
            k <= v@.len(), cur@.len() == wid(v@, w0 as nat, k as int) * h,
            inverses(ts, k as int, h as nat, cur@) == target,
            target == inverses(trs_view(v@), v@.len() as int, h as nat, px@),
        decreases k,
    {
        let t = &v[k - 1];
        let ghost wk = wid(v@, w0 as nat, k - 1);
        let ghost pre = cur@;
        proof {
            assert(tr_ok(&v@[k - 1], wk, h as nat));
            assert(ts[k - 1] == tr_view(t));
        }
        match t {
            TrX::Predictor { bits, w, img } => inv_predictor_x(*bits, *w, h, img, &mut cur),
            TrX::Color { bits, w, img } => inv_color_x(*bits, *w, h, img, &mut cur),
            TrX::SubtractGreen => inv_subtract_green_x(&mut cur),
            TrX::ColorIndexing { wb, w, pal } => {
                cur = inv_color_indexing_x(*wb, *w, h, pal, &cur);
            }
        }
        proof {
            assert(cur@ == inverse(ts[k - 1], h as nat, pre));
            assert(cur@.len() == wk * h);
        }
        k = k - 1;
    }
    cur
}

} // verus!
