//! The 16 x 16 and 8 x 8 intra predictors (DC, V, H, TM), a row at a time
//! in SSE2, proved to compute `spec::predict`.
use vstd::prelude::*;
use super::spec::*;
use super::plane::*;
#[cfg(verus_keep_ghost)]
use super::lfx::rows_w;
#[cfg(verus_keep_ghost)]
use vsimd::spec::{w16, sw16, clamp, lemma_add16_lane, lemma_set1_16_lane, lemma_zext_lane, lemma_w16_bounds};
#[cfg(verus_keep_ghost)]
use vsimd::x86::{v8, byte, lemma_byte};
use vsimd::x86::__m128i;
use vsimd::x86 as sx;

verus! {

/// The plane with row r's pixels x .. x + n set to `b`.
pub open spec fn set_rown(p: Plane, x: int, r: int, n: int, b: Seq<u8>) -> Plane {
    p.update(r, Seq::new(p[r].len(), |cc: int| if x <= cc < x + n { b[cc - x] } else { p[r][cc] }))
}

proof fn lemma_outside_n(w: nat, r: int, x: int, n: int, yy: int, xx: int)
    requires 0 <= xx < w, 0 <= yy, 0 <= r, 0 <= x, 0 <= n, x + n <= w, yy != r,
    ensures !(r * w + x <= yy * w + xx < r * w + x + n),
{
    if yy < r {
        assert(yy * w + xx < r * w) by (nonlinear_arith) requires yy < r, 0 <= xx < w;
    } else {
        assert(yy * w >= r * w + w) by (nonlinear_arith) requires yy > r, w >= 0;
    }
}

/// Bytes 0 .. n (n = 8 or 16) of `a` at pixels x .. x + n of row r.
fn put_row(v: &mut Vec<u8>, w: usize, x: usize, r: usize, n: usize, a: __m128i, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), r < pl.len(), n == 8 || n == 16, x + n <= w,
    ensures holds(final(v)@, w as nat, set_rown(pl, x as int, r as int, n as int, v8(a))),
{
    let len = v.len();
    proof { lemma_idx(w as nat, pl.len(), (x + n - 1) as int, r as int); }
    let off = r * w + x;
    if n == 16 { sx::storeu(v, off, a); } else { sx::storel(v, off, a); }
    proof {
        let p2 = set_rown(pl, x as int, r as int, n as int, v8(a));
        assert forall|yy: int, xx: int| 0 <= yy < p2.len() && 0 <= xx < w implies v@[yy * w + xx] == #[trigger] p2[yy][xx] by {
            lemma_idx(w as nat, pl.len(), xx, yy);
            if yy == r && x <= xx < x + n {
            } else if yy != r {
                lemma_outside_n(w as nat, r as int, x as int, n as int, yy, xx);
            }
        }
    }
}

/// The row above the block (`above`), bytes 0 .. n.
fn above_row(v: &Vec<u8>, w: usize, x: usize, y: usize, n: usize, Ghost(pl): Ghost<Plane>) -> (a: __m128i)
    requires holds(v@, w as nat, pl), n == 8 || n == 16, x + n <= w, y < pl.len(),
    ensures forall|c: int| 0 <= c < n ==> #[trigger] v8(a)[c] as int == above(pl, x as int, y as int, c),
{
    if y == 0 {
        sx::set1_epi8(127)
    } else {
        let len = v.len();
        proof { lemma_idx(w as nat, pl.len(), (x + n - 1) as int, (y - 1) as int); }
        let off = (y - 1) * w + x;
        let a = if n == 16 { sx::loadu(v.as_slice(), off) } else { sx::loadl(v.as_slice(), off) };
        proof {
            assert forall|c: int| 0 <= c < n implies #[trigger] v8(a)[c] as int == above(pl, x as int, y as int, c) by {
                lemma_idx(w as nat, pl.len(), x + c, (y - 1) as int);
            }
        }
        a
    }
}

/// TM_PRED's row: clamp255(left + above[c] - above_left), c < 16.
fn tm_row(a: __m128i, d: i32) -> (r: __m128i)
    requires -255 <= d <= 255,
    ensures forall|c: int| 0 <= c < 16 ==> #[trigger] v8(r)[c] == clamp255(v8(a)[c] as int + d as int),
{
    let z = sx::setzero();
    let lo = sx::unpacklo_epi8(a, z);
    let hi = sx::unpackhi_epi8(a, z);
    let du: u16 = if d < 0 { (d + 65536) as u16 } else { d as u16 };
    let dv = sx::set1_epi16(du);
    let slo = sx::add_epi16(lo, dv);
    let shi = sx::add_epi16(hi, dv);
    let r = sx::packus_epi16(slo, shi);
    proof {
        assert forall|c: int| 0 <= c < 16 implies #[trigger] v8(r)[c] == clamp255(v8(a)[c] as int + d as int) by {
            let (l, s, src) = if c < 8 { (c, v8(slo), v8(lo)) } else { (c - 8, v8(shi), v8(hi)) };
            lemma_zext_lane(v8(a), v8(z), l);
            lemma_set1_16_lane(du, l);
            lemma_add16_lane(src, v8(dv), l);
            assert(du as int == (d as int) % 65536);
            vstd::arithmetic::div_mod::lemma_add_mod_noop(v8(a)[c] as int, d as int, 65536);
            assert(w16(src, l) == v8(a)[c] as int);
            assert(w16(s, l) == (v8(a)[c] as int + d as int) % 65536);
            assert(sw16(s, l) == v8(a)[c] as int + d as int);
        }
    }
    r
}

/// The block's rows 0 .. r predicted, the rest of the plane as it was.
pub open spec fn pset(p: Plane, x: int, y: int, n: int, mode: nat, r: int) -> Plane {
    Seq::new(p.len(), |rr: int| if y <= rr < y + r {
        Seq::new(p[rr].len(), |cc: int| if x <= cc < x + n { pred_px(p, x, y, n, mode, rr - y, cc - x) } else { p[rr][cc] })
    } else { p[rr] })
}

/// predict_{dc,v,h,tm}_nxn (`predict`), a row at a time: `ab`, `lf` and
/// `al` are the row above, the column to the left and the pixel above-left,
/// `d` the DC value.
pub fn predict_rows(v: &mut Vec<u8>, w: usize, x: usize, y: usize, n: usize, mode: u8, d: u8, lf: &[i32; 16], al: i32,
    Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), n == 8 || n == 16, x + n <= w, y + n <= pl.len(),
        d == dc(pl, x as int, y as int, n as int), al as int == above_left(pl, x as int, y as int),
        forall|j: int| 0 <= j < n ==> #[trigger] lf@[j] as int == left(pl, x as int, y as int, j),
        forall|j: int| 0 <= j < 16 ==> 0 <= #[trigger] lf@[j] <= 255, 0 <= al <= 255,
    ensures holds(final(v)@, w as nat, predict(pl, x as int, y as int, n as int, mode as nat)),
{
    let ghost (xi, yi, ni, mi) = (x as int, y as int, n as int, mode as nat);
    proof { assert(rows_w(pl, w as nat)); }
    let a = above_row(v, w, x, y, n, Ghost(pl));
    let dcv = sx::set1_epi8(d);
    let mut r: usize = 0;
    proof { assert(pset(pl, xi, yi, ni, mi, 0) =~~= pl); }
    while r < n
        invariant r <= n, n == 8 || n == 16, x + n <= w, y + n <= pl.len(), rows_w(pl, w as nat),
            holds(v@, w as nat, pset(pl, xi, yi, ni, mi, r as int)), xi == x, yi == y, ni == n, mi == mode,
            d == dc(pl, xi, yi, ni), al as int == above_left(pl, xi, yi),
            forall|j: int| 0 <= j < n ==> #[trigger] lf@[j] as int == left(pl, xi, yi, j),
            forall|j: int| 0 <= j < 16 ==> 0 <= #[trigger] lf@[j] <= 255, 0 <= al <= 255,
            forall|c: int| 0 <= c < n ==> #[trigger] v8(a)[c] as int == above(pl, xi, yi, c),
            forall|c: int| 0 <= c < 16 ==> #[trigger] v8(dcv)[c] == d,
        decreases n - r,
    {
        let row = if mode == 0 { dcv } else if mode == 1 { a } else if mode == 2 { sx::set1_epi8(lf[r] as u8) } else { tm_row(a, lf[r] - al) };
        let ghost cur = pset(pl, xi, yi, ni, mi, r as int);
        proof {
            assert forall|c: int| 0 <= c < n implies #[trigger] v8(row)[c] == pred_px(pl, xi, yi, ni, mi, r as int, c) by {
                assert(lf@[r as int] as int == left(pl, xi, yi, r as int));
                assert(v8(a)[c] as int == above(pl, xi, yi, c));
            }
        }
        put_row(v, w, x, y + r, n, row, Ghost(cur));
        proof {
            assert(cur[yi + r] == pl[yi + r]);
            assert forall|cc: int| xi <= cc < xi + ni implies #[trigger] v8(row)[cc - xi] == pred_px(pl, xi, yi, ni, mi, r as int, cc - xi) by {}
            assert(set_rown(cur, xi, yi + r, ni, v8(row)) =~~= pset(pl, xi, yi, ni, mi, r + 1));
        }
        r = r + 1;
    }
    proof {
        reveal(predict);
        assert(pset(pl, xi, yi, ni, mi, ni) =~~= predict(pl, xi, yi, ni, mi));
    }
}

} // verus!
