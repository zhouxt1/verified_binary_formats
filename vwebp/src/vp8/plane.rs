//! A plane of pixels, stored as one buffer of rows `w` wide, seen by the
//! spec as rows (`spec::Plane`).
use vstd::prelude::*;
use super::spec::*;

verus! {

/// The buffer `v` holds the plane `pl`, rows of `w`.
pub open spec fn holds(v: Seq<u8>, w: nat, pl: Plane) -> bool {
    &&& pl.len() <= 16384 && w <= 16384
    &&& v.len() == pl.len() * w
    &&& forall|y: int| 0 <= y < pl.len() ==> (#[trigger] pl[y]).len() == w
    &&& forall|y: int, x: int| 0 <= y < pl.len() && 0 <= x < w ==> v[y * w + x] == #[trigger] pl[y][x]
}

pub proof fn lemma_idx(w: nat, h: nat, x: int, y: int)
    requires 0 <= x < w, 0 <= y < h,
    ensures 0 <= y * w, y * w + x < h * w,
{
    assert(y * w + x < h * w) by (nonlinear_arith) requires 0 <= x < w, 0 <= y < h;
    assert(y * w >= 0) by (nonlinear_arith) requires y >= 0;
}

pub proof fn lemma_distinct(w: nat, x: int, y: int, x2: int, y2: int)
    requires 0 <= x < w, 0 <= y, 0 <= x2 < w, 0 <= y2, x != x2 || y != y2,
    ensures y * w + x != y2 * w + x2,
{
    if y < y2 {
        assert(y * w + x < y2 * w + x2) by (nonlinear_arith) requires 0 <= x < w, y < y2, x2 >= 0;
    } else if y > y2 {
        assert(y2 * w + x2 < y * w + x) by (nonlinear_arith) requires 0 <= x2 < w, y2 < y, x >= 0;
    }
}

pub open spec fn set2(pl: Plane, x: int, y: int, v: u8) -> Plane { pl.update(y, pl[y].update(x, v)) }

/// A zeroed plane of `w` x `h`.
pub fn zeroed(w: usize, h: usize) -> (r: Vec<u8>)
    requires w <= 16384, h <= 16384,
    ensures holds(r@, w as nat, zero_plane(w as int, h as int)),
{
    proof { assert(w * h <= 16384 * 16384) by (nonlinear_arith) requires w <= 16384, h <= 16384; }
    let r = vec![0u8; w * h];
    proof {
        let pl = zero_plane(w as int, h as int);
        assert((h as nat) * (w as nat) == (w as nat) * (h as nat)) by (nonlinear_arith);
        assert forall|y: int, x: int| 0 <= y < pl.len() && 0 <= x < w implies r@[y * w + x] == #[trigger] pl[y][x] by {
            lemma_idx(w as nat, h as nat, x, y);
            assert(r@[y * w + x] == 0u8);
        }
        assert(r@.len() == pl.len() * w) by (nonlinear_arith) requires r@.len() == w * h, pl.len() == h;
    }
    r
}

pub fn get(v: &Vec<u8>, w: usize, x: usize, y: usize, Ghost(pl): Ghost<Plane>) -> (r: u8)
    requires holds(v@, w as nat, pl), x < w, y < pl.len(),
    ensures r == pl[y as int][x as int],
{
    let n = v.len();
    proof { lemma_idx(w as nat, pl.len(), x as int, y as int); }
    vsimd::mem::get(v.as_slice(), y * w + x)
}

pub fn set(v: &mut Vec<u8>, w: usize, x: usize, y: usize, val: u8, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), x < w, y < pl.len(),
    ensures holds(final(v)@, w as nat, set2(pl, x as int, y as int, val)),
{
    let n = v.len();
    proof { lemma_idx(w as nat, pl.len(), x as int, y as int); }
    let i = y * w + x;
    vsimd::mem::vset(v, i, val);
    proof {
        let p2 = set2(pl, x as int, y as int, val);
        assert forall|yy: int, xx: int| 0 <= yy < p2.len() && 0 <= xx < w implies v@[yy * w + xx] == #[trigger] p2[yy][xx] by {
            lemma_idx(w as nat, pl.len(), xx, yy);
            if yy != y || xx != x {
                lemma_distinct(w as nat, xx, yy, x as int, y as int);
            }
        }
    }
}

} // verus!
