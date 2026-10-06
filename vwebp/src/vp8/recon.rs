//! Intra prediction and reconstruction (RFC 6386 20.14, predict.c),
//! proved to follow `spec::luma` and `spec::chroma`.
use vstd::prelude::*;
use super::spec::*;
use super::hdr::*;
use super::plane::*;
use super::xf::*;
use super::tok::*;
use super::modes::*;

verus! {

pub proof fn lemma_lens(p: Plane, x: int, y: int, n: int, mode: nat, res: Seq<int>, mbw: int, mbx: int, mby: int, b: int, bm: nat, cs: Seq<int>)
    ensures
        add_block(p, x, y, res).len() == p.len(),
        predict(p, x, y, n, mode).len() == p.len(),
        b_block(p, mbw, mbx, mby, b, bm, cs).len() == p.len(),
{
    reveal(add_block);
    reveal(predict);
    reveal(b_pred4);
}

/// The plane with the `n` x `n` block at (x, y) set from `vals`, whose row
/// `r` starts at `16 r`.
pub open spec fn set_vals(p: Plane, x: int, y: int, n: int, vals: Seq<u8>) -> Plane {
    set_block(p, x, y, n, |r: int, c: int| vals[16 * r + c])
}

/// `set_vals` with rows before `r0`, and row `r0` before column `c0`, set.
pub open spec fn part(p: Plane, x: int, y: int, n: int, vals: Seq<u8>, r0: int, c0: int) -> Plane {
    Seq::new(p.len(), |r: int| if y <= r < y + n {
        Seq::new(p[r].len(), |c: int| if x <= c < x + n && (r - y < r0 || (r - y == r0 && c - x < c0)) {
            vals[16 * (r - y) + (c - x)]
        } else { p[r][c] })
    } else {
        p[r]
    })
}

/// Write the `n` x `n` block at (x, y) from `vals`.
pub fn fill_block(v: &mut Vec<u8>, w: usize, x: usize, y: usize, n: usize, vals: &[u8; 256], Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), 1 <= n <= 16, x + n <= w, y + n <= pl.len(),
    ensures holds(final(v)@, w as nat, set_vals(pl, x as int, y as int, n as int, vals@)),
{
    let mut r: usize = 0;
    proof { assert(part(pl, x as int, y as int, n as int, vals@, 0, 0) =~~= pl); }
    while r < n
        invariant
            1 <= n <= 16, x + n <= w, y + n <= pl.len(), r <= n,
            holds(v@, w as nat, part(pl, x as int, y as int, n as int, vals@, r as int, 0)),
            forall|yy: int| 0 <= yy < pl.len() ==> (#[trigger] pl[yy]).len() == w,
        decreases n - r,
    {
        let mut c: usize = 0;
        while c < n
            invariant
                1 <= n <= 16, x + n <= w, y + n <= pl.len(), r < n, c <= n,
                holds(v@, w as nat, part(pl, x as int, y as int, n as int, vals@, r as int, c as int)),
                forall|yy: int| 0 <= yy < pl.len() ==> (#[trigger] pl[yy]).len() == w,
            decreases n - c,
        {
            let ghost pp = part(pl, x as int, y as int, n as int, vals@, r as int, c as int);
            set(v, w, x + c, y + r, vals[16 * r + c], Ghost(pp));
            proof {
                assert(set2(pp, (x + c) as int, (y + r) as int, vals@[16 * r + c])
                    =~~= part(pl, x as int, y as int, n as int, vals@, r as int, c + 1));
            }
            c = c + 1;
        }
        proof {
            assert(part(pl, x as int, y as int, n as int, vals@, r as int, n as int)
                =~~= part(pl, x as int, y as int, n as int, vals@, r + 1, 0));
        }
        r = r + 1;
    }
    proof {
        assert(part(pl, x as int, y as int, n as int, vals@, n as int, 0) =~~= set_vals(pl, x as int, y as int, n as int, vals@));
    }
}

pub fn clamp255_x(x: i32) -> (r: u8)
    ensures r == clamp255(x as int),
{
    if x < 0 { 0 } else if x > 255 { 255 } else { x as u8 }
}

/// `above`, `left` and `above_left`: what a predictor reads.
fn above_x(v: &Vec<u8>, w: usize, x: usize, y: usize, k: usize, Ghost(pl): Ghost<Plane>) -> (r: i32)
    requires holds(v@, w as nat, pl), x + k < w, y < pl.len(),
    ensures r as int == above(pl, x as int, y as int, k as int), 0 <= r <= 255,
{
    if y == 0 { 127 } else { get(v, w, x + k, y - 1, Ghost(pl)) as i32 }
}

fn left_x(v: &Vec<u8>, w: usize, x: usize, y: usize, k: usize, Ghost(pl): Ghost<Plane>) -> (r: i32)
    requires holds(v@, w as nat, pl), x < w, y + k < pl.len(),
    ensures r as int == left(pl, x as int, y as int, k as int), 0 <= r <= 255,
{
    if x == 0 { 129 } else { get(v, w, x - 1, y + k, Ghost(pl)) as i32 }
}

fn above_left_x(v: &Vec<u8>, w: usize, x: usize, y: usize, Ghost(pl): Ghost<Plane>) -> (r: i32)
    requires holds(v@, w as nat, pl), x < w, y < pl.len(),
    ensures r as int == above_left(pl, x as int, y as int), 0 <= r <= 255,
{
    if y == 0 { 127 } else if x == 0 { 129 } else { get(v, w, x - 1, y - 1, Ghost(pl)) as i32 }
}

/// predict_{dc,v,h,tm}_nxn (`predict`).
pub fn predict_x(v: &mut Vec<u8>, w: usize, x: usize, y: usize, n: usize, mode: u8, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), n == 8 || n == 16, x + n <= w, y + n <= pl.len(),
    ensures holds(final(v)@, w as nat, predict(pl, x as int, y as int, n as int, mode as nat)),
{
    proof { reveal(predict); }
    let mut ab: [i32; 16] = [0; 16];
    let mut lf: [i32; 16] = [0; 16];
    let mut sum: i32 = 0;
    let mut k: usize = 0;
    while k < n
        invariant
            holds(v@, w as nat, pl), n == 8 || n == 16, x + n <= w, y + n <= pl.len(), k <= n,
            forall|j: int| 0 <= j < k ==> #[trigger] ab@[j] as int == above(pl, x as int, y as int, j),
            forall|j: int| 0 <= j < k ==> #[trigger] lf@[j] as int == left(pl, x as int, y as int, j),
            forall|j: int| 0 <= j < 16 ==> 0 <= #[trigger] ab@[j] <= 255,
            forall|j: int| 0 <= j < 16 ==> 0 <= #[trigger] lf@[j] <= 255,
            sum as int == dc_sum(pl, x as int, y as int, k as int), 0 <= sum <= 510 * k,
        decreases n - k,
    {
        ab[k] = above_x(v, w, x, y, k, Ghost(pl));
        lf[k] = left_x(v, w, x, y, k, Ghost(pl));
        let da = if y == 0 && x > 0 { lf[k] } else { ab[k] };
        let dl = if x == 0 && y > 0 { ab[k] } else { lf[k] };
        sum = sum + da + dl;
        k = k + 1;
    }
    let al = above_left_x(v, w, x, y, Ghost(pl));
    let d: u8 = ((sum + n as i32) / (2 * n as i32)) as u8;
    proof {
        assert((sum + n as i32) / (2 * n as i32) <= 255) by (nonlinear_arith)
            requires 0 <= sum <= 510 * n, n == 8 || n == 16;
    }
    #[cfg(target_arch = "x86_64")]
    super::predx::predict_rows(v, w, x, y, n, mode, d, &lf, al, Ghost(pl));
    #[cfg(not(target_arch = "x86_64"))]
    {
        let mut vals: [u8; 256] = [0; 256];
        let mut r: usize = 0;
        while r < n
            invariant
                n == 8 || n == 16, r <= n, d == dc(pl, x as int, y as int, n as int), al as int == above_left(pl, x as int, y as int),
                forall|j: int| 0 <= j < n ==> #[trigger] ab@[j] as int == above(pl, x as int, y as int, j),
                forall|j: int| 0 <= j < n ==> #[trigger] lf@[j] as int == left(pl, x as int, y as int, j),
                forall|j: int| 0 <= j < 16 ==> 0 <= #[trigger] ab@[j] <= 255,
                forall|j: int| 0 <= j < 16 ==> 0 <= #[trigger] lf@[j] <= 255,
                forall|rr: int, cc: int| 0 <= rr < r && 0 <= cc < n ==>
                    vals@[16 * rr + cc] == #[trigger] pred_px(pl, x as int, y as int, n as int, mode as nat, rr, cc),
            decreases n - r,
        {
            let mut c: usize = 0;
            while c < n
                invariant
                    n == 8 || n == 16, r < n, c <= n, d == dc(pl, x as int, y as int, n as int), al as int == above_left(pl, x as int, y as int),
                    forall|j: int| 0 <= j < n ==> #[trigger] ab@[j] as int == above(pl, x as int, y as int, j),
                    forall|j: int| 0 <= j < n ==> #[trigger] lf@[j] as int == left(pl, x as int, y as int, j),
                    forall|j: int| 0 <= j < 16 ==> 0 <= #[trigger] ab@[j] <= 255,
                    forall|j: int| 0 <= j < 16 ==> 0 <= #[trigger] lf@[j] <= 255,
                    forall|rr: int, cc: int| (0 <= rr < r && 0 <= cc < n) || (rr == r && 0 <= cc < c) ==>
                        vals@[16 * rr + cc] == #[trigger] pred_px(pl, x as int, y as int, n as int, mode as nat, rr, cc),
                decreases n - c,
            {
                let p: u8 = if mode == 0 { d } else if mode == 1 { ab[c] as u8 } else if mode == 2 { lf[r] as u8 }
                            else { clamp255_x(lf[r] + ab[c] - al) };
                vals[16 * r + c] = p;
                proof {
                    assert forall|rr: int, cc: int| (0 <= rr < r && 0 <= cc < n) || (rr == r && 0 <= cc < c + 1) implies
                        vals@[16 * rr + cc] == #[trigger] pred_px(pl, x as int, y as int, n as int, mode as nat, rr, cc) by {
                        if rr == r && cc == c {
                        } else {
                            assert(16 * rr + cc != 16 * r + c);
                        }
                    }
                }
                c = c + 1;
            }
            r = r + 1;
        }
        fill_block(v, w, x, y, n, &vals, Ghost(pl));
        proof {
            assert(set_vals(pl, x as int, y as int, n as int, vals@) =~~= predict(pl, x as int, y as int, n as int, mode as nat));
        }
    }
}

/// The residual of the coefficients `c` added to the 4x4 block at (x, y):
/// in SSE2 where there is SSE2 (`xfx::idct_add_x`), else `idct_x` and
/// `add_block_x`.
fn idct_add(v: &mut Vec<u8>, w: usize, x: usize, y: usize, c: &[i32; 16], dc: bool, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), x + 4 <= w, y + 4 <= pl.len(), c16(c@),
        dc ==> super::xfx::dc_only(c@),
    ensures holds(final(v)@, w as nat, add_block(pl, x as int, y as int, idct(ints(c@)))),
{
    #[cfg(target_arch = "x86_64")]
    {
        if dc {
            if c[0] == 0 {
                proof {
                    assert(super::lfx::rows_w(pl, w as nat));
                    super::xfx::lemma_add_zero(pl, w as nat, x as int, y as int, c@);
                }
            } else {
                super::xfx::dc_add_x(v, w, x, y, c, Ghost(pl));
            }
        } else {
            super::xfx::idct_add_x(v, w, x, y, c, Ghost(pl));
        }
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        let res = idct_x(c);
        add_block_x(v, w, x, y, &res, Ghost(pl));
    }
}

/// The residual `res` added to the 4x4 block at (x, y) (`add_block`).
pub fn add_block_x(v: &mut Vec<u8>, w: usize, x: usize, y: usize, res: &[i32; 16], Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), x + 4 <= w, y + 4 <= pl.len(),
        forall|j: int| 0 <= j < 16 ==> -16384 <= #[trigger] res@[j] <= 16384,
    ensures holds(final(v)@, w as nat, add_block(pl, x as int, y as int, ints(res@))),
{
    proof { reveal(add_block); }
    let mut vals: [u8; 256] = [0; 256];
    let mut r: usize = 0;
    while r < 4
        invariant
            holds(v@, w as nat, pl), x + 4 <= w, y + 4 <= pl.len(), r <= 4,
            forall|j: int| 0 <= j < 16 ==> -16384 <= #[trigger] res@[j] <= 16384,
            forall|rr: int, cc: int| 0 <= rr < r && 0 <= cc < 4 ==>
                vals@[16 * rr + cc] == #[trigger] add_px(pl, x as int, y as int, ints(res@), rr, cc),
        decreases 4 - r,
    {
        let mut c: usize = 0;
        while c < 4
            invariant
                holds(v@, w as nat, pl), x + 4 <= w, y + 4 <= pl.len(), r < 4, c <= 4,
                forall|j: int| 0 <= j < 16 ==> -16384 <= #[trigger] res@[j] <= 16384,
                forall|rr: int, cc: int| (0 <= rr < r && 0 <= cc < 4) || (rr == r && 0 <= cc < c) ==>
                    vals@[16 * rr + cc] == #[trigger] add_px(pl, x as int, y as int, ints(res@), rr, cc),
            decreases 4 - c,
        {
            let p = get(v, w, x + c, y + r, Ghost(pl));
            vals[16 * r + c] = clamp255_x(p as i32 + res[4 * r + c]);
            proof {
                assert forall|rr: int, cc: int| (0 <= rr < r && 0 <= cc < 4) || (rr == r && 0 <= cc < c + 1) implies
                    vals@[16 * rr + cc] == #[trigger] add_px(pl, x as int, y as int, ints(res@), rr, cc) by {
                    if !(rr == r && cc == c) {
                        assert(16 * rr + cc != 16 * r + c);
                    }
                }
            }
            c = c + 1;
        }
        r = r + 1;
    }
    fill_block(v, w, x, y, 4, &vals, Ghost(pl));
    proof {
        assert(set_vals(pl, x as int, y as int, 4, vals@) =~~= add_block(pl, x as int, y as int, ints(res@)));
    }
}

fn avg2_x(x: i32, y: i32) -> (r: u8)
    requires 0 <= x <= 255, 0 <= y <= 255,
    ensures r == avg2(x as int, y as int),
{
    ((x + y + 1) / 2) as u8
}

fn avg3_x(x: i32, y: i32, z: i32) -> (r: u8)
    requires 0 <= x <= 255, 0 <= y <= 255, 0 <= z <= 255,
    ensures r == avg3(x as int, y as int, z as int),
{
    ((x + 2 * y + z + 2) / 4) as u8
}

pub open spec fn px8(s: Seq<i32>) -> bool { forall|k: int| 0 <= k < s.len() ==> 0 <= #[trigger] s[k] <= 255 }

/// The 4x4 predictors (`pred4`), pixel (r, c).
fn pred4_x(mode: u8, a: &[i32; 9], l: &[i32; 4], r: usize, c: usize) -> (p: u8)
    requires mode <= 9, px8(a@), px8(l@), r < 4, c < 4,
    ensures p == pred4(mode as nat, ints(a@), ints(l@), r as int, c as int),
{
    if mode <= 5 {
        pred4_direct(mode, a, l, r, c)
    } else {
        let v = if mode == 6 { pred4_vr(a, l) } else if mode == 7 { pred4_vl(a, l) } else if mode == 8 { pred4_hd(a, l) } else { pred4_hu(a, l) };
        proof { assert(v@[4 * r + c] == pred4_row(mode as nat, ints(a@), ints(l@))[4 * r + c]); }
        v[4 * r + c]
    }
}

/// Modes 0..5 of `pred4`.
fn pred4_direct(mode: u8, a: &[i32; 9], l: &[i32; 4], r: usize, c: usize) -> (p: u8)
    requires mode <= 5, px8(a@), px8(l@), r < 4, c < 4,
    ensures p == pred4(mode as nat, ints(a@), ints(l@), r as int, c as int),
{
    let p0 = a[0];
    if mode == 0 {
        ((a[1] + a[2] + a[3] + a[4] + l[0] + l[1] + l[2] + l[3] + 4) / 8) as u8
    } else if mode == 1 {
        clamp255_x(l[r] + a[c + 1] - p0)
    } else if mode == 2 {
        avg3_x(a[c], a[c + 1], a[c + 2])
    } else if mode == 3 {
        if r == 0 { avg3_x(p0, l[0], l[1]) } else if r == 1 { avg3_x(l[0], l[1], l[2]) }
        else if r == 2 { avg3_x(l[1], l[2], l[3]) } else { avg3_x(l[2], l[3], l[3]) }
    } else if mode == 4 {
        let k = r + c;
        if k < 6 { avg3_x(a[k + 1], a[k + 2], a[k + 3]) } else { avg3_x(a[7], a[8], a[8]) }
    } else {
        let e: [i32; 9] = [l[3], l[2], l[1], l[0], p0, a[1], a[2], a[3], a[4]];
        let k = 4 + c - r;
        proof { assert(e@ =~= seq![l@[3], l@[2], l@[1], l@[0], p0, a@[1], a@[2], a@[3], a@[4]]); }
        avg3_x(e[k - 1], e[k], e[k + 1])
    }
}

fn pred4_dc(a: &[i32; 9], l: &[i32; 4]) -> (v: [u8; 16])
    requires px8(a@), px8(l@),
    ensures v@ == pred4_row(0, ints(a@), ints(l@)),
{
    let d = ((a[1] + a[2] + a[3] + a[4] + l[0] + l[1] + l[2] + l[3] + 4) / 8) as u8;
    let v: [u8; 16] = [d; 16];
    proof { assert(v@ =~= pred4_row(0, ints(a@), ints(l@))); }
    v
}

fn pred4_tm(a: &[i32; 9], l: &[i32; 4]) -> (v: [u8; 16])
    requires px8(a@), px8(l@),
    ensures v@ == pred4_row(1, ints(a@), ints(l@)),
{
    let p0 = a[0];
    let v: [u8; 16] = [
        clamp255_x(l[0] + a[1] - p0), clamp255_x(l[0] + a[2] - p0), clamp255_x(l[0] + a[3] - p0), clamp255_x(l[0] + a[4] - p0),
        clamp255_x(l[1] + a[1] - p0), clamp255_x(l[1] + a[2] - p0), clamp255_x(l[1] + a[3] - p0), clamp255_x(l[1] + a[4] - p0),
        clamp255_x(l[2] + a[1] - p0), clamp255_x(l[2] + a[2] - p0), clamp255_x(l[2] + a[3] - p0), clamp255_x(l[2] + a[4] - p0),
        clamp255_x(l[3] + a[1] - p0), clamp255_x(l[3] + a[2] - p0), clamp255_x(l[3] + a[3] - p0), clamp255_x(l[3] + a[4] - p0),
    ];
    proof { assert(v@ =~= pred4_row(1, ints(a@), ints(l@))); }
    v
}

fn pred4_ve(a: &[i32; 9], l: &[i32; 4]) -> (v: [u8; 16])
    requires px8(a@), px8(l@),
    ensures v@ == pred4_row(2, ints(a@), ints(l@)),
{
    let (t0, t1, t2, t3) = (avg3_x(a[0], a[1], a[2]), avg3_x(a[1], a[2], a[3]), avg3_x(a[2], a[3], a[4]), avg3_x(a[3], a[4], a[5]));
    let v: [u8; 16] = [t0, t1, t2, t3, t0, t1, t2, t3, t0, t1, t2, t3, t0, t1, t2, t3];
    proof { assert(v@ =~= pred4_row(2, ints(a@), ints(l@))); }
    v
}

fn pred4_he(a: &[i32; 9], l: &[i32; 4]) -> (v: [u8; 16])
    requires px8(a@), px8(l@),
    ensures v@ == pred4_row(3, ints(a@), ints(l@)),
{
    let (h0, h1, h2, h3) = (avg3_x(a[0], l[0], l[1]), avg3_x(l[0], l[1], l[2]), avg3_x(l[1], l[2], l[3]), avg3_x(l[2], l[3], l[3]));
    let v: [u8; 16] = [h0, h0, h0, h0, h1, h1, h1, h1, h2, h2, h2, h2, h3, h3, h3, h3];
    proof { assert(v@ =~= pred4_row(3, ints(a@), ints(l@))); }
    v
}

fn pred4_ld(a: &[i32; 9], l: &[i32; 4]) -> (v: [u8; 16])
    requires px8(a@), px8(l@),
    ensures v@ == pred4_row(4, ints(a@), ints(l@)),
{
    let d0 = avg3_x(a[1], a[2], a[3]);
    let d1 = avg3_x(a[2], a[3], a[4]);
    let d2 = avg3_x(a[3], a[4], a[5]);
    let d3 = avg3_x(a[4], a[5], a[6]);
    let d4 = avg3_x(a[5], a[6], a[7]);
    let d5 = avg3_x(a[6], a[7], a[8]);
    let d6 = avg3_x(a[7], a[8], a[8]);
    let v: [u8; 16] = [d0, d1, d2, d3, d1, d2, d3, d4, d2, d3, d4, d5, d3, d4, d5, d6];
    proof { assert(v@ =~= pred4_row(4, ints(a@), ints(l@))); }
    v
}

fn pred4_rd(a: &[i32; 9], l: &[i32; 4]) -> (v: [u8; 16])
    requires px8(a@), px8(l@),
    ensures v@ == pred4_row(5, ints(a@), ints(l@)),
{
    let p0 = a[0];
    // e = l3 l2 l1 l0 p t0 t1 t2 t3; pixel (r, c) is avg3 around e[4 - r + c]
    let e1 = avg3_x(l[3], l[2], l[1]);
    let e2 = avg3_x(l[2], l[1], l[0]);
    let e3 = avg3_x(l[1], l[0], p0);
    let e4 = avg3_x(l[0], p0, a[1]);
    let e5 = avg3_x(p0, a[1], a[2]);
    let e6 = avg3_x(a[1], a[2], a[3]);
    let e7 = avg3_x(a[2], a[3], a[4]);
    let v: [u8; 16] = [e4, e5, e6, e7, e3, e4, e5, e6, e2, e3, e4, e5, e1, e2, e3, e4];
    proof { assert(v@ =~= pred4_row(5, ints(a@), ints(l@))); }
    v
}

fn pred4_vr(a: &[i32; 9], l: &[i32; 4]) -> (v: [u8; 16])
    requires px8(a@), px8(l@),
    ensures v@ == pred4_row(6, ints(a@), ints(l@)),
{
    let p0 = a[0];
    let v: [u8; 16] = [
        avg2_x(p0, a[1]), avg2_x(a[1], a[2]), avg2_x(a[2], a[3]), avg2_x(a[3], a[4]),
        avg3_x(l[0], p0, a[1]), avg3_x(p0, a[1], a[2]), avg3_x(a[1], a[2], a[3]), avg3_x(a[2], a[3], a[4]),
        avg3_x(l[1], l[0], p0), avg2_x(p0, a[1]), avg2_x(a[1], a[2]), avg2_x(a[2], a[3]),
        avg3_x(l[2], l[1], l[0]), avg3_x(l[0], p0, a[1]), avg3_x(p0, a[1], a[2]), avg3_x(a[1], a[2], a[3]),
    ];
    proof { assert(v@ =~= pred4_row(6, ints(a@), ints(l@))); }
    v
}

fn pred4_vl(a: &[i32; 9], l: &[i32; 4]) -> (v: [u8; 16])
    requires px8(a@), px8(l@),
    ensures v@ == pred4_row(7, ints(a@), ints(l@)),
{
    let v: [u8; 16] = [
        avg2_x(a[1], a[2]), avg2_x(a[2], a[3]), avg2_x(a[3], a[4]), avg2_x(a[4], a[5]),
        avg3_x(a[1], a[2], a[3]), avg3_x(a[2], a[3], a[4]), avg3_x(a[3], a[4], a[5]), avg3_x(a[4], a[5], a[6]),
        avg2_x(a[2], a[3]), avg2_x(a[3], a[4]), avg2_x(a[4], a[5]), avg3_x(a[5], a[6], a[7]),
        avg3_x(a[2], a[3], a[4]), avg3_x(a[3], a[4], a[5]), avg3_x(a[4], a[5], a[6]), avg3_x(a[6], a[7], a[8]),
    ];
    proof { assert(v@ =~= pred4_row(7, ints(a@), ints(l@))); }
    v
}

fn pred4_hd(a: &[i32; 9], l: &[i32; 4]) -> (v: [u8; 16])
    requires px8(a@), px8(l@),
    ensures v@ == pred4_row(8, ints(a@), ints(l@)),
{
    let p0 = a[0];
    let v: [u8; 16] = [
        avg2_x(l[0], p0), avg3_x(l[0], p0, a[1]), avg3_x(p0, a[1], a[2]), avg3_x(a[1], a[2], a[3]),
        avg2_x(l[1], l[0]), avg3_x(l[1], l[0], p0), avg2_x(l[0], p0), avg3_x(l[0], p0, a[1]),
        avg2_x(l[2], l[1]), avg3_x(l[2], l[1], l[0]), avg2_x(l[1], l[0]), avg3_x(l[1], l[0], p0),
        avg2_x(l[3], l[2]), avg3_x(l[3], l[2], l[1]), avg2_x(l[2], l[1]), avg3_x(l[2], l[1], l[0]),
    ];
    proof { assert(v@ =~= pred4_row(8, ints(a@), ints(l@))); }
    v
}

fn pred4_hu(a: &[i32; 9], l: &[i32; 4]) -> (v: [u8; 16])
    requires px8(a@), px8(l@),
    ensures v@ == pred4_row(9, ints(a@), ints(l@)),
{
    let l3 = l[3] as u8;
    let v: [u8; 16] = [
        avg2_x(l[0], l[1]), avg3_x(l[0], l[1], l[2]), avg2_x(l[1], l[2]), avg3_x(l[1], l[2], l[3]),
        avg2_x(l[1], l[2]), avg3_x(l[1], l[2], l[3]), avg2_x(l[2], l[3]), avg3_x(l[2], l[3], l[3]),
        avg2_x(l[2], l[3]), avg3_x(l[2], l[3], l[3]), l3, l3,
        l3, l3, l3, l3,
    ];
    proof { assert(v@ =~= pred4_row(9, ints(a@), ints(l@))); }
    v
}

/// The 16 values of the table-shaped predictors (modes 6..9), for the proof.
pub open spec fn pred4_row(mode: nat, a: Seq<int>, l: Seq<int>) -> Seq<u8> {
    Seq::new(16, |j: int| pred4(mode, a, l, j / 4, j % 4))
}

/// `above_right`.
fn above_right_x(v: &Vec<u8>, w: usize, mbw: usize, mbx: usize, mby: usize, b: usize, k: usize, Ghost(pl): Ghost<Plane>) -> (r: i32)
    requires holds(v@, w as nat, pl), w == mbw * 16, mbx < mbw, mby * 16 + 16 <= pl.len(), b < 16, k < 4,
    ensures r as int == above_right(pl, mbw as int, mbx as int, mby as int, b as int, k as int), 0 <= r <= 255,
{
    let bx = b % 4;
    let by = b / 4;
    let x = mbx * 16 + bx * 4;
    let y = mby * 16 + by * 4;
    if bx < 3 && by > 0 {
        get(v, w, x + 4 + k, y - 1, Ghost(pl)) as i32
    } else if mby == 0 {
        127
    } else if bx < 3 {
        get(v, w, x + 4 + k, mby * 16 - 1, Ghost(pl)) as i32
    } else if mbx == mbw - 1 {
        get(v, w, mbw * 16 - 1, mby * 16 - 1, Ghost(pl)) as i32
    } else {
        get(v, w, mbx * 16 + 16 + k, mby * 16 - 1, Ghost(pl)) as i32
    }
}

/// Subblock `b` of the macroblock at (mbx, mby) (`b_block`).
fn b_block_x(v: &mut Vec<u8>, w: usize, mbw: usize, mbx: usize, mby: usize, b: usize, mode: u8, co: &[i32; 16], dc: bool, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), w == mbw * 16, mbx < mbw, mby * 16 + 16 <= pl.len(), b < 16, mode <= 9, c16(co@),
        dc ==> super::xfx::dc_only(co@),
    ensures holds(final(v)@, w as nat, b_block(pl, mbw as int, mbx as int, mby as int, b as int, mode as nat, ints(co@))),
{
    let x = mbx * 16 + (b % 4) * 4;
    let y = mby * 16 + (b / 4) * 4;
    let mut a: [i32; 9] = [0; 9];
    let mut l: [i32; 4] = [0; 4];
    a[0] = above_left_x(v, w, x, y, Ghost(pl));
    let mut k: usize = 0;
    while k < 4
        invariant
            holds(v@, w as nat, pl), w == mbw * 16, mbx < mbw, mby * 16 + 16 <= pl.len(), b < 16, k <= 4,
            x == mbx * 16 + (b % 4) * 4, y == mby * 16 + (b / 4) * 4, px8(a@), px8(l@),
            a@[0] as int == above_left(pl, x as int, y as int),
            forall|j: int| 0 <= j < k ==> #[trigger] a@[1 + j] as int == above(pl, x as int, y as int, j),
            forall|j: int| 0 <= j < k ==> #[trigger] a@[5 + j] as int == above_right(pl, mbw as int, mbx as int, mby as int, b as int, j),
            forall|j: int| 0 <= j < k ==> #[trigger] l@[j] as int == left(pl, x as int, y as int, j),
        decreases 4 - k,
    {
        a[1 + k] = above_x(v, w, x, y, k, Ghost(pl));
        a[5 + k] = above_right_x(v, w, mbw, mbx, mby, b, k, Ghost(pl));
        l[k] = left_x(v, w, x, y, k, Ghost(pl));
        k = k + 1;
    }
    let ghost ba = b_above(pl, mbw as int, mbx as int, mby as int, b as int);
    let ghost bl = b_left(pl, mbx as int, mby as int, b as int);
    proof {
        assert(ints(a@) =~= ba) by {
            assert forall|j: int| 0 <= j < 9 implies #[trigger] ints(a@)[j] == ba[j] by {
                if 1 <= j <= 4 { assert(a@[1 + (j - 1)] as int == above(pl, x as int, y as int, j - 1)); }
                else if j >= 5 { assert(a@[5 + (j - 5)] as int == above_right(pl, mbw as int, mbx as int, mby as int, b as int, j - 5)); }
            }
        }
        assert(ints(l@) =~= bl);
    }
    let p16 = pred4_all(mode, &a, &l);
    let ghost pred = b_pred4(pl, mbw as int, mbx as int, mby as int, b as int, mode as nat);
    #[cfg(target_arch = "x86_64")]
    {
        if dc {
            super::xfx::dc_add_pred_x(v, w, x, y, &p16, co, Ghost(pl));
        } else {
            super::xfx::idct_add_pred_x(v, w, x, y, &p16, co, Ghost(pl));
        }
        proof {
            reveal(b_pred4);
            assert forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 implies #[trigger] p16@[4 * r + c] == pred4(mode as nat, ba, bl, r, c) by {
                assert((4 * r + c) / 4 == r && (4 * r + c) % 4 == c);
            }
            assert(super::xfx::set_pred(pl, x as int, y as int, p16@) =~~= pred);
        }
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        let mut vals: [u8; 256] = [0; 256];
        let mut k: usize = 0;
        while k < 16
            invariant k <= 16, forall|j: int| 0 <= j < k ==> vals@[16 * (j / 4) + j % 4] == #[trigger] p16@[j],
            decreases 16 - k,
        {
            vals[16 * (k / 4) + k % 4] = p16[k];
            proof {
                assert forall|j: int| 0 <= j < k + 1 implies vals@[16 * (j / 4) + j % 4] == #[trigger] p16@[j] by {
                    if j != k { assert(16 * (j / 4) + j % 4 != 16 * (k / 4) + k % 4); }
                }
            }
            k = k + 1;
        }
        fill_block(v, w, x, y, 4, &vals, Ghost(pl));
        proof {
            reveal(b_pred4);
            assert(set_vals(pl, x as int, y as int, 4, vals@) =~~= pred) by {
                assert forall|r: int, c: int| 0 <= r < 4 && 0 <= c < 4 implies #[trigger] vals@[16 * r + c] == pred4(mode as nat, ba, bl, r, c) by {
                    assert(vals@[16 * ((4 * r + c) / 4) + (4 * r + c) % 4] == p16@[4 * r + c]);
                    assert((4 * r + c) / 4 == r && (4 * r + c) % 4 == c);
                }
            }
        }
        idct_add(v, w, x, y, co, dc, Ghost(pred));
    }
}

/// The 16 pixels of a 4x4 predictor (`pred4`), row by row.
fn pred4_all(mode: u8, a: &[i32; 9], l: &[i32; 4]) -> (p: [u8; 16])
    requires mode <= 9, px8(a@), px8(l@),
    ensures forall|k: int| 0 <= k < 16 ==> #[trigger] p@[k] == pred4(mode as nat, ints(a@), ints(l@), k / 4, k % 4),
{
    let v = if mode == 0 { pred4_dc(a, l) } else if mode == 1 { pred4_tm(a, l) } else if mode == 2 { pred4_ve(a, l) }
        else if mode == 3 { pred4_he(a, l) } else if mode == 4 { pred4_ld(a, l) } else if mode == 5 { pred4_rd(a, l) }
        else if mode == 6 { pred4_vr(a, l) } else if mode == 7 { pred4_vl(a, l) } else if mode == 8 { pred4_hd(a, l) } else { pred4_hu(a, l) };
    proof {
        assert forall|k: int| 0 <= k < 16 implies #[trigger] v@[k] == pred4(mode as nat, ints(a@), ints(l@), k / 4, k % 4) by {
            assert(v@[k] == pred4_row(mode as nat, ints(a@), ints(l@))[k]);
        }
    }
    v
}

/// Block `i` of `co` as an array.
fn block16(co: &[i32; 400], i: usize) -> (r: [i32; 16])
    requires i < 25, c16(co@),
    ensures ints(r@) == blk(co@, i as int), c16(r@),
{
    let mut r: [i32; 16] = [0; 16];
    let mut j: usize = 0;
    while j < 16
        invariant j <= 16, i < 25, c16(co@), c16(r@),
            forall|k: int| 0 <= k < j ==> #[trigger] r@[k] == co@[16 * i + k],
        decreases 16 - j,
    {
        r[j] = vsimd::mem::aget(co, 16 * i + j);
        j = j + 1;
    }
    proof { assert(ints(r@) =~= blk(co@, i as int)); }
    r
}

/// Block `i` is a DC alone by the tokens' mask (`mb_tokens_x`): its copy
/// `cb` has 0 in positions 1..16.
#[inline(always)]
fn dc_known(dcx: u32, i: usize, cb: &[i32; 16], Ghost(co): Ghost<Seq<i32>>) -> (r: bool)
    requires i < 25, co.len() == 400, ints(cb@) == blk(co, i as int),
        forall|j: int| 0 <= j < 25 && #[trigger] bit(dcx, j) ==> acz(co, j),
    ensures r ==> forall|k: int| 1 <= k < 16 ==> #[trigger] cb@[k] == 0,
{
    let r = (dcx >> (i as u32)) & 1u32 == 1u32;
    proof {
        if r {
            assert(bit(dcx, i as int));
            assert(acz(co, i as int));
            assert forall|k: int| 1 <= k < 16 implies #[trigger] cb@[k] == 0 by {
                assert(ints(cb@)[k] == blk(co, i as int)[k]);
                assert(ints(cb@)[k] == cb@[k] as int);
                assert(co[16 * i + k] == 0);
            }
        }
    }
    r
}

/// predict_intra_luma (`luma`).
pub fn luma_x(v: &mut Vec<u8>, w: usize, mbw: usize, mbx: usize, mby: usize, mb: &MbX, co: &[i32; 400], dcx: u32, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), w == mbw * 16, mbx < mbw, mby * 16 + 16 <= pl.len(), mb.wf(), c16(co@),
        forall|j: int| 0 <= j < 25 && #[trigger] bit(dcx, j) ==> acz(co@, j),
    ensures holds(final(v)@, w as nat, luma(pl, mbw as int, mbx as int, mby as int, mb.view(), blocks(co@))),
        luma(pl, mbw as int, mbx as int, mby as int, mb.view(), blocks(co@)).len() == pl.len(),
{
    proof { reveal(luma); }
    let ghost cs = blocks(co@);
    if mb.y_mode == 4 {
        let mut b: usize = 0;
        let ghost mut cur = pl;
        while b < 16
            invariant
                holds(v@, w as nat, cur), w == mbw * 16, mbx < mbw, mby * 16 + 16 <= pl.len(), cur.len() == pl.len(), mb.wf(), c16(co@), b <= 16,
                cs == blocks(co@), mb.y_mode == 4,
                forall|j: int| 0 <= j < 25 && #[trigger] bit(dcx, j) ==> acz(co@, j),
                b_pred(cur, mbw as int, mbx as int, mby as int, mb.view(), cs, b as int)
                    == b_pred(pl, mbw as int, mbx as int, mby as int, mb.view(), cs, 0),
            decreases 16 - b,
        {
            let cb = block16(co, b);
            let dc = dc_known(dcx, b, &cb, Ghost(co@));
            proof { assert(cs[b as int] == ints(cb@)); assert(mb.view().b_modes[b as int] == mb.b_modes@[b as int] as nat); }
            b_block_x(v, w, mbw, mbx, mby, b, mb.b_modes[b], &cb, dc, Ghost(cur));
            proof {
                lemma_lens(cur, 0, 0, 0, 0, Seq::empty(), mbw as int, mbx as int, mby as int, b as int, mb.b_modes@[b as int] as nat, ints(cb@));
                cur = b_block(cur, mbw as int, mbx as int, mby as int, b as int, mb.b_modes@[b as int] as nat, ints(cb@));
            }
            b = b + 1;
        }
    } else {
        let x = mbx * 16;
        let y = mby * 16;
        predict_x(v, w, x, y, 16, mb.y_mode, Ghost(pl));
        let ghost p1 = predict(pl, x as int, y as int, 16, mb.y_mode as nat);
        proof { lemma_lens(pl, x as int, y as int, 16, mb.y_mode as nat, Seq::empty(), 0, 0, 0, 0, 0, Seq::empty()); }
        let y2 = block16(co, 24);
        let dcs = iwht_x(&y2);
        let ghost lc = luma_cs(cs);
        let mut b: usize = 0;
        let ghost mut cur = p1;
        while b < 16
            invariant
                holds(v@, w as nat, cur), w == mbw * 16, mbx < mbw, mby * 16 + 16 <= pl.len(), cur.len() == pl.len(), c16(co@), c16(dcs@), b <= 16,
                x == mbx * 16, y == mby * 16, cs == blocks(co@), lc == luma_cs(cs), ints(dcs@) == iwht(cs[24]),
                forall|j: int| 0 <= j < 25 && #[trigger] bit(dcx, j) ==> acz(co@, j),
                add_blocks(cur, x as int, y as int, 4, 16, lc, b as int) == add_blocks(p1, x as int, y as int, 4, 16, lc, 0),
            decreases 16 - b,
        {
            let mut cb = block16(co, b);
            let dc = dc_known(dcx, b, &cb, Ghost(co@));
            cb[0] = dcs[b];
            proof {
                assert(ints(cb@) =~= lc[b as int]);
            }
            let bx = x + 4 * (b % 4);
            let by = y + 4 * (b / 4);
            proof { if dc { assert forall|k: int| 1 <= k < 16 implies #[trigger] cb@[k] == 0 by {} } }
            idct_add(v, w, bx, by, &cb, dc, Ghost(cur));
            proof {
                lemma_lens(cur, bx as int, by as int, 0, 0, idct(lc[b as int]), 0, 0, 0, 0, 0, Seq::empty());
                cur = add_block(cur, bx as int, by as int, idct(lc[b as int]));
            }
            b = b + 1;
        }
    }
}

/// predict_intra_chroma for one plane (`chroma`), blocks `first..first + 4`.
pub fn chroma_x(v: &mut Vec<u8>, w: usize, mbw: usize, mbx: usize, mby: usize, mode: u8, co: &[i32; 400], first: usize, dcx: u32, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), w == mbw * 8, mbx < mbw, mby * 8 + 8 <= pl.len(), mode <= 3, c16(co@),
        forall|j: int| 0 <= j < 25 && #[trigger] bit(dcx, j) ==> acz(co@, j),
        first == 16 || first == 20,
    ensures holds(final(v)@, w as nat, chroma(pl, mbx as int, mby as int, mode as nat, blocks(co@), first as int)),
        chroma(pl, mbx as int, mby as int, mode as nat, blocks(co@), first as int).len() == pl.len(),
{
    proof { reveal(chroma); }
    let x = mbx * 8;
    let y = mby * 8;
    predict_x(v, w, x, y, 8, mode, Ghost(pl));
    let ghost p1 = predict(pl, x as int, y as int, 8, mode as nat);
    proof { lemma_lens(pl, x as int, y as int, 8, mode as nat, Seq::empty(), 0, 0, 0, 0, 0, Seq::empty()); }
    let ghost cs = blocks(co@).subrange(first as int, first + 4);
    let mut b: usize = 0;
    let ghost mut cur = p1;
    while b < 4
        invariant
            holds(v@, w as nat, cur), w == mbw * 8, mbx < mbw, mby * 8 + 8 <= pl.len(), cur.len() == pl.len(), c16(co@), b <= 4,
            x == mbx * 8, y == mby * 8, first == 16 || first == 20, cs == blocks(co@).subrange(first as int, first + 4),
            forall|j: int| 0 <= j < 25 && #[trigger] bit(dcx, j) ==> acz(co@, j),
            add_blocks(cur, x as int, y as int, 2, 4, cs, b as int) == add_blocks(p1, x as int, y as int, 2, 4, cs, 0),
        decreases 4 - b,
    {
        let cb = block16(co, first + b);
        let dc = dc_known(dcx, first + b, &cb, Ghost(co@));
        proof { assert(ints(cb@) == cs[b as int]); }
        let bx = x + 4 * (b % 2);
        let by = y + 4 * (b / 2);
        idct_add(v, w, bx, by, &cb, dc, Ghost(cur));
        proof {
            lemma_lens(cur, bx as int, by as int, 0, 0, idct(cs[b as int]), 0, 0, 0, 0, 0, Seq::empty());
            cur = add_block(cur, bx as int, by as int, idct(cs[b as int]));
        }
        b = b + 1;
    }
}

} // verus!
