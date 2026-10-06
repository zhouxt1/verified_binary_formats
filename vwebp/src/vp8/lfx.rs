//! The loop filter across a horizontal edge, 16 lines at once in SSE2
//! (after libwebp's dec_sse2.c), proved to compute `spec::filter_edge`.
//!
//! The proof has three layers:
//! * the column view: `filter_line` across a horizontal edge replaces the 8
//!   pixels of its column by `c_filter` of them (`lemma_line`), so an
//!   edge's 16 lines are 16 independent columns (`lemma_edge`);
//! * lane arithmetic: the saturating 8-bit sequences libwebp uses compute
//!   `c_filter`'s integers (`lemma_*` below the column view);
//! * the vectors: each step holds lane by lane (`vsimd`'s contracts).
use vstd::prelude::*;
use super::spec::*;
use super::plane::*;
#[cfg(verus_keep_ghost)]
use vsimd::spec::{sb, ub, clamp, xor_u8, and_u8, andnot_u8, adds_i8, subs_i8, add_u8, sub_u8, avg_u8, adds_u8, max_u8, w16, sw16, put16};
#[cfg(verus_keep_ghost)]
use vsimd::x86::{byte, v8, lemma_byte};
#[cfg(verus_keep_ghost)]
use vsimd::idiom::absd8;
use vsimd::x86::__m128i;
use vsimd::x86 as sx;
use vsimd::idiom::{absdiff_epu8, le_mask_epu8, half_epu8, srai3_epi8, transpose8x8, transpose16x8, transpose16x8h};

verus! {

// ------------------------------------------------------------ column view

/// The 8 pixels of the line at column x across the horizontal edge at row
/// y, top to bottom: p3 p2 p1 p0 q0 q1 q2 q3.
pub open spec fn col(p: Plane, x: int, y: int) -> Seq<u8> { Seq::new(8, |k: int| p[y - 4 + k][x]) }

pub open spec fn c_simple(c: Seq<u8>, lim: int) -> bool {
    absd(c[3] as int, c[4] as int) * 2 + absd(c[2] as int, c[5] as int) / 2 <= lim
}

pub open spec fn c_normal(c: Seq<u8>, e: int, i: int) -> bool {
    &&& c_simple(c, 2 * e + i)
    &&& absd(c[0] as int, c[1] as int) <= i && absd(c[1] as int, c[2] as int) <= i && absd(c[2] as int, c[3] as int) <= i
    &&& absd(c[7] as int, c[6] as int) <= i && absd(c[6] as int, c[5] as int) <= i && absd(c[5] as int, c[4] as int) <= i
}

pub open spec fn c_hev(c: Seq<u8>, t: int) -> bool { absd(c[2] as int, c[3] as int) > t || absd(c[5] as int, c[4] as int) > t }

/// filter_common's `a`, and filter_mb_edge's `w` when `outer`.
pub open spec fn c_a(c: Seq<u8>, outer: bool) -> int { s8(3 * (c[4] - c[3]) + if outer { s8(c[2] - c[5]) } else { 0 }) }
pub open spec fn c_f1(a: int) -> int { (if a + 4 > 127 { 127 } else { a + 4 }) / 8 }
pub open spec fn c_f2(a: int) -> int { (if a + 3 > 127 { 127 } else { a + 3 }) / 8 }

pub open spec fn c_common(c: Seq<u8>, outer: bool) -> Seq<u8> {
    let a = c_a(c, outer);
    let c1 = c.update(3, clamp255(c[3] + c_f2(a))).update(4, clamp255(c[4] - c_f1(a)));
    if outer { c1 } else {
        let a2 = (c_f1(a) + 1) / 2;
        c1.update(2, clamp255(c[2] + a2)).update(5, clamp255(c[5] - a2))
    }
}

pub open spec fn c_mb(c: Seq<u8>) -> Seq<u8> {
    let w = s8(s8(c[2] - c[5]) + 3 * (c[4] - c[3]));
    let a0 = (27 * w + 63) / 128;
    let a1 = (18 * w + 63) / 128;
    let a2 = (9 * w + 63) / 128;
    c.update(3, clamp255(c[3] + a0)).update(4, clamp255(c[4] - a0))
     .update(2, clamp255(c[2] + a1)).update(5, clamp255(c[5] - a1))
     .update(1, clamp255(c[1] + a2)).update(6, clamp255(c[6] - a2))
}

/// `filter_line` on a column.
pub open spec fn c_filter(c: Seq<u8>, kind: int, e: int, i: int, h: int) -> Seq<u8> {
    if kind == kind_simple() {
        if c_simple(c, e) { c_common(c, true) } else { c }
    } else if kind == kind_mb() {
        if c_normal(c, e, i) { if c_hev(c, h) { c_common(c, true) } else { c_mb(c) } } else { c }
    } else {
        if c_normal(c, e, i) { c_common(c, c_hev(c, h)) } else { c }
    }
}

/// The plane with column x of rows y - 4 .. y + 4 set to `v`.
pub open spec fn set_col(p: Plane, x: int, y: int, v: Seq<u8>) -> Plane {
    Seq::new(p.len(), |r: int| if y - 4 <= r < y + 4 { p[r].update(x, v[r - y + 4]) } else { p[r] })
}

pub open spec fn rows_w(p: Plane, w: nat) -> bool { forall|r: int| 0 <= r < p.len() ==> (#[trigger] p[r]).len() == w }

proof fn lemma_setpx(p: Plane, w: nat, x: int, y: int, k: int, v: u8)
    requires rows_w(p, w), 4 <= y, y + 4 <= p.len(), 0 <= x < w, -4 <= k < 4,
    ensures setpx(p, x, y, 1, k, v) == set_col(p, x, y, col(p, x, y).update(k + 4, v)),
{
    assert(setpx(p, x, y, 1, k, v) =~~= set_col(p, x, y, col(p, x, y).update(k + 4, v)));
}

proof fn lemma_set_col2(p: Plane, w: nat, x: int, y: int, c1: Seq<u8>, c2: Seq<u8>)
    requires rows_w(p, w), 4 <= y, y + 4 <= p.len(), 0 <= x < w, c1.len() == 8, c2.len() == 8,
    ensures
        set_col(set_col(p, x, y, c1), x, y, c2) == set_col(p, x, y, c2),
        col(set_col(p, x, y, c1), x, y) == c1,
        rows_w(set_col(p, x, y, c1), w),
{
    assert(set_col(set_col(p, x, y, c1), x, y, c2) =~~= set_col(p, x, y, c2));
    assert(col(set_col(p, x, y, c1), x, y) =~= c1);
}

proof fn lemma_set_col_id(p: Plane, w: nat, x: int, y: int)
    requires rows_w(p, w), 4 <= y, y + 4 <= p.len(), 0 <= x < w,
    ensures set_col(p, x, y, col(p, x, y)) == p,
{
    assert(set_col(p, x, y, col(p, x, y)) =~~= p);
}

/// setpx on a plane already seen as a column update.
proof fn lemma_setpx_col(p0: Plane, w: nat, x: int, y: int, c: Seq<u8>, k: int, v: u8)
    requires rows_w(p0, w), 4 <= y, y + 4 <= p0.len(), 0 <= x < w, -4 <= k < 4, c.len() == 8,
    ensures setpx(set_col(p0, x, y, c), x, y, 1, k, v) == set_col(p0, x, y, c.update(k + 4, v)),
{
    let p1 = set_col(p0, x, y, c);
    lemma_set_col2(p0, w, x, y, c, c);
    lemma_setpx(p1, w, x, y, k, v);
    lemma_set_col2(p0, w, x, y, c, c.update(k + 4, v));
}

/// `filter_line` across a horizontal edge replaces its column by `c_filter`.
pub proof fn lemma_line(p: Plane, w: nat, x: int, y: int, kind: int, e: int, i: int, h: int)
    requires rows_w(p, w), 4 <= y, y + 4 <= p.len(), 0 <= x < w,
    ensures filter_line(p, x, y, 1, kind, e, i, h) == set_col(p, x, y, c_filter(col(p, x, y), kind, e, i, h)),
{
    reveal(filter_line);
    let c = col(p, x, y);
    assert forall|k: int| -4 <= k < 4 implies px(p, x, y, 1, k) == c[k + 4] as int by {}
    lemma_set_col_id(p, w, x, y);
    // Every branch is a chain of setpx from p = set_col(p, x, y, c).
    let a_t = c_a(c, true);
    let a_f = c_a(c, false);
    let ghost s = |cc: Seq<u8>| set_col(p, x, y, cc);
    // common, outer
    let ct1 = c.update(3, clamp255(c[3] + c_f2(a_t)));
    let ct2 = ct1.update(4, clamp255(c[4] - c_f1(a_t)));
    lemma_setpx_col(p, w, x, y, c, -1, clamp255(c[3] + c_f2(a_t)));
    lemma_setpx_col(p, w, x, y, ct1, 0, clamp255(c[4] - c_f1(a_t)));
    assert(common(p, x, y, 1, true) == s(ct2));
    // common, not outer
    let a2 = (c_f1(a_f) + 1) / 2;
    let cf1 = c.update(3, clamp255(c[3] + c_f2(a_f)));
    let cf2 = cf1.update(4, clamp255(c[4] - c_f1(a_f)));
    let cf3 = cf2.update(2, clamp255(c[2] + a2));
    let cf4 = cf3.update(5, clamp255(c[5] - a2));
    lemma_setpx_col(p, w, x, y, c, -1, clamp255(c[3] + c_f2(a_f)));
    lemma_setpx_col(p, w, x, y, cf1, 0, clamp255(c[4] - c_f1(a_f)));
    lemma_setpx_col(p, w, x, y, cf2, -2, clamp255(c[2] + a2));
    lemma_setpx_col(p, w, x, y, cf3, 1, clamp255(c[5] - a2));
    assert(common(p, x, y, 1, false) == s(cf4));
    // mb_edge
    let wv = s8(s8(c[2] - c[5]) + 3 * (c[4] - c[3]));
    let a0 = (27 * wv + 63) / 128;
    let a1 = (18 * wv + 63) / 128;
    let a2m = (9 * wv + 63) / 128;
    let m1 = c.update(3, clamp255(c[3] + a0));
    let m2 = m1.update(4, clamp255(c[4] - a0));
    let m3 = m2.update(2, clamp255(c[2] + a1));
    let m4 = m3.update(5, clamp255(c[5] - a1));
    let m5 = m4.update(1, clamp255(c[1] + a2m));
    let m6 = m5.update(6, clamp255(c[6] - a2m));
    lemma_setpx_col(p, w, x, y, c, -1, clamp255(c[3] + a0));
    lemma_setpx_col(p, w, x, y, m1, 0, clamp255(c[4] - a0));
    lemma_setpx_col(p, w, x, y, m2, -2, clamp255(c[2] + a1));
    lemma_setpx_col(p, w, x, y, m3, 1, clamp255(c[5] - a1));
    lemma_setpx_col(p, w, x, y, m4, -3, clamp255(c[1] + a2m));
    lemma_setpx_col(p, w, x, y, m5, 2, clamp255(c[6] - a2m));
    assert(mb_edge(p, x, y, 1) == s(m6));
    assert(c_mb(c) == m6);
    assert(c_common(c, true) == ct2);
    assert(c_common(c, false) == cf4);
}

/// The first k lines of an edge done, from the original plane: columns
/// x + k .. x + n hold `c_filter` of their original column.
pub open spec fn edge_res(p: Plane, x: int, y: int, n: int, k: int, kind: int, e: int, i: int, h: int) -> Plane {
    Seq::new(p.len(), |r: int| if y - 4 <= r < y + 4 {
        Seq::new(p[r].len(), |cc: int| if x + k <= cc < x + n { c_filter(col(p, cc, y), kind, e, i, h)[r - y + 4] } else { p[r][cc] })
    } else { p[r] })
}

/// An edge's lines are independent columns.
pub proof fn lemma_edge(p: Plane, w: nat, x: int, y: int, n: int, k: int, kind: int, e: int, i: int, h: int)
    requires rows_w(p, w), 4 <= y, y + 4 <= p.len(), 0 <= x, x + n <= w, 0 <= k <= n,
    ensures filter_edge(p, x, y, 1, n, kind, e, i, h, k) == edge_res(p, x, y, n, k, kind, e, i, h),
    decreases n - k,
{
    if k >= n {
        assert(edge_res(p, x, y, n, k, kind, e, i, h) =~~= p);
    } else {
        let cf = c_filter(col(p, x + k, y), kind, e, i, h);
        let p1 = set_col(p, x + k, y, cf);
        lemma_line(p, w, x + k, y, kind, e, i, h);
        assert(rows_w(p1, w));
        lemma_edge(p1, w, x, y, n, k + 1, kind, e, i, h);
        assert forall|cc: int| x + k < cc < x + n implies #[trigger] col(p1, cc, y) == col(p, cc, y) by {
            assert(col(p1, cc, y) =~= col(p, cc, y));
        }
        assert(edge_res(p1, x, y, n, k + 1, kind, e, i, h) =~~= edge_res(p, x, y, n, k, kind, e, i, h));
    }
}


// ------------------------------------------------ column view, vertical

/// The 8 pixels of the line at row y across the vertical edge at column
/// x, left to right: p3 .. q3.
pub open spec fn rowv(p: Plane, x: int, y: int) -> Seq<u8> { Seq::new(8, |k: int| p[y][x - 4 + k]) }

/// The plane with row y's columns x - 4 .. x + 4 set to `v`.
pub open spec fn set_rowv(p: Plane, x: int, y: int, v: Seq<u8>) -> Plane {
    p.update(y, Seq::new(p[y].len(), |cc: int| if x - 4 <= cc < x + 4 { v[cc - x + 4] } else { p[y][cc] }))
}


proof fn lemma_setpx_v(p: Plane, w: nat, x: int, y: int, k: int, v: u8)
    requires rows_w(p, w), 4 <= x, x + 4 <= w, 0 <= y < p.len(), -4 <= k < 4,
    ensures setpx(p, x, y, 0, k, v) == set_rowv(p, x, y, rowv(p, x, y).update(k + 4, v)),
{
    assert(setpx(p, x, y, 0, k, v) =~~= set_rowv(p, x, y, rowv(p, x, y).update(k + 4, v)));
}

proof fn lemma_set_rowv2_v(p: Plane, w: nat, x: int, y: int, c1: Seq<u8>, c2: Seq<u8>)
    requires rows_w(p, w), 4 <= x, x + 4 <= w, 0 <= y < p.len(), c1.len() == 8, c2.len() == 8,
    ensures
        set_rowv(set_rowv(p, x, y, c1), x, y, c2) == set_rowv(p, x, y, c2),
        rowv(set_rowv(p, x, y, c1), x, y) == c1,
        rows_w(set_rowv(p, x, y, c1), w),
{
    assert(set_rowv(set_rowv(p, x, y, c1), x, y, c2) =~~= set_rowv(p, x, y, c2));
    assert(rowv(set_rowv(p, x, y, c1), x, y) =~= c1);
}

proof fn lemma_set_rowv_id_v(p: Plane, w: nat, x: int, y: int)
    requires rows_w(p, w), 4 <= x, x + 4 <= w, 0 <= y < p.len(),
    ensures set_rowv(p, x, y, rowv(p, x, y)) == p,
{
    assert(set_rowv(p, x, y, rowv(p, x, y)) =~~= p);
}

/// setpx on a plane already seen as a row update.
proof fn lemma_setpx_rowv(p0: Plane, w: nat, x: int, y: int, c: Seq<u8>, k: int, v: u8)
    requires rows_w(p0, w), 4 <= x, x + 4 <= w, 0 <= y < p0.len(), -4 <= k < 4, c.len() == 8,
    ensures setpx(set_rowv(p0, x, y, c), x, y, 0, k, v) == set_rowv(p0, x, y, c.update(k + 4, v)),
{
    let p1 = set_rowv(p0, x, y, c);
    lemma_set_rowv2_v(p0, w, x, y, c, c);
    lemma_setpx_v(p1, w, x, y, k, v);
    lemma_set_rowv2_v(p0, w, x, y, c, c.update(k + 4, v));
}

proof fn lemma_common_v(p: Plane, w: nat, x: int, y: int, outer: bool)
    requires rows_w(p, w), 4 <= x, x + 4 <= w, 0 <= y < p.len(),
    ensures common(p, x, y, 0, outer) == set_rowv(p, x, y, c_common(rowv(p, x, y), outer)),
{
    let c = rowv(p, x, y);
    assert forall|k: int| -4 <= k < 4 implies px(p, x, y, 0, k) == c[k + 4] as int by {}
    lemma_set_rowv_id_v(p, w, x, y);
    let a = c_a(c, outer);
    let c1 = c.update(3, clamp255(c[3] + c_f2(a)));
    let c2 = c1.update(4, clamp255(c[4] - c_f1(a)));
    lemma_setpx_rowv(p, w, x, y, c, -1, clamp255(c[3] + c_f2(a)));
    lemma_setpx_rowv(p, w, x, y, c1, 0, clamp255(c[4] - c_f1(a)));
    if !outer {
        let a2 = (c_f1(a) + 1) / 2;
        let c3 = c2.update(2, clamp255(c[2] + a2));
        lemma_setpx_rowv(p, w, x, y, c2, -2, clamp255(c[2] + a2));
        lemma_setpx_rowv(p, w, x, y, c3, 1, clamp255(c[5] - a2));
    }
}

proof fn lemma_mb_v(p: Plane, w: nat, x: int, y: int)
    requires rows_w(p, w), 4 <= x, x + 4 <= w, 0 <= y < p.len(),
    ensures mb_edge(p, x, y, 0) == set_rowv(p, x, y, c_mb(rowv(p, x, y))),
{
    let c = rowv(p, x, y);
    assert forall|k: int| -4 <= k < 4 implies px(p, x, y, 0, k) == c[k + 4] as int by {}
    lemma_set_rowv_id_v(p, w, x, y);
    let wv = s8(s8(c[2] - c[5]) + 3 * (c[4] - c[3]));
    let a0 = (27 * wv + 63) / 128;
    let a1 = (18 * wv + 63) / 128;
    let a2m = (9 * wv + 63) / 128;
    let m1 = c.update(3, clamp255(c[3] + a0));
    let m2 = m1.update(4, clamp255(c[4] - a0));
    let m3 = m2.update(2, clamp255(c[2] + a1));
    let m4 = m3.update(5, clamp255(c[5] - a1));
    let m5 = m4.update(1, clamp255(c[1] + a2m));
    lemma_setpx_rowv(p, w, x, y, c, -1, clamp255(c[3] + a0));
    lemma_setpx_rowv(p, w, x, y, m1, 0, clamp255(c[4] - a0));
    lemma_setpx_rowv(p, w, x, y, m2, -2, clamp255(c[2] + a1));
    lemma_setpx_rowv(p, w, x, y, m3, 1, clamp255(c[5] - a1));
    lemma_setpx_rowv(p, w, x, y, m4, -3, clamp255(c[1] + a2m));
    lemma_setpx_rowv(p, w, x, y, m5, 2, clamp255(c[6] - a2m));
}

/// `filter_line` across a vertical edge replaces its row's 8 pixels by `c_filter`.
pub proof fn lemma_line_v(p: Plane, w: nat, x: int, y: int, kind: int, e: int, i: int, h: int)
    requires rows_w(p, w), 4 <= x, x + 4 <= w, 0 <= y < p.len(),
    ensures filter_line(p, x, y, 0, kind, e, i, h) == set_rowv(p, x, y, c_filter(rowv(p, x, y), kind, e, i, h)),
{
    reveal(filter_line);
    let c = rowv(p, x, y);
    assert forall|k: int| -4 <= k < 4 implies px(p, x, y, 0, k) == c[k + 4] as int by {}
    lemma_set_rowv_id_v(p, w, x, y);
    lemma_common_v(p, w, x, y, true);
    lemma_common_v(p, w, x, y, false);
    lemma_mb_v(p, w, x, y);
    assert(simple_threshold(p, x, y, 0, e) == c_simple(c, e));
    assert(normal_threshold(p, x, y, 0, e, i) == c_normal(c, e, i));
    assert(hev(p, x, y, 0, h) == c_hev(c, h));
}

/// The lines y + k .. y + n of a vertical edge done, from the original
/// plane: those rows' pixels x - 4 .. x + 4 hold `c_filter` of their line.
pub open spec fn edge_res_v(p: Plane, x: int, y: int, n: int, k: int, kind: int, e: int, i: int, h: int) -> Plane {
    Seq::new(p.len(), |r: int| if y + k <= r < y + n {
        Seq::new(p[r].len(), |cc: int| if x - 4 <= cc < x + 4 { c_filter(rowv(p, x, r), kind, e, i, h)[cc - x + 4] } else { p[r][cc] })
    } else { p[r] })
}

/// A vertical edge's lines are independent rows.
pub proof fn lemma_edge_v(p: Plane, w: nat, x: int, y: int, n: int, k: int, kind: int, e: int, i: int, h: int)
    requires rows_w(p, w), 4 <= x, x + 4 <= w, 0 <= y, y + n <= p.len(), 0 <= k <= n,
    ensures filter_edge(p, x, y, 0, n, kind, e, i, h, k) == edge_res_v(p, x, y, n, k, kind, e, i, h),
    decreases n - k,
{
    if k >= n {
        assert(edge_res_v(p, x, y, n, k, kind, e, i, h) =~~= p);
    } else {
        let cf = c_filter(rowv(p, x, y + k), kind, e, i, h);
        let p1 = set_rowv(p, x, y + k, cf);
        lemma_line_v(p, w, x, y + k, kind, e, i, h);
        assert(rows_w(p1, w));
        lemma_edge_v(p1, w, x, y, n, k + 1, kind, e, i, h);
        assert forall|r: int| y + k < r < y + n implies #[trigger] rowv(p1, x, r) == rowv(p, x, r) by {
            assert(rowv(p1, x, r) =~= rowv(p, x, r));
        }
        assert(edge_res_v(p1, x, y, n, k + 1, kind, e, i, h) =~~= edge_res_v(p, x, y, n, k, kind, e, i, h));
    }
}

// ------------------------------------------------------- lane arithmetic
//
// One lane of libwebp's SSE2 filters, as spec functions of bytes built from
// vsimd's lane operations, in the pieces the vector code computes. Pixels
// are handled in flipped form (x ^ 0x80, the signed byte x - 128).

/// The base delta byte: s8(3 (q0 - p0) + t), t = s8(p1 - q1) where `nh`
/// is 0 and 0 where it is 255.
pub open spec fn delta(p1: u8, p0: u8, q0: u8, q1: u8, nh: u8) -> u8 {
    let d = subs_i8(xor_u8(q0, 128), xor_u8(p0, 128));
    let t1 = andnot_u8(nh, subs_i8(xor_u8(p1, 128), xor_u8(q1, 128)));
    adds_i8(adds_i8(adds_i8(t1, d), d), d)
}

/// A pixel adjusted by the signed byte d, through its flipped form.
pub open spec fn adj_p(p: u8, d: u8) -> u8 { xor_u8(adds_i8(xor_u8(p, 128), d), 128) }
pub open spec fn adj_q(q: u8, d: u8) -> u8 { xor_u8(subs_i8(xor_u8(q, 128), d), 128) }
pub open spec fn adj_p2(p: u8, d1: u8, d2: u8) -> u8 { xor_u8(adds_i8(adds_i8(xor_u8(p, 128), d1), d2), 128) }
pub open spec fn adj_q2(q: u8, d1: u8, d2: u8) -> u8 { xor_u8(subs_i8(subs_i8(xor_u8(q, 128), d1), d2), 128) }

/// (f + k) >> 3, saturated, of a signed byte f.
pub open spec fn sh3(f: u8, k: u8) -> u8 { ub(sb(adds_i8(f, k)) / 8) }

/// libwebp's signed (f + 1) >> 1: an unsigned average, offset.
pub open spec fn half1(f: u8) -> u8 { sub_u8(avg_u8(add_u8(f, 128), 0), 64) }

/// One of DoFilter6's taps: (c * f + 63) >> 7 of a signed byte f.
pub open spec fn tap(c: int, f: u8) -> u8 { ub((c * sb(f) + 63) / 128) }

/// One lane of the 4-pixel filter (libwebp's DoFilter4 and DoFilter2):
/// p1 p0 q0 q1 in, their new values out. `mask`: 255 where the line is
/// filtered; `nh`: 255 where p1 and q1 are adjusted too (no high edge
/// variance, and not the simple filter).
pub open spec fn lane4(p1: u8, p0: u8, q0: u8, q1: u8, mask: u8, nh: u8) -> Seq<u8> {
    let t = and_u8(delta(p1, p0, q0, q1, nh), mask);
    let f1 = sh3(t, 4);
    let a2 = and_u8(nh, half1(f1));
    seq![adj_p(p1, a2), adj_p(p0, sh3(t, 3)), adj_q(q0, f1), adj_q(q1, a2)]
}

/// One lane of the 6-pixel filter (libwebp's DoFilter6): p2 .. q2 in,
/// their new values out. Where the edge variance is high, p0 and q0 get
/// the simple filter (`fa`); elsewhere all six get the taps of `fb`.
pub open spec fn lane6(p2: u8, p1: u8, p0: u8, q0: u8, q1: u8, q2: u8, mask: u8, nh: u8) -> Seq<u8> {
    let a = delta(p1, p0, q0, q1, 0);
    let fa = and_u8(a, andnot_u8(nh, mask));
    let fb = and_u8(a, and_u8(nh, mask));
    seq![adj_p(p2, tap(9, fb)), adj_p(p1, tap(18, fb)), adj_p2(p0, sh3(fa, 3), tap(27, fb)),
         adj_q2(q0, sh3(fa, 4), tap(27, fb)), adj_q(q1, tap(18, fb)), adj_q(q2, tap(9, fb))]
}

pub proof fn lemma_flip(x: u8)
    ensures sb(xor_u8(x, 128)) == x as int - 128,
{
    assert(x ^ 128u8 == if x < 128 { (x + 128) as u8 } else { (x - 128) as u8 }) by (bit_vector);
}

/// Back from signed: the byte of v, sign flipped, is v + 128.
pub proof fn lemma_unflip(v: int)
    requires -128 <= v <= 127,
    ensures xor_u8(ub(v), 128) as int == v + 128,
{
    let b = ub(v);
    assert(b ^ 128u8 == if b < 128 { (b + 128) as u8 } else { (b - 128) as u8 }) by (bit_vector);
}

pub proof fn lemma_sb_ub(v: int)
    requires -128 <= v <= 127,
    ensures sb(ub(v)) == v,
{}

pub proof fn lemma_ub_sb(x: u8)
    ensures ub(sb(x)) == x, -128 <= sb(x) <= 127,
{}

/// Three saturating additions of the saturated d are one saturated t + 3D.
pub proof fn lemma_sat3(t: int, dd: int)
    requires -128 <= t <= 127, -255 <= dd <= 255,
    ensures ({
        let d = clamp(dd, -128, 127);
        clamp(clamp(clamp(t + d, -128, 127) + d, -128, 127) + d, -128, 127) == clamp(t + 3 * dd, -128, 127)
    }),
{}

pub proof fn lemma_half1(f: int)
    requires -16 <= f <= 15,
    ensures half1(ub(f)) == ub((f + 1) / 2), -8 <= (f + 1) / 2 <= 8,
{
    let x = add_u8(ub(f), 128);
    assert(x as int == f + 128);
    let y = avg_u8(x, 0);
    assert(y as int == (f + 129) / 2);
    assert(sb(sub_u8(y, 64)) == (f + 129) / 2 - 64);
    lemma_ub_sb(sub_u8(y, 64));
}

pub proof fn lemma_mask(x: u8, m: u8)
    requires m == 0 || m == 255,
    ensures and_u8(x, m) == if m == 255 { x } else { 0 }, andnot_u8(m, x) == if m == 255 { 0 } else { x },
        and_u8(m, x) == if m == 255 { x } else { 0 },
{
    vsimd::idiom::lemma_and_mask(x);
}

pub proof fn lemma_masks2(a: u8, b: u8)
    requires a == 0 || a == 255, b == 0 || b == 255,
    ensures andnot_u8(a, b) == if a == 0 && b == 255 { 255u8 } else { 0u8 },
        and_u8(a, b) == if a == 255 && b == 255 { 255u8 } else { 0u8 },
{
    vsimd::idiom::lemma_and_mask(a);
    vsimd::idiom::lemma_and_mask(b);
}

pub proof fn lemma_delta(p1: u8, p0: u8, q0: u8, q1: u8, nh: u8)
    requires nh == 0 || nh == 255,
    ensures delta(p1, p0, q0, q1, nh) == ub(s8(3 * (q0 - p0) + if nh == 0 { s8(p1 - q1) } else { 0 })),
{
    lemma_flip(p1); lemma_flip(p0); lemma_flip(q0); lemma_flip(q1);
    let d = subs_i8(xor_u8(q0, 128), xor_u8(p0, 128));
    let t0 = subs_i8(xor_u8(p1, 128), xor_u8(q1, 128));
    lemma_sb_ub(clamp(q0 - p0, -128, 127));
    lemma_sb_ub(clamp(p1 - q1, -128, 127));
    lemma_mask(t0, nh);
    let t1 = andnot_u8(nh, t0);
    let tv = if nh == 0 { s8(p1 - q1) } else { 0 };
    assert(sb(t1) == tv);
    let dv = clamp(q0 - p0, -128, 127);
    assert(sb(d) == dv);
    let u1 = adds_i8(t1, d);
    lemma_sb_ub(clamp(tv + dv, -128, 127));
    let u2 = adds_i8(u1, d);
    lemma_sb_ub(clamp(sb(u1) + dv, -128, 127));
    lemma_sb_ub(clamp(sb(u2) + dv, -128, 127));
    lemma_sat3(tv, q0 - p0);
}

/// Adding a signed amount to a flipped pixel and flipping back is clamp255.
pub proof fn lemma_adj(p: u8, v: int)
    requires -128 <= v <= 127,
    ensures adj_p(p, ub(v)) == clamp255(p + v), adj_q(p, ub(v)) == clamp255(p - v),
{
    lemma_flip(p);
    lemma_sb_ub(v);
    lemma_unflip(clamp(p - 128 + v, -128, 127));
    lemma_unflip(clamp(p - 128 - v, -128, 127));
}

/// Two adjustments, one of them zero.
pub proof fn lemma_adj2(p: u8, v1: int, v2: int)
    requires -128 <= v1 <= 127, -128 <= v2 <= 127, v1 == 0 || v2 == 0,
    ensures adj_p2(p, ub(v1), ub(v2)) == clamp255(p + v1 + v2), adj_q2(p, ub(v1), ub(v2)) == clamp255(p - v1 - v2),
{
    lemma_flip(p);
    lemma_sb_ub(v1);
    lemma_sb_ub(v2);
    lemma_sb_ub(clamp(p - 128 + v1, -128, 127));
    lemma_sb_ub(clamp(p - 128 - v1, -128, 127));
    lemma_unflip(clamp(clamp(p - 128 + v1, -128, 127) + v2, -128, 127));
    lemma_unflip(clamp(clamp(p - 128 - v1, -128, 127) - v2, -128, 127));
}

pub proof fn lemma_sh3(v: int)
    requires -128 <= v <= 127,
    ensures sh3(ub(v), 3) == ub(c_f2(v)), sh3(ub(v), 4) == ub(c_f1(v)),
        -16 <= c_f1(v) <= 15, -16 <= c_f2(v) <= 15,
{
    lemma_sb_ub(v);
    lemma_sb_ub(3);
    lemma_sb_ub(4);
}

pub proof fn lemma_tap(v: int)
    requires -128 <= v <= 127,
    ensures tap(27, ub(v)) == ub((27 * v + 63) / 128), tap(18, ub(v)) == ub((18 * v + 63) / 128), tap(9, ub(v)) == ub((9 * v + 63) / 128),
        -27 <= (27 * v + 63) / 128 <= 27, -18 <= (18 * v + 63) / 128 <= 18, -9 <= (9 * v + 63) / 128 <= 9,
{
    lemma_sb_ub(v);
}

pub proof fn lemma_s8(x: int)
    ensures -128 <= s8(x) <= 127, s8(x) == clamp(x, -128, 127),
{}

/// `lane4` is `c_filter` for the subblock and simple filters.
pub proof fn lemma_lane4(c: Seq<u8>, kind: int, e: int, i: int, h: int, mask: u8, nh: u8)
    requires c.len() == 8, kind == 1 || kind == 2,
        mask == if (if kind == 2 { c_simple(c, e) } else { c_normal(c, e, i) }) { 255u8 } else { 0u8 },
        nh == if kind == 1 && !c_hev(c, h) { 255u8 } else { 0u8 },
    ensures lane4(c[2], c[3], c[4], c[5], mask, nh) == c_filter(c, kind, e, i, h).subrange(2, 6),
{
    hide(delta); hide(adj_p); hide(adj_q); hide(sh3); hide(half1); hide(clamp255);
    hide(and_u8); hide(andnot_u8); hide(ub); hide(sb);
    let (p1, p0, q0, q1) = (c[2], c[3], c[4], c[5]);
    let outer = nh == 0;
    let filt = mask == 255;
    let a = c_a(c, outer);
    lemma_s8(3 * (q0 - p0) + if outer { s8(p1 - q1) } else { 0 });
    lemma_delta(p1, p0, q0, q1, nh);
    let av = if filt { a } else { 0 };
    lemma_mask(delta(p1, p0, q0, q1, nh), mask);
    let t = and_u8(delta(p1, p0, q0, q1, nh), mask);
    assert(t == ub(av)) by { reveal(ub); }
    lemma_sh3(av);
    let f1v = c_f1(av);
    lemma_half1(f1v);
    let hv = (f1v + 1) / 2;
    lemma_mask(half1(ub(f1v)), nh);
    let a2v = if nh == 255 { hv } else { 0 };
    assert(and_u8(nh, half1(sh3(t, 4))) == ub(a2v)) by { reveal(ub); }
    lemma_adj(p1, a2v);
    lemma_adj(q1, a2v);
    lemma_adj(p0, c_f2(av));
    lemma_adj(q0, f1v);
    if !filt {
        assert(c_f1(0) == 0 && c_f2(0) == 0 && (0int + 1) / 2 == 0);
        assert(clamp255(p1 + 0) == p1 && clamp255(q1 - 0) == q1 && clamp255(p0 + 0) == p0 && clamp255(q0 - 0) == q0) by { reveal(clamp255); }
    } else if outer {
        assert(clamp255(p1 + 0) == p1 && clamp255(q1 - 0) == q1) by { reveal(clamp255); }
    }
    let out = lane4(p1, p0, q0, q1, mask, nh);
    let cf = c_filter(c, kind, e, i, h);
    assert(out =~= cf.subrange(2, 6));
}

/// `lane6` is `c_filter` for the macroblock-edge filter.
pub proof fn lemma_lane6(c: Seq<u8>, e: int, i: int, h: int, mask: u8, nh: u8)
    requires c.len() == 8,
        mask == if c_normal(c, e, i) { 255u8 } else { 0u8 },
        nh == if !c_hev(c, h) { 255u8 } else { 0u8 },
    ensures lane6(c[1], c[2], c[3], c[4], c[5], c[6], mask, nh) == c_filter(c, kind_mb(), e, i, h).subrange(1, 7),
{
    hide(delta); hide(adj_p); hide(adj_q); hide(adj_p2); hide(adj_q2); hide(sh3); hide(tap); hide(clamp255);
    hide(and_u8); hide(andnot_u8); hide(ub); hide(sb);
    let (p2, p1, p0, q0, q1, q2) = (c[1], c[2], c[3], c[4], c[5], c[6]);
    let wv = c_a(c, true);
    lemma_s8(3 * (q0 - p0) + s8(p1 - q1));
    lemma_delta(p1, p0, q0, q1, 0);
    let a = delta(p1, p0, q0, q1, 0);
    let filt = mask == 255;
    let hev = nh == 0;
    lemma_masks2(nh, mask);
    lemma_mask(a, andnot_u8(nh, mask));
    lemma_mask(a, and_u8(nh, mask));
    let av = if filt && hev { wv } else { 0 };
    let bv = if filt && !hev { wv } else { 0 };
    let fa = and_u8(a, andnot_u8(nh, mask));
    let fb = and_u8(a, and_u8(nh, mask));
    assert(fa == ub(av) && fb == ub(bv)) by { reveal(ub); }
    lemma_sh3(av);
    lemma_tap(bv);
    let (a0, a1, a2) = ((27 * bv + 63) / 128, (18 * bv + 63) / 128, (9 * bv + 63) / 128);
    lemma_adj(p2, a2);
    lemma_adj(q2, a2);
    lemma_adj(p1, a1);
    lemma_adj(q1, a1);
    if filt && hev {
        assert(a0 == 0 && a1 == 0 && a2 == 0);
    } else {
        assert(av == 0 && c_f1(0) == 0 && c_f2(0) == 0);
    }
    lemma_adj2(p0, c_f2(av), a0);
    lemma_adj2(q0, c_f1(av), a0);
    assert(wv == s8(s8(c[2] - c[5]) + 3 * (c[4] - c[3])));
    if !filt || hev {
        assert(clamp255(p2 + 0) == p2 && clamp255(q2 - 0) == q2 && clamp255(p1 + 0) == p1 && clamp255(q1 - 0) == q1) by { reveal(clamp255); }
        if !filt {
            assert(clamp255(p0 + 0 + 0) == p0 && clamp255(q0 - 0 - 0) == q0) by { reveal(clamp255); }
        }
    }
    let out = lane6(p2, p1, p0, q0, q1, q2, mask, nh);
    let cf = c_filter(c, kind_mb(), e, i, h);
    assert(out =~= cf.subrange(1, 7));
}


// ------------------------------------------------------------- vectors

/// Lane j's column: p3 .. q3.
pub open spec fn lc(p3: __m128i, p2: __m128i, p1: __m128i, p0: __m128i, q0: __m128i, q1: __m128i, q2: __m128i, q3: __m128i, j: int) -> Seq<u8> {
    seq![byte(p3, j), byte(p2, j), byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(q2, j), byte(q3, j)]
}

/// Whether the filter applies to a column.
pub open spec fn c_thr(c: Seq<u8>, kind: int, e: int, i: int) -> bool {
    if kind == kind_simple() { c_simple(c, e) } else { c_normal(c, e, i) }
}

proof fn lemma_edge_test(t4: int, t3: int, lim: int)
    requires 0 <= t4 <= 255, 0 <= t3 <= 127, 0 <= lim <= 254,
    ensures (adds_u8(adds_u8(t4 as u8, t4 as u8), t3 as u8) <= lim as u8) == (t4 * 2 + t3 <= lim),
{}

/// The filter mask (255 where the line is filtered) and the not-hev mask
/// (255 where p1 and q1 are adjusted), per lane.
fn masks(p3: __m128i, p2: __m128i, p1: __m128i, p0: __m128i, q0: __m128i, q1: __m128i, q2: __m128i, q3: __m128i,
    kind: u8, e: i32, i: i32, h: i32) -> (r: (__m128i, __m128i))
    requires kind <= 2, 0 <= e, 0 <= i <= 255, 0 <= h <= 255, (if kind == 2 { e as int } else { 2 * e + i }) <= 254,
    ensures forall|j: int| 0 <= j < 16 ==> {
        let c = lc(p3, p2, p1, p0, q0, q1, q2, q3, j);
        &&& #[trigger] byte(r.0, j) == if c_thr(c, kind as int, e as int, i as int) { 255u8 } else { 0u8 }
        &&& byte(r.1, j) == if kind != 2 && !c_hev(c, h as int) { 255u8 } else { 0u8 }
    },
{
    broadcast use lemma_byte;
    let lim = if kind == 2 { e } else { 2 * e + i };
    let t1 = absdiff_epu8(p1, q1);
    let t3 = half_epu8(t1);
    let t4 = absdiff_epu8(p0, q0);
    let t6 = sx::adds_epu8(sx::adds_epu8(t4, t4), t3);
    let lv = sx::set1_epi8(lim as u8);
    let edge = le_mask_epu8(t6, lv);
    let d_p10 = absdiff_epu8(p1, p0);
    let d_q10 = absdiff_epu8(q1, q0);
    if kind == 2 {
        let z = sx::setzero();
        proof {
            assert forall|j: int| 0 <= j < 16 implies #[trigger] byte(edge, j) == if c_thr(lc(p3, p2, p1, p0, q0, q1, q2, q3, j), kind as int, e as int, i as int) { 255u8 } else { 0u8 } by {
                lemma_edge_test(absd8(byte(p0, j), byte(q0, j)), absd8(byte(p1, j), byte(q1, j)) / 2, lim as int);
                assert(byte(t1, j) as int == absd8(byte(p1, j), byte(q1, j)));
            }
        }
        (edge, z)
    } else {
        let hv = sx::max_epu8(d_p10, d_q10);
        let nh = le_mask_epu8(hv, sx::set1_epi8(h as u8));
        let m = sx::max_epu8(sx::max_epu8(sx::max_epu8(absdiff_epu8(p3, p2), absdiff_epu8(p2, p1)), sx::max_epu8(d_p10, absdiff_epu8(q3, q2))),
                             sx::max_epu8(absdiff_epu8(q2, q1), d_q10));
        let inner = le_mask_epu8(m, sx::set1_epi8(i as u8));
        let mask = sx::and_si128(inner, edge);
        proof {
            assert forall|j: int| 0 <= j < 16 implies {
                let c = lc(p3, p2, p1, p0, q0, q1, q2, q3, j);
                &&& #[trigger] byte(mask, j) == if c_thr(c, kind as int, e as int, i as int) { 255u8 } else { 0u8 }
                &&& byte(nh, j) == if kind != 2 && !c_hev(c, h as int) { 255u8 } else { 0u8 }
            } by {
                lemma_edge_test(absd8(byte(p0, j), byte(q0, j)), absd8(byte(p1, j), byte(q1, j)) / 2, lim as int);
                assert(byte(t1, j) as int == absd8(byte(p1, j), byte(q1, j)));
                lemma_masks2(byte(inner, j), byte(edge, j));
            }
        }
        (mask, nh)
    }
}

/// The 4-pixel filter on four rows of 16 lines (`lane4` in each lane).
fn filter4(p1: __m128i, p0: __m128i, q0: __m128i, q1: __m128i, mask: __m128i, nh: __m128i) -> (r: (__m128i, __m128i, __m128i, __m128i))
    ensures forall|j: int| 0 <= j < 16 ==> {
        let l = lane4(byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(mask, j), byte(nh, j));
        &&& #[trigger] byte(r.0, j) == l[0] && byte(r.1, j) == l[1] && byte(r.2, j) == l[2] && byte(r.3, j) == l[3]
    },
{
    broadcast use lemma_byte;
    let sbit = sx::set1_epi8(0x80);
    let fp1 = sx::xor_si128(p1, sbit);
    let fp0 = sx::xor_si128(p0, sbit);
    let fq0 = sx::xor_si128(q0, sbit);
    let fq1 = sx::xor_si128(q1, sbit);
    let d = sx::subs_epi8(fq0, fp0);
    let t = sx::andnot_si128(nh, sx::subs_epi8(fp1, fq1));
    let t = sx::adds_epi8(sx::adds_epi8(sx::adds_epi8(t, d), d), d);
    let t = sx::and_si128(t, mask);
    let f2 = srai3_epi8(sx::adds_epi8(t, sx::set1_epi8(3)));
    let f1 = srai3_epi8(sx::adds_epi8(t, sx::set1_epi8(4)));
    let o0 = sx::xor_si128(sx::adds_epi8(fp0, f2), sbit);
    let n0 = sx::xor_si128(sx::subs_epi8(fq0, f1), sbit);
    let a2 = sx::sub_epi8(sx::avg_epu8(sx::add_epi8(f1, sbit), sx::setzero()), sx::set1_epi8(64));
    let a2 = sx::and_si128(nh, a2);
    let o1 = sx::xor_si128(sx::adds_epi8(fp1, a2), sbit);
    let n1 = sx::xor_si128(sx::subs_epi8(fq1, a2), sbit);
    (o1, o0, n0, n1)
}

/// One 16-bit lane of `taps`: f << 8, times 9 << 8 (high half), plus 63,
/// summed three times, each shifted right by 7.
proof fn lemma_taps_lane(lo: Seq<u8>, k9: Seq<u8>, k63: Seq<u8>, f9: Seq<u8>, a2: Seq<u8>, a1: Seq<u8>, a0: Seq<u8>,
    s2: Seq<u8>, s1: Seq<u8>, s0: Seq<u8>, l: int, s: int)
    requires 0 <= l < 8, -128 <= s <= 127, lo.len() == 16,
        lo[2 * l] == 0, lo[2 * l + 1] == ub(s),
        k9 == vsimd::spec::set1_epi16(0x0900), k63 == vsimd::spec::set1_epi16(63),
        f9 == vsimd::spec::mulhi_epi16(lo, k9), a2 == vsimd::spec::add_epi16(f9, k63),
        a1 == vsimd::spec::add_epi16(a2, f9), a0 == vsimd::spec::add_epi16(a1, f9),
        s0 == vsimd::spec::srai_epi16(a0, 7), s1 == vsimd::spec::srai_epi16(a1, 7), s2 == vsimd::spec::srai_epi16(a2, 7),
    ensures sw16(s0, l) == (27 * s + 63) / 128, sw16(s1, l) == (18 * s + 63) / 128, sw16(s2, l) == (9 * s + 63) / 128,
{
    use vsimd::spec::{lemma_rt16, lemma_put16_mod};
    vstd::arithmetic::power2::lemma2_to64();
    let (e, o) = (2 * l, 2 * l + 1);
    assert(e / 2 == l && o / 2 == l && e % 2 == 0 && o % 2 == 1);
    assert(sw16(lo, l) == 256 * s);
    lemma_rt16(k9, l, 2304);
    lemma_rt16(k63, l, 63);
    assert(256 * s * 2304 / 65536 == 9 * s);
    lemma_rt16(f9, l, 9 * s);
    lemma_put16_mod(w16(f9, l) + w16(k63, l), 9 * s + 63, e);
    lemma_put16_mod(w16(f9, l) + w16(k63, l), 9 * s + 63, o);
    lemma_rt16(a2, l, 9 * s + 63);
    lemma_put16_mod(w16(a2, l) + w16(f9, l), 18 * s + 63, e);
    lemma_put16_mod(w16(a2, l) + w16(f9, l), 18 * s + 63, o);
    lemma_rt16(a1, l, 18 * s + 63);
    lemma_put16_mod(w16(a1, l) + w16(f9, l), 27 * s + 63, e);
    lemma_put16_mod(w16(a1, l) + w16(f9, l), 27 * s + 63, o);
    lemma_rt16(a0, l, 27 * s + 63);
    lemma_rt16(s0, l, (27 * s + 63) / 128);
    lemma_rt16(s1, l, (18 * s + 63) / 128);
    lemma_rt16(s2, l, (9 * s + 63) / 128);
}

/// `lemma_taps_lane` for the 8 lanes of one half (`off` 0 or 8) of f.
proof fn lemma_taps_half(f: Seq<u8>, fx: Seq<u8>, k9: Seq<u8>, k63: Seq<u8>, f9: Seq<u8>, a2: Seq<u8>, a1: Seq<u8>, a0: Seq<u8>,
    s2: Seq<u8>, s1: Seq<u8>, s0: Seq<u8>, off: int)
    requires f.len() == 16, fx.len() == 16, off == 0 || off == 8,
        forall|l: int| 0 <= l < 8 ==> fx[2 * l] == 0 && #[trigger] fx[2 * l + 1] == f[off + l],
        k9 == vsimd::spec::set1_epi16(0x0900), k63 == vsimd::spec::set1_epi16(63),
        f9 == vsimd::spec::mulhi_epi16(fx, k9), a2 == vsimd::spec::add_epi16(f9, k63),
        a1 == vsimd::spec::add_epi16(a2, f9), a0 == vsimd::spec::add_epi16(a1, f9),
        s0 == vsimd::spec::srai_epi16(a0, 7), s1 == vsimd::spec::srai_epi16(a1, 7), s2 == vsimd::spec::srai_epi16(a2, 7),
    ensures
        forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(s0, l) == (27 * sb(f[off + l]) + 63) / 128,
        forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(s1, l) == (18 * sb(f[off + l]) + 63) / 128,
        forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(s2, l) == (9 * sb(f[off + l]) + 63) / 128,
{
    hide(sw16); hide(w16); hide(put16);
    assert forall|l: int| 0 <= l < 8 implies
        sw16(s0, l) == (27 * sb(f[off + l]) + 63) / 128 && sw16(s1, l) == (18 * sb(f[off + l]) + 63) / 128
            && sw16(s2, l) == (9 * sb(f[off + l]) + 63) / 128 by {
        lemma_ub_sb(f[off + l]);
        assert(fx[2 * l + 1] == f[off + l]);
        lemma_taps_lane(fx, k9, k63, f9, a2, a1, a0, s2, s1, s0, l, sb(f[off + l]));
    }
}

/// The three taps packed back to bytes.
proof fn lemma_taps_pack(f: Seq<u8>, s0lo: Seq<u8>, s0hi: Seq<u8>, s1lo: Seq<u8>, s1hi: Seq<u8>, s2lo: Seq<u8>, s2hi: Seq<u8>,
    d0: Seq<u8>, d1: Seq<u8>, d2: Seq<u8>)
    requires f.len() == 16,
        forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(s0lo, l) == (27 * sb(f[l]) + 63) / 128,
        forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(s1lo, l) == (18 * sb(f[l]) + 63) / 128,
        forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(s2lo, l) == (9 * sb(f[l]) + 63) / 128,
        forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(s0hi, l) == (27 * sb(f[8 + l]) + 63) / 128,
        forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(s1hi, l) == (18 * sb(f[8 + l]) + 63) / 128,
        forall|l: int| 0 <= l < 8 ==> #[trigger] sw16(s2hi, l) == (9 * sb(f[8 + l]) + 63) / 128,
        d0 == vsimd::spec::packs_epi16(s0lo, s0hi), d1 == vsimd::spec::packs_epi16(s1lo, s1hi), d2 == vsimd::spec::packs_epi16(s2lo, s2hi),
    ensures
        forall|j: int| 0 <= j < 16 ==> #[trigger] d0[j] == tap(27, f[j]),
        forall|j: int| 0 <= j < 16 ==> #[trigger] d1[j] == tap(18, f[j]),
        forall|j: int| 0 <= j < 16 ==> #[trigger] d2[j] == tap(9, f[j]),
{
    hide(sw16); hide(w16); hide(put16);
    assert forall|j: int| 0 <= j < 16 implies d0[j] == tap(27, f[j]) && d1[j] == tap(18, f[j]) && d2[j] == tap(9, f[j]) by {
        let s = sb(f[j]);
        lemma_ub_sb(f[j]);
        lemma_tap(s);
        if j < 8 {
            assert(sw16(s0lo, j) == (27 * s + 63) / 128);
            assert(sw16(s1lo, j) == (18 * s + 63) / 128);
            assert(sw16(s2lo, j) == (9 * s + 63) / 128);
        } else {
            assert(8 + (j - 8) == j);
            assert(sw16(s0hi, j - 8) == (27 * s + 63) / 128);
            assert(sw16(s1hi, j - 8) == (18 * s + 63) / 128);
            assert(sw16(s2hi, j - 8) == (9 * s + 63) / 128);
        }
        assert(f[j] == ub(s));
    }
}

/// DoFilter6's three taps of a vector of signed bytes f, in 16-bit lanes:
/// f * 9 as the high half of (f << 8) * (9 << 8), then + 63, and >> 7.
fn taps(f: __m128i) -> (r: (__m128i, __m128i, __m128i))
    ensures
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r.0, j) == tap(27, byte(f, j)),
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r.1, j) == tap(18, byte(f, j)),
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r.2, j) == tap(9, byte(f, j)),
{
    let z = sx::setzero();
    let k9 = sx::set1_epi16(0x0900);
    let k63 = sx::set1_epi16(63);
    let flo = sx::unpacklo_epi8(z, f);
    let fhi = sx::unpackhi_epi8(z, f);
    let f9lo = sx::mulhi_epi16(flo, k9);
    let f9hi = sx::mulhi_epi16(fhi, k9);
    let a2lo = sx::add_epi16(f9lo, k63);
    let a2hi = sx::add_epi16(f9hi, k63);
    let a1lo = sx::add_epi16(a2lo, f9lo);
    let a1hi = sx::add_epi16(a2hi, f9hi);
    let a0lo = sx::add_epi16(a1lo, f9lo);
    let a0hi = sx::add_epi16(a1hi, f9hi);
    let s0lo = sx::srai_epi16_7(a0lo);
    let s0hi = sx::srai_epi16_7(a0hi);
    let s1lo = sx::srai_epi16_7(a1lo);
    let s1hi = sx::srai_epi16_7(a1hi);
    let s2lo = sx::srai_epi16_7(a2lo);
    let s2hi = sx::srai_epi16_7(a2hi);
    let d0 = sx::packs_epi16(s0lo, s0hi);
    let d1 = sx::packs_epi16(s1lo, s1hi);
    let d2 = sx::packs_epi16(s2lo, s2hi);
    proof {
        assert forall|l: int| 0 <= l < 8 implies v8(flo)[2 * l] == 0 && #[trigger] v8(flo)[2 * l + 1] == v8(f)[0 + l] by {
            assert((2 * l) % 2 == 0 && (2 * l + 1) % 2 == 1 && (2 * l) / 2 == l && (2 * l + 1) / 2 == l);
        }
        assert forall|l: int| 0 <= l < 8 implies v8(fhi)[2 * l] == 0 && #[trigger] v8(fhi)[2 * l + 1] == v8(f)[8 + l] by {
            assert((2 * l) % 2 == 0 && (2 * l + 1) % 2 == 1 && (2 * l) / 2 == l && (2 * l + 1) / 2 == l);
        }
        lemma_taps_half(v8(f), v8(flo), v8(k9), v8(k63), v8(f9lo), v8(a2lo), v8(a1lo), v8(a0lo), v8(s2lo), v8(s1lo), v8(s0lo), 0);
        lemma_taps_half(v8(f), v8(fhi), v8(k9), v8(k63), v8(f9hi), v8(a2hi), v8(a1hi), v8(a0hi), v8(s2hi), v8(s1hi), v8(s0hi), 8);
        assert forall|l: int| 0 <= l < 8 implies sw16(v8(s0lo), l) == (27 * sb(v8(f)[l]) + 63) / 128
            && sw16(v8(s1lo), l) == (18 * sb(v8(f)[l]) + 63) / 128 && sw16(v8(s2lo), l) == (9 * sb(v8(f)[l]) + 63) / 128 by {
            assert(0 + l == l);
            assert(sw16(v8(s0lo), l) == (27 * sb(v8(f)[0 + l]) + 63) / 128);
            assert(sw16(v8(s1lo), l) == (18 * sb(v8(f)[0 + l]) + 63) / 128);
            assert(sw16(v8(s2lo), l) == (9 * sb(v8(f)[0 + l]) + 63) / 128);
        }
        lemma_taps_pack(v8(f), v8(s0lo), v8(s0hi), v8(s1lo), v8(s1hi), v8(s2lo), v8(s2hi), v8(d0), v8(d1), v8(d2));
        assert forall|j: int| 0 <= j < 16 implies
            byte(d0, j) == tap(27, byte(f, j)) && byte(d1, j) == tap(18, byte(f, j)) && byte(d2, j) == tap(9, byte(f, j)) by {
            lemma_byte(d0, j); lemma_byte(d1, j); lemma_byte(d2, j); lemma_byte(f, j);
        }
    }
    (d0, d1, d2)
}

/// `delta` of four rows, with t = s8(p1 - q1) where `nh` is 0.
fn delta_v(p1: __m128i, p0: __m128i, q0: __m128i, q1: __m128i, nh: __m128i) -> (r: __m128i)
    ensures forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r, j) == delta(byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(nh, j)),
{
    broadcast use lemma_byte;
    let sbit = sx::set1_epi8(0x80);
    let d = sx::subs_epi8(sx::xor_si128(q0, sbit), sx::xor_si128(p0, sbit));
    let t = sx::andnot_si128(nh, sx::subs_epi8(sx::xor_si128(p1, sbit), sx::xor_si128(q1, sbit)));
    sx::adds_epi8(sx::adds_epi8(sx::adds_epi8(t, d), d), d)
}

fn sh3_v(f: __m128i, k: u8) -> (r: __m128i)
    ensures forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r, j) == sh3(byte(f, j), k),
{
    broadcast use lemma_byte;
    srai3_epi8(sx::adds_epi8(f, sx::set1_epi8(k)))
}

/// p + d and q - d, saturated, through the flipped forms.
fn adj_v(p: __m128i, q: __m128i, d: __m128i) -> (r: (__m128i, __m128i))
    ensures
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r.0, j) == adj_p(byte(p, j), byte(d, j)),
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r.1, j) == adj_q(byte(q, j), byte(d, j)),
{
    broadcast use lemma_byte;
    let sbit = sx::set1_epi8(0x80);
    (sx::xor_si128(sx::adds_epi8(sx::xor_si128(p, sbit), d), sbit), sx::xor_si128(sx::subs_epi8(sx::xor_si128(q, sbit), d), sbit))
}

/// p + dp + d and q - dq - d, each step saturated.
fn adj2_v(p: __m128i, q: __m128i, dp: __m128i, dq: __m128i, d: __m128i) -> (r: (__m128i, __m128i))
    ensures
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r.0, j) == adj_p2(byte(p, j), byte(dp, j), byte(d, j)),
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r.1, j) == adj_q2(byte(q, j), byte(dq, j), byte(d, j)),
{
    broadcast use lemma_byte;
    let sbit = sx::set1_epi8(0x80);
    (sx::xor_si128(sx::adds_epi8(sx::adds_epi8(sx::xor_si128(p, sbit), dp), d), sbit),
     sx::xor_si128(sx::subs_epi8(sx::subs_epi8(sx::xor_si128(q, sbit), dq), d), sbit))
}

/// The 6-pixel filter on six rows of 16 lines (`lane6` in each lane).
fn filter6(p2: __m128i, p1: __m128i, p0: __m128i, q0: __m128i, q1: __m128i, q2: __m128i, mask: __m128i, nh: __m128i)
    -> (r: (__m128i, __m128i, __m128i, __m128i, __m128i, __m128i))
    ensures
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r.0, j) == lane6(byte(p2, j), byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(q2, j), byte(mask, j), byte(nh, j))[0],
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r.1, j) == lane6(byte(p2, j), byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(q2, j), byte(mask, j), byte(nh, j))[1],
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r.2, j) == lane6(byte(p2, j), byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(q2, j), byte(mask, j), byte(nh, j))[2],
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r.3, j) == lane6(byte(p2, j), byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(q2, j), byte(mask, j), byte(nh, j))[3],
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r.4, j) == lane6(byte(p2, j), byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(q2, j), byte(mask, j), byte(nh, j))[4],
        forall|j: int| 0 <= j < 16 ==> #[trigger] byte(r.5, j) == lane6(byte(p2, j), byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(q2, j), byte(mask, j), byte(nh, j))[5],
{
    hide(delta); hide(adj_p); hide(adj_q); hide(adj_p2); hide(adj_q2); hide(sh3); hide(tap);
    let z = sx::setzero();
    let a = delta_v(p1, p0, q0, q1, z);
    let na = sx::andnot_si128(nh, mask);
    let fa = sx::and_si128(a, na);
    let nb = sx::and_si128(nh, mask);
    let fb = sx::and_si128(a, nb);
    let v3 = sh3_v(fa, 3);
    let v4 = sh3_v(fa, 4);
    let (d0, d1, d2) = taps(fb);
    let (o2, n2) = adj_v(p2, q2, d2);
    let (o1, n1) = adj_v(p1, q1, d1);
    let (o0, n0) = adj2_v(p0, q0, v3, v4, d0);
    proof {
        assert forall|j: int| 0 <= j < 16 implies
            byte(o2, j) == lane6(byte(p2, j), byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(q2, j), byte(mask, j), byte(nh, j))[0] && byte(o1, j) == lane6(byte(p2, j), byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(q2, j), byte(mask, j), byte(nh, j))[1] && byte(o0, j) == lane6(byte(p2, j), byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(q2, j), byte(mask, j), byte(nh, j))[2]
            && byte(n0, j) == lane6(byte(p2, j), byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(q2, j), byte(mask, j), byte(nh, j))[3] && byte(n1, j) == lane6(byte(p2, j), byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(q2, j), byte(mask, j), byte(nh, j))[4] && byte(n2, j) == lane6(byte(p2, j), byte(p1, j), byte(p0, j), byte(q0, j), byte(q1, j), byte(q2, j), byte(mask, j), byte(nh, j))[5] by {
            lemma_byte(z, j); lemma_byte(na, j); lemma_byte(fa, j); lemma_byte(nb, j); lemma_byte(fb, j);
            assert(byte(z, j) == 0u8);
            assert(byte(fa, j) == and_u8(byte(a, j), andnot_u8(byte(nh, j), byte(mask, j))));
            assert(byte(fb, j) == and_u8(byte(a, j), and_u8(byte(nh, j), byte(mask, j))));
        }
    }
    (o2, o1, o0, n0, n1, n2)
}

/// The plane with row r's 16 pixels from x set to `b`.
pub open spec fn set_row(pl: Plane, r: int, x: int, b: Seq<u8>) -> Plane {
    pl.update(r, Seq::new(pl[r].len(), |cc: int| if x <= cc < x + 16 { b[cc - x] } else { pl[r][cc] }))
}

fn load_row(v: &Vec<u8>, w: usize, x: usize, r: usize, Ghost(pl): Ghost<Plane>) -> (a: __m128i)
    requires holds(v@, w as nat, pl), r < pl.len(), x + 16 <= w,
    ensures forall|j: int| 0 <= j < 16 ==> #[trigger] byte(a, j) == pl[r as int][x + j],
{
    let n = v.len();
    proof { lemma_idx(w as nat, pl.len(), (x + 15) as int, r as int); }
    let a = sx::loadu(v.as_slice(), r * w + x);
    proof {
        assert forall|j: int| 0 <= j < 16 implies #[trigger] byte(a, j) == pl[r as int][x + j] by {
            lemma_idx(w as nat, pl.len(), x + j, r as int);
            lemma_byte(a, j);
        }
    }
    a
}

proof fn lemma_outside(w: nat, r: int, x: int, yy: int, xx: int)
    requires 0 <= xx < w, 0 <= yy, 0 <= r, 0 <= x, x + 16 <= w, yy != r || !(x <= xx < x + 16),
    ensures !(r * w + x <= yy * w + xx < r * w + x + 16),
{
    if yy < r {
        assert(yy * w + xx < r * w) by (nonlinear_arith) requires yy < r, 0 <= xx < w;
    } else if yy > r {
        assert(yy * w >= r * w + w) by (nonlinear_arith) requires yy > r, w >= 0;
    }
}

fn store_row(v: &mut Vec<u8>, w: usize, x: usize, r: usize, a: __m128i, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), r < pl.len(), x + 16 <= w,
    ensures holds(final(v)@, w as nat, set_row(pl, r as int, x as int, v8(a))),
{
    let n = v.len();
    proof { lemma_idx(w as nat, pl.len(), (x + 15) as int, r as int); }
    let off = r * w + x;
    sx::storeu(v, off, a);
    proof {
        let p2 = set_row(pl, r as int, x as int, v8(a));
        assert forall|yy: int, xx: int| 0 <= yy < p2.len() && 0 <= xx < w implies v@[yy * w + xx] == #[trigger] p2[yy][xx] by {
            lemma_idx(w as nat, pl.len(), xx, yy);
            if yy == r && x <= xx < x + 16 {
            } else {
                lemma_outside(w as nat, r as int, x as int, yy, xx);
            }
        }
    }
}

/// Row r of the filtered edge.
pub open spec fn tgt_row(pl: Plane, x: int, y: int, r: int, kind: int, e: int, i: int, h: int) -> Seq<u8> {
    Seq::new(pl[r].len(), |cc: int| if x <= cc < x + 16 { c_filter(col(pl, cc, y), kind, e, i, h)[r - y + 4] } else { pl[r][cc] })
}

/// The rows a filter leaves alone: p3 and q3 always, p2 and q2 unless it
/// is the macroblock filter, p1 and q1 in the simple filter.
proof fn lemma_keep(c: Seq<u8>, kind: int, e: int, i: int, h: int)
    requires c.len() == 8, 0 <= kind <= 2,
    ensures ({ let cf = c_filter(c, kind, e, i, h);
        &&& cf.len() == 8 && cf[0] == c[0] && cf[7] == c[7]
        &&& kind != 0 ==> cf[1] == c[1] && cf[6] == c[6]
        &&& kind == 2 ==> cf[2] == c[2] && cf[5] == c[5] }),
{}

/// Storing a row of the filtered edge.
proof fn lemma_put_row(pl: Plane, g: Plane, w: nat, x: int, y: int, r: int, b: Seq<u8>, kind: int, e: int, i: int, h: int)
    requires rows_w(pl, w), 4 <= y, y + 4 <= pl.len(), 0 <= x, x + 16 <= w, y - 4 <= r < y + 4,
        g.len() == pl.len(), g[r] == pl[r], b.len() == 16,
        forall|j: int| 0 <= j < 16 ==> #[trigger] b[j] == c_filter(col(pl, x + j, y), kind, e, i, h)[r - y + 4],
    ensures set_row(g, r, x, b)[r] == tgt_row(pl, x, y, r, kind, e, i, h),
        forall|rr: int| 0 <= rr < g.len() && rr != r ==> #[trigger] set_row(g, r, x, b)[rr] == g[rr],
        set_row(g, r, x, b).len() == g.len(),
{
    assert forall|cc: int| x <= cc < x + 16 implies #[trigger] b[cc - x] == c_filter(col(pl, cc, y), kind, e, i, h)[r - y + 4] by {
        assert(x + (cc - x) == cc);
    }
    assert(set_row(g, r, x, b)[r] =~= tgt_row(pl, x, y, r, kind, e, i, h));
}

/// A row the filter leaves alone is already its row of the filtered edge.
proof fn lemma_kept_row(pl: Plane, w: nat, x: int, y: int, r: int, kind: int, e: int, i: int, h: int)
    requires rows_w(pl, w), 4 <= y, y + 4 <= pl.len(), 0 <= x, x + 16 <= w, y - 4 <= r < y + 4, 0 <= kind <= 2,
        forall|cc: int| x <= cc < x + 16 ==> #[trigger] c_filter(col(pl, cc, y), kind, e, i, h)[r - y + 4] == col(pl, cc, y)[r - y + 4],
    ensures pl[r] == tgt_row(pl, x, y, r, kind, e, i, h),
{
    assert(pl[r] =~= tgt_row(pl, x, y, r, kind, e, i, h));
}

proof fn lemma_edge_rows(pl: Plane, g: Plane, w: nat, x: int, y: int, kind: int, e: int, i: int, h: int)
    requires rows_w(pl, w), 4 <= y, y + 4 <= pl.len(), 0 <= x, x + 16 <= w, g.len() == pl.len(),
        forall|r: int| 0 <= r < pl.len() && !(y - 4 <= r < y + 4) ==> #[trigger] g[r] == pl[r],
        forall|r: int| y - 4 <= r < y + 4 ==> #[trigger] g[r] == tgt_row(pl, x, y, r, kind, e, i, h),
    ensures g == edge_res(pl, x, y, 16, 0, kind, e, i, h),
{
    let er = edge_res(pl, x, y, 16, 0, kind, e, i, h);
    assert forall|r: int| 0 <= r < pl.len() implies #[trigger] g[r] == er[r] by {
        if y - 4 <= r < y + 4 {
            assert(g[r] =~= er[r]);
        }
    }
    assert(g =~= er);
}

/// What the filter computed, per row: row k of the window (0 is p3).
pub open spec fn row_ok(pl: Plane, x: int, y: int, k: int, o: __m128i, kind: int, e: int, i: int, h: int) -> bool {
    forall|j: int| 0 <= j < 16 ==> #[trigger] v8(o)[j] == c_filter(col(pl, x + j, y), kind, e, i, h)[k]
}

/// A row the filter keeps: row k of the window.
pub open spec fn row_kept(pl: Plane, x: int, y: int, k: int, kind: int, e: int, i: int, h: int) -> bool {
    forall|cc: int| x <= cc < x + 16 ==> #[trigger] c_filter(col(pl, cc, y), kind, e, i, h)[k] == col(pl, cc, y)[k]
}

/// Store row `k` of the window, and account for it.
fn put(v: &mut Vec<u8>, w: usize, x: usize, y: usize, k: usize, o: __m128i, kind: u8, e: i32, i: i32, h: i32,
    Ghost(pl): Ghost<Plane>, Ghost(g): Ghost<Plane>) -> (g2: Ghost<Plane>)
    requires holds(old(v)@, w as nat, g), rows_w(pl, w as nat), g.len() == pl.len(), 4 <= y, y + 4 <= pl.len(), x + 16 <= w, k < 8,
        g[y - 4 + k] == pl[y - 4 + k], row_ok(pl, x as int, y as int, k as int, o, kind as int, e as int, i as int, h as int),
    ensures holds(final(v)@, w as nat, g2@), g2@.len() == g.len(),
        g2@[y - 4 + k] == tgt_row(pl, x as int, y as int, y - 4 + k, kind as int, e as int, i as int, h as int),
        forall|r: int| 0 <= r < g.len() && r != y - 4 + k ==> #[trigger] g2@[r] == g[r],
{
    let r = y - 4 + k;
    store_row(v, w, x, r, o, Ghost(g));
    proof {
        assert forall|j: int| 0 <= j < 16 implies #[trigger] v8(o)[j] == c_filter(col(pl, x + j, y as int), kind as int, e as int, i as int, h as int)[r - y + 4] by {
            assert(r - y + 4 == k);
        }
        lemma_put_row(pl, g, w as nat, x as int, y as int, r as int, v8(o), kind as int, e as int, i as int, h as int);
    }
    Ghost(set_row(g, r as int, x as int, v8(o)))
}

proof fn lemma_done(pl: Plane, g: Plane, w: nat, x: int, y: int, kind: int, e: int, i: int, h: int, lo: int, hi: int)
    requires rows_w(pl, w), 4 <= y, y + 4 <= pl.len(), 0 <= x, x + 16 <= w, g.len() == pl.len(), 0 <= kind <= 2,
        0 <= lo <= hi <= 8,
        forall|r: int| 0 <= r < pl.len() && !(y - 4 + lo <= r < y - 4 + hi) ==> #[trigger] g[r] == pl[r],
        forall|r: int| y - 4 + lo <= r < y - 4 + hi ==> #[trigger] g[r] == tgt_row(pl, x, y, r, kind, e, i, h),
        forall|k: int| 0 <= k < 8 && !(lo <= k < hi) ==> #[trigger] row_kept(pl, x, y, k, kind, e, i, h),
    ensures g == edge_res(pl, x, y, 16, 0, kind, e, i, h),
{
    assert forall|r: int| y - 4 <= r < y + 4 implies #[trigger] g[r] == tgt_row(pl, x, y, r, kind, e, i, h) by {
        if !(y - 4 + lo <= r < y - 4 + hi) {
            assert(row_kept(pl, x, y, r - y + 4, kind, e, i, h));
            lemma_kept_row(pl, w, x, y, r, kind, e, i, h);
        }
    }
    lemma_edge_rows(pl, g, w, x, y, kind, e, i, h);
}

fn store_rows6(v: &mut Vec<u8>, w: usize, x: usize, y: usize, o2: __m128i, o1: __m128i, o0: __m128i, n0: __m128i, n1: __m128i, n2: __m128i,
    kind: u8, e: i32, i: i32, h: i32, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), 4 <= y, y + 4 <= pl.len(), x + 16 <= w, kind == 0,
        row_ok(pl, x as int, y as int, 1, o2, kind as int, e as int, i as int, h as int),
        row_ok(pl, x as int, y as int, 2, o1, kind as int, e as int, i as int, h as int),
        row_ok(pl, x as int, y as int, 3, o0, kind as int, e as int, i as int, h as int),
        row_ok(pl, x as int, y as int, 4, n0, kind as int, e as int, i as int, h as int),
        row_ok(pl, x as int, y as int, 5, n1, kind as int, e as int, i as int, h as int),
        row_ok(pl, x as int, y as int, 6, n2, kind as int, e as int, i as int, h as int),
        row_kept(pl, x as int, y as int, 0, kind as int, e as int, i as int, h as int),
        row_kept(pl, x as int, y as int, 7, kind as int, e as int, i as int, h as int),
    ensures holds(final(v)@, w as nat, edge_res(pl, x as int, y as int, 16, 0, kind as int, e as int, i as int, h as int)),
{
    proof { assert(rows_w(pl, w as nat)); }
    let Ghost(g1) = put(v, w, x, y, 1, o2, kind, e, i, h, Ghost(pl), Ghost(pl));
    let Ghost(g2) = put(v, w, x, y, 2, o1, kind, e, i, h, Ghost(pl), Ghost(g1));
    let Ghost(g3) = put(v, w, x, y, 3, o0, kind, e, i, h, Ghost(pl), Ghost(g2));
    let Ghost(g4) = put(v, w, x, y, 4, n0, kind, e, i, h, Ghost(pl), Ghost(g3));
    let Ghost(g5) = put(v, w, x, y, 5, n1, kind, e, i, h, Ghost(pl), Ghost(g4));
    let Ghost(g6) = put(v, w, x, y, 6, n2, kind, e, i, h, Ghost(pl), Ghost(g5));
    proof {
        let (yi, xi) = (y as int, x as int);
        assert forall|r: int| yi - 3 <= r < yi + 3 implies #[trigger] g6[r] == tgt_row(pl, xi, yi, r, kind as int, e as int, i as int, h as int) by {}
        lemma_done(pl, g6, w as nat, xi, yi, kind as int, e as int, i as int, h as int, 1, 7);
    }
}

fn store_rows4(v: &mut Vec<u8>, w: usize, x: usize, y: usize, o1: __m128i, o0: __m128i, n0: __m128i, n1: __m128i,
    kind: u8, e: i32, i: i32, h: i32, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), 4 <= y, y + 4 <= pl.len(), x + 16 <= w, kind == 1 || kind == 2,
        row_ok(pl, x as int, y as int, 2, o1, kind as int, e as int, i as int, h as int),
        row_ok(pl, x as int, y as int, 3, o0, kind as int, e as int, i as int, h as int),
        row_ok(pl, x as int, y as int, 4, n0, kind as int, e as int, i as int, h as int),
        row_ok(pl, x as int, y as int, 5, n1, kind as int, e as int, i as int, h as int),
        row_kept(pl, x as int, y as int, 0, kind as int, e as int, i as int, h as int),
        row_kept(pl, x as int, y as int, 1, kind as int, e as int, i as int, h as int),
        row_kept(pl, x as int, y as int, 6, kind as int, e as int, i as int, h as int),
        row_kept(pl, x as int, y as int, 7, kind as int, e as int, i as int, h as int),
        kind == 2 ==> row_kept(pl, x as int, y as int, 2, kind as int, e as int, i as int, h as int)
            && row_kept(pl, x as int, y as int, 5, kind as int, e as int, i as int, h as int),
    ensures holds(final(v)@, w as nat, edge_res(pl, x as int, y as int, 16, 0, kind as int, e as int, i as int, h as int)),
{
    proof { assert(rows_w(pl, w as nat)); }
    let (yi, xi) = (Ghost(y as int), Ghost(x as int));
    if kind == 1 {
        let Ghost(g1) = put(v, w, x, y, 2, o1, kind, e, i, h, Ghost(pl), Ghost(pl));
        let Ghost(g2) = put(v, w, x, y, 3, o0, kind, e, i, h, Ghost(pl), Ghost(g1));
        let Ghost(g3) = put(v, w, x, y, 4, n0, kind, e, i, h, Ghost(pl), Ghost(g2));
        let Ghost(g4) = put(v, w, x, y, 5, n1, kind, e, i, h, Ghost(pl), Ghost(g3));
        proof {
            assert forall|r: int| y - 2 <= r < y + 2 implies #[trigger] g4[r] == tgt_row(pl, x as int, y as int, r, kind as int, e as int, i as int, h as int) by {}
            lemma_done(pl, g4, w as nat, x as int, y as int, kind as int, e as int, i as int, h as int, 2, 6);
        }
    } else {
        let Ghost(g1) = put(v, w, x, y, 3, o0, kind, e, i, h, Ghost(pl), Ghost(pl));
        let Ghost(g2) = put(v, w, x, y, 4, n0, kind, e, i, h, Ghost(pl), Ghost(g1));
        proof {
            assert forall|r: int| y - 1 <= r < y + 1 implies #[trigger] g2[r] == tgt_row(pl, x as int, y as int, r, kind as int, e as int, i as int, h as int) by {}
            lemma_done(pl, g2, w as nat, x as int, y as int, kind as int, e as int, i as int, h as int, 3, 5);
        }
    }
}

/// Lane j of `o` is entry k of `c_filter` of column j.
pub open spec fn lanes_ok(cs: Seq<Seq<u8>>, k: int, o: __m128i, kind: int, e: int, i: int, h: int) -> bool {
    forall|j: int| 0 <= j < 16 ==> #[trigger] v8(o)[j] == c_filter(cs[j], kind, e, i, h)[k]
}

proof fn lemma_row_ok(pl: Plane, x: int, y: int, cs: Seq<Seq<u8>>, k: int, o: __m128i, kind: int, e: int, i: int, h: int)
    requires forall|j: int| 0 <= j < 16 ==> #[trigger] cs[j] == col(pl, x + j, y), lanes_ok(cs, k, o, kind, e, i, h),
    ensures row_ok(pl, x, y, k, o, kind, e, i, h),
{
    assert forall|j: int| 0 <= j < 16 implies #[trigger] v8(o)[j] == c_filter(col(pl, x + j, y), kind, e, i, h)[k] by {
        assert(cs[j] == col(pl, x + j, y));
    }
}

/// The macroblock-edge filter's six rows, as `c_filter` computes them.
fn rows6(p3: __m128i, p2: __m128i, p1: __m128i, p0: __m128i, q0: __m128i, q1: __m128i, q2: __m128i, q3: __m128i,
    mask: __m128i, nh: __m128i, Ghost(cs): Ghost<Seq<Seq<u8>>>,
    Ghost(kind): Ghost<int>, Ghost(e): Ghost<int>, Ghost(i): Ghost<int>, Ghost(h): Ghost<int>)
    -> (r: (__m128i, __m128i, __m128i, __m128i, __m128i, __m128i))
    requires kind == 0,
        forall|j: int| 0 <= j < 16 ==> #[trigger] lc(p3, p2, p1, p0, q0, q1, q2, q3, j) == cs[j],
        forall|j: int| 0 <= j < 16 ==> {
            let c = lc(p3, p2, p1, p0, q0, q1, q2, q3, j);
            &&& #[trigger] byte(mask, j) == if c_thr(c, kind, e, i) { 255u8 } else { 0u8 }
            &&& byte(nh, j) == if kind != 2 && !c_hev(c, h) { 255u8 } else { 0u8 }
        },
    ensures lanes_ok(cs, 1, r.0, kind, e, i, h), lanes_ok(cs, 2, r.1, kind, e, i, h), lanes_ok(cs, 3, r.2, kind, e, i, h),
        lanes_ok(cs, 4, r.3, kind, e, i, h), lanes_ok(cs, 5, r.4, kind, e, i, h), lanes_ok(cs, 6, r.5, kind, e, i, h),
{
    hide(c_filter); hide(lane6); hide(c_normal); hide(c_simple); hide(c_hev);
    let r = filter6(p2, p1, p0, q0, q1, q2, mask, nh);
    proof {
        assert forall|j: int| #![trigger c_filter(cs[j], kind, e, i, h)] 0 <= j < 16 implies {
            let cf = c_filter(cs[j], kind, e, i, h);
            &&& v8(r.0)[j] == cf[1] && v8(r.1)[j] == cf[2] && v8(r.2)[j] == cf[3]
            &&& v8(r.3)[j] == cf[4] && v8(r.4)[j] == cf[5] && v8(r.5)[j] == cf[6]
        } by {
            let c = cs[j];
            assert(lc(p3, p2, p1, p0, q0, q1, q2, q3, j) == c);
            lemma_byte(r.0, j); lemma_byte(r.1, j); lemma_byte(r.2, j); lemma_byte(r.3, j); lemma_byte(r.4, j); lemma_byte(r.5, j);
            lemma_lane6(c, e, i, h, byte(mask, j), byte(nh, j));
            lemma_keep(c, kind, e, i, h);
            let cf = c_filter(c, kind, e, i, h);
            assert(cf.subrange(1, 7)[0] == cf[1] && cf.subrange(1, 7)[1] == cf[2] && cf.subrange(1, 7)[2] == cf[3]);
            assert(cf.subrange(1, 7)[3] == cf[4] && cf.subrange(1, 7)[4] == cf[5] && cf.subrange(1, 7)[5] == cf[6]);
        }
    }
    r
}

/// The subblock or simple filter's four rows, as `c_filter` computes them.
fn rows4(p3: __m128i, p2: __m128i, p1: __m128i, p0: __m128i, q0: __m128i, q1: __m128i, q2: __m128i, q3: __m128i,
    mask: __m128i, nh: __m128i, Ghost(cs): Ghost<Seq<Seq<u8>>>,
    Ghost(kind): Ghost<int>, Ghost(e): Ghost<int>, Ghost(i): Ghost<int>, Ghost(h): Ghost<int>)
    -> (r: (__m128i, __m128i, __m128i, __m128i))
    requires kind == 1 || kind == 2,
        forall|j: int| 0 <= j < 16 ==> #[trigger] lc(p3, p2, p1, p0, q0, q1, q2, q3, j) == cs[j],
        forall|j: int| 0 <= j < 16 ==> {
            let c = lc(p3, p2, p1, p0, q0, q1, q2, q3, j);
            &&& #[trigger] byte(mask, j) == if c_thr(c, kind, e, i) { 255u8 } else { 0u8 }
            &&& byte(nh, j) == if kind != 2 && !c_hev(c, h) { 255u8 } else { 0u8 }
        },
    ensures lanes_ok(cs, 2, r.0, kind, e, i, h), lanes_ok(cs, 3, r.1, kind, e, i, h),
        lanes_ok(cs, 4, r.2, kind, e, i, h), lanes_ok(cs, 5, r.3, kind, e, i, h),
{
    hide(c_filter); hide(lane4); hide(c_normal); hide(c_simple); hide(c_hev);
    let r = filter4(p1, p0, q0, q1, mask, nh);
    proof {
        assert forall|j: int| #![trigger c_filter(cs[j], kind, e, i, h)] 0 <= j < 16 implies {
            let cf = c_filter(cs[j], kind, e, i, h);
            &&& v8(r.0)[j] == cf[2] && v8(r.1)[j] == cf[3] && v8(r.2)[j] == cf[4] && v8(r.3)[j] == cf[5]
        } by {
            let c = cs[j];
            assert(lc(p3, p2, p1, p0, q0, q1, q2, q3, j) == c);
            lemma_byte(r.0, j); lemma_byte(r.1, j); lemma_byte(r.2, j); lemma_byte(r.3, j);
            lemma_lane4(c, kind, e, i, h, byte(mask, j), byte(nh, j));
            lemma_keep(c, kind, e, i, h);
            let cf = c_filter(c, kind, e, i, h);
            assert(cf.subrange(2, 6)[0] == cf[2] && cf.subrange(2, 6)[1] == cf[3] && cf.subrange(2, 6)[2] == cf[4] && cf.subrange(2, 6)[3] == cf[5]);
        }
    }
    r
}

proof fn lemma_kept_all(pl: Plane, x: int, y: int, kind: int, e: int, i: int, h: int)
    requires 0 <= kind <= 2,
    ensures row_kept(pl, x, y, 0, kind, e, i, h), row_kept(pl, x, y, 7, kind, e, i, h),
        kind != 0 ==> row_kept(pl, x, y, 1, kind, e, i, h) && row_kept(pl, x, y, 6, kind, e, i, h),
        kind == 2 ==> row_kept(pl, x, y, 2, kind, e, i, h) && row_kept(pl, x, y, 5, kind, e, i, h),
{
    assert forall|cc: int| #![trigger c_filter(col(pl, cc, y), kind, e, i, h)] x <= cc < x + 16 implies {
        let c = col(pl, cc, y);
        let cf = c_filter(c, kind, e, i, h);
        &&& cf[0] == c[0] && cf[7] == c[7]
        &&& kind != 0 ==> cf[1] == c[1] && cf[6] == c[6]
        &&& kind == 2 ==> cf[2] == c[2] && cf[5] == c[5]
    } by {
        lemma_keep(col(pl, cc, y), kind, e, i, h);
    }
}

/// The loop filter across the horizontal edge at row y, columns x .. x + 16,
/// in SSE2: `filter_edge` of its 16 lines.
pub fn hedge_x(v: &mut Vec<u8>, w: usize, x: usize, y: usize, kind: u8, e: i32, i: i32, h: i32, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), 4 <= y, y + 4 <= pl.len(), x + 16 <= w, kind <= 2,
        0 <= e, 0 <= i <= 255, 0 <= h <= 255, (if kind == 2 { e as int } else { 2 * e + i }) <= 254,
    ensures holds(final(v)@, w as nat, filter_edge(pl, x as int, y as int, 1, 16, kind as int, e as int, i as int, h as int, 0)),
        filter_edge(pl, x as int, y as int, 1, 16, kind as int, e as int, i as int, h as int, 0).len() == pl.len(),
{
    let ghost (xi, yi, ki, ei, ii, hi) = (x as int, y as int, kind as int, e as int, i as int, h as int);
    proof { assert(rows_w(pl, w as nat)); }
    let p3 = load_row(v, w, x, y - 4, Ghost(pl));
    let p2 = load_row(v, w, x, y - 3, Ghost(pl));
    let p1 = load_row(v, w, x, y - 2, Ghost(pl));
    let p0 = load_row(v, w, x, y - 1, Ghost(pl));
    let q0 = load_row(v, w, x, y, Ghost(pl));
    let q1 = load_row(v, w, x, y + 1, Ghost(pl));
    let q2 = load_row(v, w, x, y + 2, Ghost(pl));
    let q3 = load_row(v, w, x, y + 3, Ghost(pl));
    let (mask, nh) = masks(p3, p2, p1, p0, q0, q1, q2, q3, kind, e, i, h);
    proof {
        assert forall|j: int| 0 <= j < 16 implies #[trigger] lc(p3, p2, p1, p0, q0, q1, q2, q3, j) == col(pl, xi + j, yi) by {
            assert(lc(p3, p2, p1, p0, q0, q1, q2, q3, j) =~= col(pl, xi + j, yi));
        }
        lemma_kept_all(pl, xi, yi, ki, ei, ii, hi);
    }
    let ghost cs = Seq::new(16, |j: int| col(pl, xi + j, yi));
    if kind == 0 {
        let (o2, o1, o0, n0, n1, n2) = rows6(p3, p2, p1, p0, q0, q1, q2, q3, mask, nh, Ghost(cs), Ghost(ki), Ghost(ei), Ghost(ii), Ghost(hi));
        proof {
            lemma_row_ok(pl, xi, yi, cs, 1, o2, ki, ei, ii, hi); lemma_row_ok(pl, xi, yi, cs, 2, o1, ki, ei, ii, hi);
            lemma_row_ok(pl, xi, yi, cs, 3, o0, ki, ei, ii, hi); lemma_row_ok(pl, xi, yi, cs, 4, n0, ki, ei, ii, hi);
            lemma_row_ok(pl, xi, yi, cs, 5, n1, ki, ei, ii, hi); lemma_row_ok(pl, xi, yi, cs, 6, n2, ki, ei, ii, hi);
        }
        store_rows6(v, w, x, y, o2, o1, o0, n0, n1, n2, kind, e, i, h, Ghost(pl));
    } else {
        let (o1, o0, n0, n1) = rows4(p3, p2, p1, p0, q0, q1, q2, q3, mask, nh, Ghost(cs), Ghost(ki), Ghost(ei), Ghost(ii), Ghost(hi));
        proof {
            lemma_row_ok(pl, xi, yi, cs, 2, o1, ki, ei, ii, hi); lemma_row_ok(pl, xi, yi, cs, 3, o0, ki, ei, ii, hi);
            lemma_row_ok(pl, xi, yi, cs, 4, n0, ki, ei, ii, hi); lemma_row_ok(pl, xi, yi, cs, 5, n1, ki, ei, ii, hi);
        }
        store_rows4(v, w, x, y, o1, o0, n0, n1, kind, e, i, h, Ghost(pl));
    }
    proof { lemma_edge(pl, w as nat, xi, yi, 16, 0, ki, ei, ii, hi); }
}

// ------------------------------------------------------- vertical edges

/// Where row j's 8 bytes sit in its vector after the transpose back.
pub open spec fn hoff(j: int) -> int { if j % 2 == 1 { 8 } else { 0 } }

/// Pixels x - 4 .. x + 4 of row r, in the low half.
fn load8(v: &Vec<u8>, w: usize, x: usize, r: usize, Ghost(pl): Ghost<Plane>) -> (a: __m128i)
    requires holds(v@, w as nat, pl), r < pl.len(), 4 <= x, x + 4 <= w,
    ensures forall|k: int| 0 <= k < 8 ==> #[trigger] byte(a, k) == pl[r as int][x - 4 + k],
{
    let n = v.len();
    proof { lemma_idx(w as nat, pl.len(), (x + 3) as int, r as int); }
    let a = sx::loadl(v.as_slice(), r * w + x - 4);
    proof {
        assert forall|k: int| 0 <= k < 8 implies #[trigger] byte(a, k) == pl[r as int][x - 4 + k] by {
            lemma_idx(w as nat, pl.len(), x - 4 + k, r as int);
            lemma_byte(a, k);
        }
    }
    a
}

/// Write the half `hi` of `a` at pixels x - 4 .. x + 4 of row r.
fn put8(v: &mut Vec<u8>, w: usize, x: usize, r: usize, a: __m128i, hi: bool, Ghost(pl): Ghost<Plane>, Ghost(t): Ghost<Seq<u8>>)
    requires holds(old(v)@, w as nat, pl), r < pl.len(), 4 <= x, x + 4 <= w, t.len() == 8,
        forall|m: int| 0 <= m < 8 ==> #[trigger] t[m] == v8(a)[m + if hi { 8int } else { 0 }],
    ensures holds(final(v)@, w as nat, set_rowv(pl, x as int, r as int, t)),
{
    let n = v.len();
    proof { lemma_idx(w as nat, pl.len(), (x + 3) as int, r as int); }
    let off = r * w + x - 4;
    if hi { sx::storeh(v, off, a); } else { sx::storel(v, off, a); }
    proof {
        let p2 = set_rowv(pl, x as int, r as int, t);
        assert forall|yy: int, xx: int| 0 <= yy < p2.len() && 0 <= xx < w implies v@[yy * w + xx] == #[trigger] p2[yy][xx] by {
            lemma_idx(w as nat, pl.len(), xx, yy);
            if yy == r && x - 4 <= xx < x + 4 {
                assert(t[xx - x + 4] == v8(a)[(yy * w + xx - off) + if hi { 8int } else { 0 }]);
            } else if yy != r {
                lemma_outside8(w as nat, r as int, x - 4, yy, xx);
            }
        }
    }
}

proof fn lemma_outside8(w: nat, r: int, x: int, yy: int, xx: int)
    requires 0 <= xx < w, 0 <= yy, 0 <= r, 0 <= x, x + 8 <= w, yy != r,
    ensures !(r * w + x <= yy * w + xx < r * w + x + 8),
{
    if yy < r {
        assert(yy * w + xx < r * w) by (nonlinear_arith) requires yy < r, 0 <= xx < w;
    } else {
        assert(yy * w >= r * w + w) by (nonlinear_arith) requires yy > r, w >= 0;
    }
}

/// The filter on 8 columns of 16 lanes (p3 .. q3): the 8 new columns,
/// lane j of column k being entry k of `c_filter` of lane j's line `cs[j]`.
fn filter_cols(c: &[__m128i; 8], kind: u8, e: i32, i: i32, h: i32, Ghost(cs): Ghost<Seq<Seq<u8>>>) -> (nv: [__m128i; 8])
    requires kind <= 2, 0 <= e, 0 <= i <= 255, 0 <= h <= 255, (if kind == 2 { e as int } else { 2 * e + i }) <= 254,
        forall|j: int| 0 <= j < 16 ==> #[trigger] lc(c@[0], c@[1], c@[2], c@[3], c@[4], c@[5], c@[6], c@[7], j) == cs[j],
    ensures forall|k: int| 0 <= k < 8 ==> #[trigger] lanes_ok(cs, k, nv@[k], kind as int, e as int, i as int, h as int),
{
    let ghost (ki, ei, ii, hi) = (kind as int, e as int, i as int, h as int);
    let (p3, p2, p1, p0, q0, q1, q2, q3) = (c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]);
    let (mask, nh) = masks(p3, p2, p1, p0, q0, q1, q2, q3, kind, e, i, h);
    let nv: [__m128i; 8] = if kind == 0 {
        let (o2, o1, o0, n0, n1, n2) = rows6(p3, p2, p1, p0, q0, q1, q2, q3, mask, nh, Ghost(cs), Ghost(ki), Ghost(ei), Ghost(ii), Ghost(hi));
        [p3, o2, o1, o0, n0, n1, n2, q3]
    } else {
        let (o1, o0, n0, n1) = rows4(p3, p2, p1, p0, q0, q1, q2, q3, mask, nh, Ghost(cs), Ghost(ki), Ghost(ei), Ghost(ii), Ghost(hi));
        [p3, p2, o1, o0, n0, n1, q2, q3]
    };
    proof {
        assert forall|k: int| 0 <= k < 8 implies #[trigger] lanes_ok(cs, k, nv@[k], ki, ei, ii, hi) by {
            assert forall|j: int| 0 <= j < 16 implies #[trigger] v8(nv@[k])[j] == c_filter(cs[j], ki, ei, ii, hi)[k] by {
                assert(lc(p3, p2, p1, p0, q0, q1, q2, q3, j) == cs[j]);
                lemma_keep(cs[j], ki, ei, ii, hi);
                lemma_byte(nv@[k], j);
                if k == 0 || k == 7 || (ki != 0 && (k == 1 || k == 6)) {
                    lemma_byte(c@[k], j);
                }
            }
        }
    }
    nv
}

/// The 8 filtered columns transposed back to 16 lines of 8 bytes: line j
/// is the half `hoff(j)` of vector j / 2.
fn back_cols(nv: &[__m128i; 8], Ghost(cs): Ghost<Seq<Seq<u8>>>, Ghost(kind): Ghost<int>, Ghost(e): Ghost<int>, Ghost(i): Ghost<int>, Ghost(h): Ghost<int>)
    -> (hv: [__m128i; 8])
    requires forall|k: int| 0 <= k < 8 ==> #[trigger] lanes_ok(cs, k, nv@[k], kind, e, i, h),
    ensures forall|j: int, m: int| 0 <= j < 16 && 0 <= m < 8 ==>
        #[trigger] v8(hv@[j / 2])[m + hoff(j)] == c_filter(cs[j], kind, e, i, h)[m],
{
    let t0 = transpose8x8(nv, false);
    let t1 = transpose8x8(nv, true);
    let hv = [t0[0], t0[1], t0[2], t0[3], t1[0], t1[1], t1[2], t1[3]];
    proof {
        assert forall|j: int, m: int| 0 <= j < 16 && 0 <= m < 8 implies
            #[trigger] v8(hv@[j / 2])[m + hoff(j)] == c_filter(cs[j], kind, e, i, h)[m] by {
            let mm = m + hoff(j);
            lemma_byte(hv@[j / 2], mm);
            assert(mm % 8 == m && mm / 8 == j % 2);
            assert(lanes_ok(cs, m, nv@[m], kind, e, i, h));
            lemma_byte(nv@[m], j);
            if j < 8 {
                assert(byte(t0@[j / 2], mm) == byte(nv@[mm % 8], 2 * (j / 2) + mm / 8));
            } else {
                assert(byte(t1@[j / 2 - 4], mm) == byte(nv@[mm % 8], 8 + 2 * (j / 2 - 4) + mm / 8));
            }
        }
    }
    hv
}

/// Eight rows' 8 pixels at x - 4 .. x + 4, from row y.
fn load_rows8(v: &Vec<u8>, w: usize, x: usize, y: usize, Ghost(pl): Ghost<Plane>) -> (r: [__m128i; 8])
    requires holds(v@, w as nat, pl), 4 <= x, x + 4 <= w, y + 8 <= pl.len(),
    ensures forall|j: int, k: int| 0 <= j < 8 && 0 <= k < 8 ==> #[trigger] byte(r@[j], k) == pl[y + j][x - 4 + k],
{
    [load8(v, w, x, y, Ghost(pl)), load8(v, w, x, y + 1, Ghost(pl)), load8(v, w, x, y + 2, Ghost(pl)), load8(v, w, x, y + 3, Ghost(pl)),
     load8(v, w, x, y + 4, Ghost(pl)), load8(v, w, x, y + 5, Ghost(pl)), load8(v, w, x, y + 6, Ghost(pl)), load8(v, w, x, y + 7, Ghost(pl))]
}

/// Lines `from .. from + n` of the transposed-back vectors written as rows
/// y .. y + n of one plane (a vertical edge's lines).
fn store_vlines(v: &mut Vec<u8>, w: usize, x: usize, y: usize, n: usize, from: usize, hv: &[__m128i; 8],
    Ghost(pl): Ghost<Plane>, Ghost(cs): Ghost<Seq<Seq<u8>>>, Ghost(kind): Ghost<int>, Ghost(e): Ghost<int>, Ghost(i): Ghost<int>, Ghost(h): Ghost<int>)
    requires holds(old(v)@, w as nat, pl), 4 <= x, x + 4 <= w, y + n <= pl.len(), from + n <= 16, 0 <= kind <= 2,
        forall|j: int| 0 <= j < n ==> #[trigger] cs[from + j] == rowv(pl, x as int, y + j),
        forall|j: int, m: int| 0 <= j < 16 && 0 <= m < 8 ==>
            #[trigger] v8(hv@[j / 2])[m + hoff(j)] == c_filter(cs[j], kind, e, i, h)[m],
    ensures holds(final(v)@, w as nat, edge_res_v(pl, x as int, y as int, n as int, 0, kind, e, i, h)),
{
    let ghost (xi, yi) = (x as int, y as int);
    proof { assert(rows_w(pl, w as nat)); }
    let mut j: usize = 0;
    while j < n
        invariant j <= n, holds(v@, w as nat, edge_res_v(pl, xi, yi, j as int, 0, kind, e, i, h)), rows_w(pl, w as nat),
            4 <= x, x + 4 <= w, y + n <= pl.len(), from + n <= 16, xi == x, yi == y, 0 <= kind <= 2,
            forall|j: int| 0 <= j < n ==> #[trigger] cs[from + j] == rowv(pl, x as int, y + j),
            forall|j: int, m: int| 0 <= j < 16 && 0 <= m < 8 ==>
                #[trigger] v8(hv@[j / 2])[m + hoff(j)] == c_filter(cs[j], kind, e, i, h)[m],
        decreases n - j,
    {
        let ghost cur = edge_res_v(pl, xi, yi, j as int, 0, kind, e, i, h);
        let ghost jj = (from + j) as int;
        let ghost t = c_filter(rowv(pl, xi, yi + j), kind, e, i, h);
        proof {
            assert(cs[from + j] == rowv(pl, xi, yi + j));
            lemma_keep(cs[jj], kind, e, i, h);
            assert forall|m: int| 0 <= m < 8 implies #[trigger] t[m] == v8(hv@[jj / 2])[m + hoff(jj)] by {
                assert(v8(hv@[jj / 2])[m + hoff(jj)] == c_filter(cs[jj], kind, e, i, h)[m]);
            }
        }
        put8(v, w, x, y + j, hv[(from + j) / 2], (from + j) % 2 == 1, Ghost(cur), Ghost(t));
        proof {
            assert(cur[yi + j] == pl[yi + j]);
            assert(set_rowv(cur, xi, yi + j, t) =~~= edge_res_v(pl, xi, yi, j + 1, 0, kind, e, i, h));
        }
        j = j + 1;
    }
}

/// The loop filter across the vertical edge at column x, rows y .. y + 16,
/// in SSE2: the rows' 8 pixels transposed into 8 vectors of 16 lines,
/// filtered as a horizontal edge is, and transposed back.
pub fn vedge_x(v: &mut Vec<u8>, w: usize, x: usize, y: usize, kind: u8, e: i32, i: i32, h: i32, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), 4 <= x, x + 4 <= w, y + 16 <= pl.len(), kind <= 2,
        0 <= e, 0 <= i <= 255, 0 <= h <= 255, (if kind == 2 { e as int } else { 2 * e + i }) <= 254,
    ensures holds(final(v)@, w as nat, filter_edge(pl, x as int, y as int, 0, 16, kind as int, e as int, i as int, h as int, 0)),
        filter_edge(pl, x as int, y as int, 0, 16, kind as int, e as int, i as int, h as int, 0).len() == pl.len(),
{
    let ghost (xi, yi, ki, ei, ii, hi) = (x as int, y as int, kind as int, e as int, i as int, h as int);
    let lo = load_rows8(v, w, x, y, Ghost(pl));
    let hi8 = load_rows8(v, w, x, y + 8, Ghost(pl));
    let c = transpose16x8(&lo, &hi8);
    let ghost cs = Seq::new(16, |j: int| rowv(pl, xi, yi + j));
    proof {
        assert forall|j: int| 0 <= j < 16 implies #[trigger] lc(c@[0], c@[1], c@[2], c@[3], c@[4], c@[5], c@[6], c@[7], j) == cs[j] by {
            assert forall|k: int| 0 <= k < 8 implies #[trigger] byte(c@[k], j) == pl[yi + j][xi - 4 + k] by {
                if j < 8 { assert(byte(lo@[j], k) == pl[yi + j][xi - 4 + k]); } else { assert(byte(hi8@[j - 8], k) == pl[yi + 8 + (j - 8)][xi - 4 + k]); }
            }
            assert(lc(c@[0], c@[1], c@[2], c@[3], c@[4], c@[5], c@[6], c@[7], j) =~= cs[j]);
        }
    }
    let nv = filter_cols(&c, kind, e, i, h, Ghost(cs));
    let hv = back_cols(&nv, Ghost(cs), Ghost(ki), Ghost(ei), Ghost(ii), Ghost(hi));
    store_vlines(v, w, x, y, 16, 0, &hv, Ghost(pl), Ghost(cs), Ghost(ki), Ghost(ei), Ghost(ii), Ghost(hi));
    proof { lemma_edge_v(pl, w as nat, xi, yi, 16, 0, ki, ei, ii, hi); }
}

// ---------------------------------------------------------------- chroma
//
// U and V share a register: lanes 0 .. 8 are U's lines, 8 .. 16 V's.

/// Where the lanes of U (false) or V (true) start.
pub open spec fn half(hi: bool) -> int { if hi { 8 } else { 0 } }

/// The plane's horizontal edge at row y, columns x .. x + 8, with its rows
/// y - 4 .. y - 4 + k written.
pub open spec fn hres(p: Plane, x: int, y: int, k: int, kind: int, e: int, i: int, h: int) -> Plane {
    Seq::new(p.len(), |r: int| if y - 4 <= r < y - 4 + k {
        Seq::new(p[r].len(), |cc: int| if x <= cc < x + 8 { c_filter(col(p, cc, y), kind, e, i, h)[r - y + 4] } else { p[r][cc] })
    } else { p[r] })
}

/// A horizontal edge's 8 filtered rows, from the half `hi` of each column
/// vector, written to one plane.
fn store_hlines(v: &mut Vec<u8>, w: usize, x: usize, y: usize, nv: &[__m128i; 8], hi: bool,
    Ghost(pl): Ghost<Plane>, Ghost(cs): Ghost<Seq<Seq<u8>>>, Ghost(kind): Ghost<int>, Ghost(e): Ghost<int>, Ghost(i): Ghost<int>, Ghost(h): Ghost<int>)
    requires holds(old(v)@, w as nat, pl), 4 <= y, y + 4 <= pl.len(), x + 8 <= w,
        forall|m: int| 0 <= m < 8 ==> #[trigger] cs[m + half(hi)] == col(pl, x + m, y as int),
        forall|k: int| 0 <= k < 8 ==> #[trigger] lanes_ok(cs, k, nv@[k], kind, e, i, h),
    ensures holds(final(v)@, w as nat, edge_res(pl, x as int, y as int, 8, 0, kind, e, i, h)),
{
    let ghost (xi, yi) = (x as int, y as int);
    let ghost off: int = half(hi);
    proof { assert(rows_w(pl, w as nat)); }
    let mut k: usize = 0;
    while k < 8
        invariant k <= 8, holds(v@, w as nat, hres(pl, xi, yi, k as int, kind, e, i, h)), rows_w(pl, w as nat),
            4 <= y, y + 4 <= pl.len(), x + 8 <= w, xi == x, yi == y, off == half(hi),
            forall|m: int| 0 <= m < 8 ==> #[trigger] cs[m + off] == col(pl, x + m, y as int),
            forall|k: int| 0 <= k < 8 ==> #[trigger] lanes_ok(cs, k, nv@[k], kind, e, i, h),
        decreases 8 - k,
    {
        let ghost cur = hres(pl, xi, yi, k as int, kind, e, i, h);
        let ghost t = Seq::new(8, |m: int| c_filter(col(pl, xi + m, yi), kind, e, i, h)[k as int]);
        proof {
            assert(lanes_ok(cs, k as int, nv@[k as int], kind, e, i, h));
            assert forall|m: int| 0 <= m < 8 implies #[trigger] t[m] == v8(nv@[k as int])[m + off] by {
                assert(cs[m + off] == col(pl, xi + m, yi));
            }
        }
        put8(v, w, x + 4, y - 4 + k, nv[k], hi, Ghost(cur), Ghost(t));
        proof {
            assert(cur[yi - 4 + k] == pl[yi - 4 + k]);
            assert forall|cc: int| xi <= cc < xi + 8 implies #[trigger] t[cc - xi] == c_filter(col(pl, cc, yi), kind, e, i, h)[k as int] by {
                assert(xi + (cc - xi) == cc);
            }
            assert(set_rowv(cur, xi + 4, yi - 4 + k, t) =~~= hres(pl, xi, yi, k + 1, kind, e, i, h));
        }
        k = k + 1;
    }
    proof { assert(hres(pl, xi, yi, 8, kind, e, i, h) =~~= edge_res(pl, xi, yi, 8, 0, kind, e, i, h)); }
}

/// The loop filter across the horizontal chroma edges at row y, columns
/// x .. x + 8, of U and V at once.
pub fn hedge_uv(uv: &mut Vec<u8>, vv: &mut Vec<u8>, w: usize, x: usize, y: usize, kind: u8, e: i32, i: i32, h: i32,
    Ghost(pu): Ghost<Plane>, Ghost(pv): Ghost<Plane>)
    requires holds(old(uv)@, w as nat, pu), holds(old(vv)@, w as nat, pv), 4 <= y, y + 4 <= pu.len(), y + 4 <= pv.len(), x + 8 <= w,
        kind <= 1, 0 <= e, 0 <= i <= 255, 0 <= h <= 255, 2 * e + i <= 254,
    ensures
        holds(final(uv)@, w as nat, filter_edge(pu, x as int, y as int, 1, 8, kind as int, e as int, i as int, h as int, 0)),
        holds(final(vv)@, w as nat, filter_edge(pv, x as int, y as int, 1, 8, kind as int, e as int, i as int, h as int, 0)),
        filter_edge(pu, x as int, y as int, 1, 8, kind as int, e as int, i as int, h as int, 0).len() == pu.len(),
        filter_edge(pv, x as int, y as int, 1, 8, kind as int, e as int, i as int, h as int, 0).len() == pv.len(),
{
    let ghost (xi, yi, ki, ei, ii, hi) = (x as int, y as int, kind as int, e as int, i as int, h as int);
    let mut c: [__m128i; 8] = [sx::setzero(); 8];
    let mut k: usize = 0;
    while k < 8
        invariant k <= 8, holds(uv@, w as nat, pu), holds(vv@, w as nat, pv), 4 <= y, y + 4 <= pu.len(), y + 4 <= pv.len(), x + 8 <= w,
            forall|kk: int, j: int| 0 <= kk < k && 0 <= j < 16 ==> #[trigger] byte(c@[kk], j) ==
                if j < 8 { pu[y - 4 + kk][x + j] } else { pv[y - 4 + kk][x + j - 8] },
        decreases 8 - k,
    {
        let a = load8(uv, w, x + 4, y - 4 + k, Ghost(pu));
        let b = load8(vv, w, x + 4, y - 4 + k, Ghost(pv));
        let r = sx::unpacklo_epi64(a, b);
        c[k] = r;
        proof {
            assert forall|j: int| 0 <= j < 16 implies #[trigger] byte(r, j) ==
                if j < 8 { pu[y - 4 + k][x + j] } else { pv[y - 4 + k][x + j - 8] } by {
                lemma_byte(r, j);
                if j < 8 { lemma_byte(a, j); assert(byte(a, j) == pu[y - 4 + k][x + 4 - 4 + j]); }
                else { lemma_byte(b, j - 8); assert(byte(b, j - 8) == pv[y - 4 + k][x + 4 - 4 + (j - 8)]); }
            }
        }
        k = k + 1;
    }
    let ghost cs = Seq::new(16, |j: int| if j < 8 { col(pu, xi + j, yi) } else { col(pv, xi + j - 8, yi) });
    proof {
        assert forall|j: int| 0 <= j < 16 implies #[trigger] lc(c@[0], c@[1], c@[2], c@[3], c@[4], c@[5], c@[6], c@[7], j) == cs[j] by {
            assert forall|kk: int| 0 <= kk < 8 implies #[trigger] byte(c@[kk], j) == cs[j][kk] by {}
            assert(lc(c@[0], c@[1], c@[2], c@[3], c@[4], c@[5], c@[6], c@[7], j) =~= cs[j]);
        }
    }
    let nv = filter_cols(&c, kind, e, i, h, Ghost(cs));
    proof {
        assert forall|m: int| 0 <= m < 8 implies #[trigger] cs[m + half(false)] == col(pu, xi + m, yi) by {}
        assert forall|m: int| 0 <= m < 8 implies #[trigger] cs[m + half(true)] == col(pv, xi + m, yi) by {}
    }
    store_hlines(uv, w, x, y, &nv, false, Ghost(pu), Ghost(cs), Ghost(ki), Ghost(ei), Ghost(ii), Ghost(hi));
    store_hlines(vv, w, x, y, &nv, true, Ghost(pv), Ghost(cs), Ghost(ki), Ghost(ei), Ghost(ii), Ghost(hi));
    proof {
        assert(rows_w(pu, w as nat) && rows_w(pv, w as nat));
        lemma_edge(pu, w as nat, xi, yi, 8, 0, ki, ei, ii, hi);
        lemma_edge(pv, w as nat, xi, yi, 8, 0, ki, ei, ii, hi);
    }
}

/// The loop filter across the vertical chroma edges at column x, rows
/// y .. y + 8, of U and V at once: U's 8 rows and V's 8 fill the 16 lanes.
pub fn vedge_uv(uv: &mut Vec<u8>, vv: &mut Vec<u8>, w: usize, x: usize, y: usize, kind: u8, e: i32, i: i32, h: i32,
    Ghost(pu): Ghost<Plane>, Ghost(pv): Ghost<Plane>)
    requires holds(old(uv)@, w as nat, pu), holds(old(vv)@, w as nat, pv), 4 <= x, x + 4 <= w, y + 8 <= pu.len(), y + 8 <= pv.len(),
        kind <= 1, 0 <= e, 0 <= i <= 255, 0 <= h <= 255, 2 * e + i <= 254,
    ensures
        holds(final(uv)@, w as nat, filter_edge(pu, x as int, y as int, 0, 8, kind as int, e as int, i as int, h as int, 0)),
        holds(final(vv)@, w as nat, filter_edge(pv, x as int, y as int, 0, 8, kind as int, e as int, i as int, h as int, 0)),
        filter_edge(pu, x as int, y as int, 0, 8, kind as int, e as int, i as int, h as int, 0).len() == pu.len(),
        filter_edge(pv, x as int, y as int, 0, 8, kind as int, e as int, i as int, h as int, 0).len() == pv.len(),
{
    let ghost (xi, yi, ki, ei, ii, hi) = (x as int, y as int, kind as int, e as int, i as int, h as int);
    let lo = load_rows8(uv, w, x, y, Ghost(pu));
    let hi8 = load_rows8(vv, w, x, y, Ghost(pv));
    let c = transpose16x8(&lo, &hi8);
    let ghost cs = Seq::new(16, |j: int| if j < 8 { rowv(pu, xi, yi + j) } else { rowv(pv, xi, yi + j - 8) });
    proof {
        assert forall|j: int| 0 <= j < 16 implies #[trigger] lc(c@[0], c@[1], c@[2], c@[3], c@[4], c@[5], c@[6], c@[7], j) == cs[j] by {
            assert forall|k: int| 0 <= k < 8 implies #[trigger] byte(c@[k], j) == cs[j][k] by {
                if j < 8 { assert(byte(lo@[j], k) == pu[yi + j][xi - 4 + k]); } else { assert(byte(hi8@[j - 8], k) == pv[yi + (j - 8)][xi - 4 + k]); }
            }
            assert(lc(c@[0], c@[1], c@[2], c@[3], c@[4], c@[5], c@[6], c@[7], j) =~= cs[j]);
        }
    }
    let nv = filter_cols(&c, kind, e, i, h, Ghost(cs));
    let hv = back_cols(&nv, Ghost(cs), Ghost(ki), Ghost(ei), Ghost(ii), Ghost(hi));
    proof {
        assert forall|j: int| 0 <= j < 8 implies #[trigger] cs[0 + j] == rowv(pu, xi, yi + j) by {}
        assert forall|j: int| 0 <= j < 8 implies #[trigger] cs[8 + j] == rowv(pv, xi, yi + j) by {}
    }
    store_vlines(uv, w, x, y, 8, 0, &hv, Ghost(pu), Ghost(cs), Ghost(ki), Ghost(ei), Ghost(ii), Ghost(hi));
    store_vlines(vv, w, x, y, 8, 8, &hv, Ghost(pv), Ghost(cs), Ghost(ki), Ghost(ei), Ghost(ii), Ghost(hi));
    proof {
        assert(rows_w(pu, w as nat) && rows_w(pv, w as nat));
        lemma_edge_v(pu, w as nat, xi, yi, 8, 0, ki, ei, ii, hi);
        lemma_edge_v(pv, w as nat, xi, yi, 8, 0, ki, ei, ii, hi);
    }
}

// ------------------------------------- the three inner vertical edges

/// The block's 16 columns x .. x + 16, rows y .. y + 16, as vectors whose
/// lane j is row y + j: `cols` holds plane `g` there.
pub open spec fn cols_hold(cols: Seq<__m128i>, g: Plane, x: int, y: int) -> bool {
    &&& cols.len() == 16
    &&& forall|k: int, j: int| 0 <= k < 16 && 0 <= j < 16 ==> #[trigger] byte(cols[k], j) == g[y + j][x + k]
}

/// Rows y .. y + 16, pixels x .. x + 16, loaded and transposed.
fn load_cols16(v: &Vec<u8>, w: usize, x: usize, y: usize, Ghost(pl): Ghost<Plane>) -> (c: [__m128i; 16])
    requires holds(v@, w as nat, pl), x + 16 <= w, y + 16 <= pl.len(),
    ensures cols_hold(c@, pl, x as int, y as int),
{
    let mut r: [__m128i; 16] = [sx::setzero(); 16];
    let mut j: usize = 0;
    while j < 16
        invariant j <= 16, holds(v@, w as nat, pl), x + 16 <= w, y + 16 <= pl.len(),
            forall|jj: int, k: int| 0 <= jj < j && 0 <= k < 16 ==> #[trigger] byte(r@[jj], k) == pl[y + jj][x + k],
        decreases 16 - j,
    {
        let a = load_row(v, w, x, y + j, Ghost(pl));
        r[j] = a;
        j = j + 1;
    }
    let lo = [r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7]];
    let hi = [r[8], r[9], r[10], r[11], r[12], r[13], r[14], r[15]];
    let c0 = transpose16x8h(&lo, &hi, false);
    let c1 = transpose16x8h(&lo, &hi, true);
    let c = [c0[0], c0[1], c0[2], c0[3], c0[4], c0[5], c0[6], c0[7], c1[0], c1[1], c1[2], c1[3], c1[4], c1[5], c1[6], c1[7]];
    proof {
        assert forall|k: int, j: int| 0 <= k < 16 && 0 <= j < 16 implies #[trigger] byte(c@[k], j) == pl[y + j][x + k] by {
            if k < 8 {
                if j < 8 { assert(byte(lo@[j], k) == pl[y + j][x + k]); } else { assert(byte(hi@[j - 8], k) == pl[y + 8 + (j - 8)][x + k]); }
            } else {
                if j < 8 { assert(byte(lo@[j], 8 + (k - 8)) == pl[y + j][x + k]); } else { assert(byte(hi@[j - 8], 8 + (k - 8)) == pl[y + 8 + (j - 8)][x + k]); }
            }
        }
    }
    c
}

/// One inner edge (subblock filter) at column x + off + 4 on the columns:
/// columns off .. off + 8 filtered, the plane as `filter_edge` leaves it.
fn vedge_step(c: &[__m128i; 16], off: usize, e: i32, i: i32, h: i32, Ghost(g): Ghost<Plane>, Ghost(w): Ghost<nat>,
    Ghost(x): Ghost<int>, Ghost(y): Ghost<int>) -> (r: [__m128i; 16])
    requires off == 0 || off == 4 || off == 8, cols_hold(c@, g, x, y), rows_w(g, w), 0 <= x, x + 16 <= w, 0 <= y, y + 16 <= g.len(),
        0 <= e, 0 <= i <= 255, 0 <= h <= 255, 2 * e + i <= 254,
    ensures cols_hold(r@, filter_edge(g, x + off + 4, y, 0, 16, 1, e as int, i as int, h as int, 0), x, y),
        filter_edge(g, x + off + 4, y, 0, 16, 1, e as int, i as int, h as int, 0).len() == g.len(),
        rows_w(filter_edge(g, x + off + 4, y, 0, 16, 1, e as int, i as int, h as int, 0), w),
{
    let ghost xe = x + off + 4;
    let ghost (ei, ii, hi) = (e as int, i as int, h as int);
    let c8 = [c[off], c[off + 1], c[off + 2], c[off + 3], c[off + 4], c[off + 5], c[off + 6], c[off + 7]];
    let ghost cs = Seq::new(16, |j: int| rowv(g, xe, y + j));
    proof {
        assert forall|j: int| 0 <= j < 16 implies #[trigger] lc(c8@[0], c8@[1], c8@[2], c8@[3], c8@[4], c8@[5], c8@[6], c8@[7], j) == cs[j] by {
            assert forall|k: int| 0 <= k < 8 implies #[trigger] byte(c8@[k], j) == cs[j][k] by {
                assert(byte(c@[off + k], j) == g[y + j][x + off + k]);
                assert(xe - 4 + k == x + off + k);
            }
            assert(lc(c8@[0], c8@[1], c8@[2], c8@[3], c8@[4], c8@[5], c8@[6], c8@[7], j) =~= cs[j]);
        }
    }
    let nv = filter_cols(&c8, 1, e, i, h, Ghost(cs));
    let mut r = *c;
    r[off] = nv[0]; r[off + 1] = nv[1]; r[off + 2] = nv[2]; r[off + 3] = nv[3];
    r[off + 4] = nv[4]; r[off + 5] = nv[5]; r[off + 6] = nv[6]; r[off + 7] = nv[7];
    proof {
        lemma_edge_v(g, w, xe, y, 16, 0, 1, ei, ii, hi);
        let g2 = edge_res_v(g, xe, y, 16, 0, 1, ei, ii, hi);
        assert forall|k: int, j: int| 0 <= k < 16 && 0 <= j < 16 implies #[trigger] byte(r@[k], j) == g2[y + j][x + k] by {
            if off <= k < off + 8 {
                assert(r@[k] == nv@[k - off]);
                assert(lanes_ok(cs, k - off, nv@[k - off], 1, ei, ii, hi));
                lemma_byte(nv@[k - off], j);
                assert(x + k - xe + 4 == k - off);
            } else {
                assert(r@[k] == c@[k]);
            }
        }
        assert(rows_w(g2, w));
    }
    r
}

/// Eight column vectors transposed back: line j is the half `hoff(j)` of
/// vector j / 2.
fn back8(c: &[__m128i; 8]) -> (hv: [__m128i; 8])
    ensures forall|j: int, m: int| 0 <= j < 16 && 0 <= m < 8 ==> #[trigger] v8(hv@[j / 2])[m + hoff(j)] == byte(c@[m], j),
{
    let t0 = transpose8x8(c, false);
    let t1 = transpose8x8(c, true);
    let hv = [t0[0], t0[1], t0[2], t0[3], t1[0], t1[1], t1[2], t1[3]];
    proof {
        assert forall|j: int, m: int| 0 <= j < 16 && 0 <= m < 8 implies #[trigger] v8(hv@[j / 2])[m + hoff(j)] == byte(c@[m], j) by {
            let mm = m + hoff(j);
            lemma_byte(hv@[j / 2], mm);
            assert(mm % 8 == m && mm / 8 == j % 2);
            if j < 8 {
                assert(byte(t0@[j / 2], mm) == byte(c@[mm % 8], 2 * (j / 2) + mm / 8));
            } else {
                assert(byte(t1@[j / 2 - 4], mm) == byte(c@[mm % 8], 8 + 2 * (j / 2 - 4) + mm / 8));
            }
        }
    }
    hv
}

/// Write the columns back as rows y .. y + 16, pixels x .. x + 16.
fn store_cols16(v: &mut Vec<u8>, w: usize, x: usize, y: usize, c: &[__m128i; 16], Ghost(pl): Ghost<Plane>, Ghost(g): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), x + 16 <= w, y + 16 <= pl.len(), g.len() == pl.len(),
        cols_hold(c@, g, x as int, y as int),
        forall|r: int| 0 <= r < pl.len() && !(y <= r < y + 16) ==> #[trigger] g[r] == pl[r],
        forall|r: int| y <= r < y + 16 ==> (#[trigger] g[r]).len() == w,
        forall|r: int, cc: int| y <= r < y + 16 && 0 <= cc < w && !(x <= cc < x + 16) ==> #[trigger] g[r][cc] == pl[r][cc],
    ensures holds(final(v)@, w as nat, g),
{
    let lo = [c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]];
    let hi = [c[8], c[9], c[10], c[11], c[12], c[13], c[14], c[15]];
    let hl = back8(&lo);
    let hh = back8(&hi);
    let ghost mut cur = pl;
    let mut j: usize = 0;
    while j < 16
        invariant j <= 16, x + 16 <= w, y + 16 <= pl.len(), g.len() == pl.len(), cur.len() == pl.len(),
            holds(v@, w as nat, cur),
            cols_hold(c@, g, x as int, y as int),
            forall|jj: int, m: int| 0 <= jj < 16 && 0 <= m < 8 ==> #[trigger] v8(hl@[jj / 2])[m + hoff(jj)] == byte(lo@[m], jj),
            forall|jj: int, m: int| 0 <= jj < 16 && 0 <= m < 8 ==> #[trigger] v8(hh@[jj / 2])[m + hoff(jj)] == byte(hi@[m], jj),
            lo@ == c@.subrange(0, 8), hi@ == c@.subrange(8, 16),
            forall|r: int| 0 <= r < pl.len() && !(y <= r < y + j) ==> #[trigger] cur[r] == pl[r],
            forall|r: int| y <= r < y + j ==> #[trigger] cur[r] == g[r],
            forall|r: int| 0 <= r < pl.len() && !(y <= r < y + 16) ==> #[trigger] g[r] == pl[r],
            forall|r: int| y <= r < y + 16 ==> (#[trigger] g[r]).len() == w,
            forall|r: int, cc: int| y <= r < y + 16 && 0 <= cc < w && !(x <= cc < x + 16) ==> #[trigger] g[r][cc] == pl[r][cc],
        decreases 16 - j,
    {
        let row = if j % 2 == 0 { sx::unpacklo_epi64(hl[j / 2], hh[j / 2]) } else { sx::unpackhi_epi64(hl[j / 2], hh[j / 2]) };
        proof {
            assert forall|k: int| 0 <= k < 16 implies #[trigger] v8(row)[k] == g[y + j][x + k] by {
                let jj = j as int;
                if k < 8 {
                    assert(v8(hl@[jj / 2])[k + hoff(jj)] == byte(lo@[k], jj));
                    assert(lo@[k] == c@[k]);
                } else {
                    assert(v8(hh@[jj / 2])[(k - 8) + hoff(jj)] == byte(hi@[k - 8], jj));
                    assert(hi@[k - 8] == c@[k]);
                }
            }
        }
        store_row(v, w, x, y + j, row, Ghost(cur));
        proof {
            let nc = set_row(cur, (y + j) as int, x as int, v8(row));
            assert(nc[(y + j) as int] =~= g[(y + j) as int]);
            cur = nc;
        }
        j = j + 1;
    }
    proof { assert(cur =~~= g); }
}

/// The three inner vertical edges of a macroblock (subblock filter, at
/// columns x + 4, x + 8 and x + 12, rows y .. y + 16), in SSE2 with one
/// transpose each way, as libwebp's HFilter16i: `filter_edge` three times.
pub fn vedge3_x(v: &mut Vec<u8>, w: usize, x: usize, y: usize, e: i32, i: i32, h: i32, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), x + 16 <= w, y + 16 <= pl.len(),
        0 <= e, 0 <= i <= 255, 0 <= h <= 255, 2 * e + i <= 254,
    ensures ({
        let (ei, ii, hi) = (e as int, i as int, h as int);
        let g1 = filter_edge(pl, x + 4, y as int, 0, 16, 1, ei, ii, hi, 0);
        let g2 = filter_edge(g1, x + 8, y as int, 0, 16, 1, ei, ii, hi, 0);
        let g3 = filter_edge(g2, x + 12, y as int, 0, 16, 1, ei, ii, hi, 0);
        &&& holds(final(v)@, w as nat, g3) && g1.len() == pl.len() && g2.len() == pl.len() && g3.len() == pl.len()
    }),
{
    let ghost (xi, yi, wn) = (x as int, y as int, w as nat);
    proof { assert(rows_w(pl, wn)); }
    let c0 = load_cols16(v, w, x, y, Ghost(pl));
    let c1 = vedge_step(&c0, 0, e, i, h, Ghost(pl), Ghost(wn), Ghost(xi), Ghost(yi));
    let ghost g1 = filter_edge(pl, xi + 4, yi, 0, 16, 1, e as int, i as int, h as int, 0);
    let c2 = vedge_step(&c1, 4, e, i, h, Ghost(g1), Ghost(wn), Ghost(xi), Ghost(yi));
    let ghost g2 = filter_edge(g1, xi + 8, yi, 0, 16, 1, e as int, i as int, h as int, 0);
    let c3 = vedge_step(&c2, 8, e, i, h, Ghost(g2), Ghost(wn), Ghost(xi), Ghost(yi));
    let ghost g3 = filter_edge(g2, xi + 12, yi, 0, 16, 1, e as int, i as int, h as int, 0);
    proof {
        // each edge changes only rows y .. y + 16, pixels x .. x + 16
        lemma_edge_v(pl, wn, xi + 4, yi, 16, 0, 1, e as int, i as int, h as int);
        lemma_edge_v(g1, wn, xi + 8, yi, 16, 0, 1, e as int, i as int, h as int);
        lemma_edge_v(g2, wn, xi + 12, yi, 16, 0, 1, e as int, i as int, h as int);
        assert forall|r: int| 0 <= r < pl.len() && !(yi <= r < yi + 16) implies #[trigger] g3[r] == pl[r] by {}
        assert forall|r: int, cc: int| yi <= r < yi + 16 && 0 <= cc < w && !(xi <= cc < xi + 16) implies #[trigger] g3[r][cc] == pl[r][cc] by {}
    }
    store_cols16(v, w, x, y, &c3, Ghost(pl), Ghost(g3));
}

} // verus!
