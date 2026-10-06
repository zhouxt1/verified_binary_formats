//! The loop filter (RFC 6386 20.6, dixie_loopfilter.c), proved to follow
//! `spec::loop_filter`.
use vstd::prelude::*;
use super::spec::*;
use super::plane::*;
use super::recon::clamp255_x;
use super::hdr::*;
use super::modes::*;

verus! {

fn s8_x(x: i32) -> (r: i32)
    ensures r as int == s8(x as int),
{
    if x < -128 { -128 } else if x > 127 { 127 } else { x }
}

fn absd_x(a: i32, b: i32) -> (r: i32)
    requires -1000 <= a <= 1000, -1000 <= b <= 1000,
    ensures r as int == absd(a as int, b as int),
{
    if a >= b { a - b } else { b - a }
}

/// `x >> k` for k = 1, 3, 7: a division that floors.
fn shr(x: i32, k: u32) -> (r: i32)
    requires k == 1 || k == 3 || k == 7,
    ensures r as int == (x as int) / (if k == 1 { 2int } else if k == 3 { 8 } else { 128 }),
{
    let r = x >> k;
    proof {
        if k == 1 { assert(r as int == (x as int) / 2) by (bit_vector) requires r == x >> 1u32; }
        else if k == 3 { assert(r as int == (x as int) / 8) by (bit_vector) requires r == x >> 3u32; }
        else { assert(r as int == (x as int) / 128) by (bit_vector) requires r == x >> 7u32; }
    }
    r
}

/// The plane position of pixel `k` across the edge at (x, y).
pub open spec fn at(x: int, y: int, dir: int, k: int) -> (int, int) {
    if dir == 0 { (x + k, y) } else { (x, y + k) }
}

/// The 8 pixels across an edge are in the plane.
pub open spec fn line_ok(pl: Plane, w: nat, x: int, y: int, dir: int) -> bool {
    &&& dir == 0 || dir == 1
    &&& if dir == 0 { 4 <= x && x + 4 <= w && 0 <= y < pl.len() } else { 4 <= y && y + 4 <= pl.len() && 0 <= x < w }
}

fn px_x(v: &Vec<u8>, w: usize, x: usize, y: usize, dir: usize, k: i32, Ghost(pl): Ghost<Plane>) -> (r: i32)
    requires holds(v@, w as nat, pl), line_ok(pl, w as nat, x as int, y as int, dir as int), -4 <= k <= 3,
    ensures r as int == px(pl, x as int, y as int, dir as int, k as int), 0 <= r <= 255,
{
    if dir == 0 { get(v, w, (x as i32 + k) as usize, y, Ghost(pl)) as i32 }
    else { get(v, w, x, (y as i32 + k) as usize, Ghost(pl)) as i32 }
}

fn setpx_x(v: &mut Vec<u8>, w: usize, x: usize, y: usize, dir: usize, k: i32, val: u8, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), line_ok(pl, w as nat, x as int, y as int, dir as int), -4 <= k <= 3,
    ensures holds(final(v)@, w as nat, setpx(pl, x as int, y as int, dir as int, k as int, val)),
        setpx(pl, x as int, y as int, dir as int, k as int, val).len() == pl.len(),
{
    if dir == 0 { set(v, w, (x as i32 + k) as usize, y, val, Ghost(pl)); }
    else { set(v, w, x, (y as i32 + k) as usize, val, Ghost(pl)); }
}

/// One pixel line across an edge (`filter_line`).
pub fn filter_line_x(v: &mut Vec<u8>, w: usize, x: usize, y: usize, dir: usize, kind: u8, e: i32, i: i32, h: i32, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), line_ok(pl, w as nat, x as int, y as int, dir as int), kind <= 2,
        0 <= e <= 200, 0 <= i <= 200, 0 <= h <= 2,
    ensures holds(final(v)@, w as nat, filter_line(pl, x as int, y as int, dir as int, kind as int, e as int, i as int, h as int)),
        filter_line(pl, x as int, y as int, dir as int, kind as int, e as int, i as int, h as int).len() == pl.len(),
{
    proof { reveal(filter_line); }
    let p3 = px_x(v, w, x, y, dir, -4, Ghost(pl));
    let p2 = px_x(v, w, x, y, dir, -3, Ghost(pl));
    let p1 = px_x(v, w, x, y, dir, -2, Ghost(pl));
    let p0 = px_x(v, w, x, y, dir, -1, Ghost(pl));
    let q0 = px_x(v, w, x, y, dir, 0, Ghost(pl));
    let q1 = px_x(v, w, x, y, dir, 1, Ghost(pl));
    let q2 = px_x(v, w, x, y, dir, 2, Ghost(pl));
    let q3 = px_x(v, w, x, y, dir, 3, Ghost(pl));
    let lim = if kind == 2 { e } else { 2 * e + i };
    let simple = absd_x(p0, q0) * 2 + shr(absd_x(p1, q1), 1) <= lim;
    let normal = simple && absd_x(p3, p2) <= i && absd_x(p2, p1) <= i && absd_x(p1, p0) <= i
        && absd_x(q3, q2) <= i && absd_x(q2, q1) <= i && absd_x(q1, q0) <= i;
    let hev = absd_x(p1, p0) > h || absd_x(q1, q0) > h;
    let filt = if kind == 2 { simple } else { normal };
    if !filt {
        return;
    }
    if kind == 0 && !hev {
        // filter_mb_edge
        let wv = s8_x(s8_x(p1 - q1) + 3 * (q0 - p0));
        let a0 = shr(27 * wv + 63, 7);
        let a1 = shr(18 * wv + 63, 7);
        let a2 = shr(9 * wv + 63, 7);
        let ghost g0 = pl;
        setpx_x(v, w, x, y, dir, -1, clamp255_x(p0 + a0), Ghost(g0));
        let ghost g1 = setpx(g0, x as int, y as int, dir as int, -1, clamp255(p0 as int + a0 as int));
        setpx_x(v, w, x, y, dir, 0, clamp255_x(q0 - a0), Ghost(g1));
        let ghost g2 = setpx(g1, x as int, y as int, dir as int, 0, clamp255(q0 as int - a0 as int));
        setpx_x(v, w, x, y, dir, -2, clamp255_x(p1 + a1), Ghost(g2));
        let ghost g3 = setpx(g2, x as int, y as int, dir as int, -2, clamp255(p1 as int + a1 as int));
        setpx_x(v, w, x, y, dir, 1, clamp255_x(q1 - a1), Ghost(g3));
        let ghost g4 = setpx(g3, x as int, y as int, dir as int, 1, clamp255(q1 as int - a1 as int));
        setpx_x(v, w, x, y, dir, -3, clamp255_x(p2 + a2), Ghost(g4));
        let ghost g5 = setpx(g4, x as int, y as int, dir as int, -3, clamp255(p2 as int + a2 as int));
        setpx_x(v, w, x, y, dir, 2, clamp255_x(q2 - a2), Ghost(g5));
    } else {
        // filter_common
        let outer = kind != 1 || hev;
        let a = s8_x(3 * (q0 - p0) + if outer { s8_x(p1 - q1) } else { 0 });
        let f1 = shr(if a + 4 > 127 { 127 } else { a + 4 }, 3);
        let f2 = shr(if a + 3 > 127 { 127 } else { a + 3 }, 3);
        let ghost g0 = pl;
        setpx_x(v, w, x, y, dir, -1, clamp255_x(p0 + f2), Ghost(g0));
        let ghost g1 = setpx(g0, x as int, y as int, dir as int, -1, clamp255(p0 as int + f2 as int));
        setpx_x(v, w, x, y, dir, 0, clamp255_x(q0 - f1), Ghost(g1));
        if !outer {
            let ghost g2 = setpx(g1, x as int, y as int, dir as int, 0, clamp255(q0 as int - f1 as int));
            let a2 = shr(f1 + 1, 1);
            setpx_x(v, w, x, y, dir, -2, clamp255_x(p1 + a2), Ghost(g2));
            let ghost g3 = setpx(g2, x as int, y as int, dir as int, -2, clamp255(p1 as int + a2 as int));
            setpx_x(v, w, x, y, dir, 1, clamp255_x(q1 - a2), Ghost(g3));
        }
    }
}

/// The lines of an edge (`filter_edge`, from line 0).
fn filter_edge_x(v: &mut Vec<u8>, w: usize, x: usize, y: usize, dir: usize, n: usize, kind: u8, e: i32, i: i32, h: i32, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), kind <= 2, 0 <= e <= 200, 0 <= i <= 200, 0 <= h <= 2, n <= 16,
        dir == 0 || dir == 1,
        dir == 0 ==> 4 <= x && x + 4 <= w && y + n <= pl.len(),
        dir == 1 ==> 4 <= y && y + 4 <= pl.len() && x + n <= w,
    ensures
        holds(final(v)@, w as nat, filter_edge(pl, x as int, y as int, dir as int, n as int, kind as int, e as int, i as int, h as int, 0)),
        filter_edge(pl, x as int, y as int, dir as int, n as int, kind as int, e as int, i as int, h as int, 0).len() == pl.len(),
{
    let mut k: usize = 0;
    let ghost mut cur = pl;
    while k < n
        invariant
            holds(v@, w as nat, cur), cur.len() == pl.len(), kind <= 2, 0 <= e <= 200, 0 <= i <= 200, 0 <= h <= 2, n <= 16, k <= n,
            dir == 0 || dir == 1,
            dir == 0 ==> 4 <= x && x + 4 <= w && y + n <= pl.len(),
            dir == 1 ==> 4 <= y && y + 4 <= pl.len() && x + n <= w,
            filter_edge(cur, x as int, y as int, dir as int, n as int, kind as int, e as int, i as int, h as int, k as int)
                == filter_edge(pl, x as int, y as int, dir as int, n as int, kind as int, e as int, i as int, h as int, 0),
        decreases n - k,
    {
        let (lx, ly) = if dir == 0 { (x, y + k) } else { (x + k, y) };
        filter_line_x(v, w, lx, ly, dir, kind, e, i, h, Ghost(cur));
        proof { cur = filter_line(cur, lx as int, ly as int, dir as int, kind as int, e as int, i as int, h as int); }
        k = k + 1;
    }
}

/// A horizontal edge across a macroblock's 16 columns: in SSE2 where there
/// is SSE2 (`lfx::hedge_x`), else line by line.
fn hedge16(v: &mut Vec<u8>, w: usize, x: usize, y: usize, kind: u8, e: i32, i: i32, h: i32, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), kind <= 2, 0 <= e <= 200, 0 <= i <= 63, 0 <= h <= 2,
        (if kind == 2 { e as int } else { 2 * e + i }) <= 254,
        4 <= y && y + 4 <= pl.len() && x + 16 <= w,
    ensures
        holds(final(v)@, w as nat, filter_edge(pl, x as int, y as int, 1, 16, kind as int, e as int, i as int, h as int, 0)),
        filter_edge(pl, x as int, y as int, 1, 16, kind as int, e as int, i as int, h as int, 0).len() == pl.len(),
{
    #[cfg(target_arch = "x86_64")]
    super::lfx::hedge_x(v, w, x, y, kind, e, i, h, Ghost(pl));
    #[cfg(not(target_arch = "x86_64"))]
    filter_edge_x(v, w, x, y, 1, 16, kind, e, i, h, Ghost(pl));
}

/// A vertical edge down a macroblock's 16 rows: in SSE2 where there is
/// SSE2 (`lfx::vedge_x`), else line by line.
fn vedge16(v: &mut Vec<u8>, w: usize, x: usize, y: usize, kind: u8, e: i32, i: i32, h: i32, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), kind <= 2, 0 <= e <= 200, 0 <= i <= 63, 0 <= h <= 2,
        (if kind == 2 { e as int } else { 2 * e + i }) <= 254,
        4 <= x && x + 4 <= w && y + 16 <= pl.len(),
    ensures
        holds(final(v)@, w as nat, filter_edge(pl, x as int, y as int, 0, 16, kind as int, e as int, i as int, h as int, 0)),
        filter_edge(pl, x as int, y as int, 0, 16, kind as int, e as int, i as int, h as int, 0).len() == pl.len(),
{
    #[cfg(target_arch = "x86_64")]
    super::lfx::vedge_x(v, w, x, y, kind, e, i, h, Ghost(pl));
    #[cfg(not(target_arch = "x86_64"))]
    filter_edge_x(v, w, x, y, 0, 16, kind, e, i, h, Ghost(pl));
}

/// A macroblock's three inner vertical luma edges: in SSE2 with one
/// transpose each way where there is SSE2 (`lfx::vedge3_x`), else line by
/// line.
fn vedge3(v: &mut Vec<u8>, w: usize, x: usize, y: usize, e: i32, i: i32, h: i32, Ghost(pl): Ghost<Plane>)
    requires holds(old(v)@, w as nat, pl), 0 <= e <= 63, 0 <= i <= 63, 0 <= h <= 2, x + 16 <= w, y + 16 <= pl.len(),
    ensures ({
        let (ei, ii, hi) = (e as int, i as int, h as int);
        let g1 = filter_edge(pl, x + 4, y as int, 0, 16, 1, ei, ii, hi, 0);
        let g2 = filter_edge(g1, x + 8, y as int, 0, 16, 1, ei, ii, hi, 0);
        let g3 = filter_edge(g2, x + 12, y as int, 0, 16, 1, ei, ii, hi, 0);
        &&& holds(final(v)@, w as nat, g3) && g1.len() == pl.len() && g2.len() == pl.len() && g3.len() == pl.len()
    }),
{
    #[cfg(target_arch = "x86_64")]
    super::lfx::vedge3_x(v, w, x, y, e, i, h, Ghost(pl));
    #[cfg(not(target_arch = "x86_64"))]
    {
        let ghost (ei, ii, hi) = (e as int, i as int, h as int);
        vedge16(v, w, x + 4, y, 1, e, i, h, Ghost(pl));
        let ghost g1 = filter_edge(pl, x + 4, y as int, 0, 16, 1, ei, ii, hi, 0);
        vedge16(v, w, x + 8, y, 1, e, i, h, Ghost(g1));
        let ghost g2 = filter_edge(g1, x + 8, y as int, 0, 16, 1, ei, ii, hi, 0);
        vedge16(v, w, x + 12, y, 1, e, i, h, Ghost(g2));
    }
}

/// A chroma edge of U and V at once (`dir` 0: vertical, 1: horizontal):
/// in SSE2 where there is SSE2 (`lfx::vedge_uv`, `lfx::hedge_uv`), else
/// line by line.
fn edge_uv(uv: &mut Vec<u8>, vv: &mut Vec<u8>, w: usize, x: usize, y: usize, dir: usize, kind: u8, e: i32, i: i32, h: i32,
    Ghost(pu): Ghost<Plane>, Ghost(pv): Ghost<Plane>)
    requires holds(old(uv)@, w as nat, pu), holds(old(vv)@, w as nat, pv), kind <= 1, 0 <= e <= 200, 0 <= i <= 63, 0 <= h <= 2,
        2 * e + i <= 254, dir == 0 || dir == 1,
        dir == 0 ==> 4 <= x && x + 4 <= w && y + 8 <= pu.len() && y + 8 <= pv.len(),
        dir == 1 ==> 4 <= y && y + 4 <= pu.len() && y + 4 <= pv.len() && x + 8 <= w,
    ensures
        holds(final(uv)@, w as nat, filter_edge(pu, x as int, y as int, dir as int, 8, kind as int, e as int, i as int, h as int, 0)),
        holds(final(vv)@, w as nat, filter_edge(pv, x as int, y as int, dir as int, 8, kind as int, e as int, i as int, h as int, 0)),
        filter_edge(pu, x as int, y as int, dir as int, 8, kind as int, e as int, i as int, h as int, 0).len() == pu.len(),
        filter_edge(pv, x as int, y as int, dir as int, 8, kind as int, e as int, i as int, h as int, 0).len() == pv.len(),
{
    #[cfg(target_arch = "x86_64")]
    {
        if dir == 0 { super::lfx::vedge_uv(uv, vv, w, x, y, kind, e, i, h, Ghost(pu), Ghost(pv)); }
        else { super::lfx::hedge_uv(uv, vv, w, x, y, kind, e, i, h, Ghost(pu), Ghost(pv)); }
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        filter_edge_x(uv, w, x, y, dir, 8, kind, e, i, h, Ghost(pu));
        filter_edge_x(vv, w, x, y, dir, 8, kind, e, i, h, Ghost(pv));
    }
}

/// `filter_level`, `interior_limit` and `hev_threshold`.
fn filter_params_x(hd: &HdrX, mb: &MbX) -> (r: (i32, i32, i32))
    requires hd.wf(), mb.wf(),
    ensures
        r.0 as int == filter_level(hd.view(), mb.view()), r.1 as int == interior_limit(hd.view(), r.0 as int),
        r.2 as int == hev_threshold(r.0 as int), 0 <= r.0 <= 63, 1 <= r.1 <= 63, 0 <= r.2 <= 2,
{
    let seg = mb.segment as usize;
    let base = if !hd.seg.enabled { hd.filt.level } else if hd.seg.abs { hd.seg.lf[seg] } else { hd.filt.level + hd.seg.lf[seg] };
    let l1 = if base < 0 { 0 } else if base > 63 { 63 } else { base };
    let l2 = if hd.filt.delta { l1 + hd.filt.ref_delta[0] + if mb.y_mode == 4 { hd.filt.mode_delta[0] } else { 0 } } else { l1 };
    let e = if l2 < 0 { 0 } else if l2 > 63 { 63 } else { l2 };
    let sh = hd.filt.sharpness;
    let i1 = if sh != 0 { e / (if sh > 4 { 4 } else { 2 }) } else { e };
    let i2 = if sh != 0 && i1 > 9 - sh { 9 - sh } else { i1 };
    let i = if i2 < 1 { 1 } else { i2 };
    let h = (if e >= 15 { 1 } else { 0 }) + (if e >= 40 { 1 } else { 0 });
    proof {
        assert(ints(hd.seg.lf@)[seg as int] == hd.seg.lf@[seg as int] as int);
        assert(ints(hd.filt.ref_delta@)[0] == hd.filt.ref_delta@[0] as int);
        assert(ints(hd.filt.mode_delta@)[0] == hd.filt.mode_delta@[0] as int);
    }
    (e, i, h)
}

/// A frame's three planes, held by the three buffers.
pub open spec fn holds3(y: Seq<u8>, u: Seq<u8>, v: Seq<u8>, mbw: nat, mbh: nat, pl: Planes) -> bool {
    &&& holds(y, mbw * 16, pl.y) && pl.y.len() == mbh * 16
    &&& holds(u, mbw * 8, pl.u) && pl.u.len() == mbh * 8
    &&& holds(v, mbw * 8, pl.v) && pl.v.len() == mbh * 8
}

/// One macroblock's loop filter (`filter_mb`).
fn filter_mb_x(hd: &HdrX, mb: &MbX, nz: bool, x: usize, y: usize, mbw: usize, mbh: usize,
    yv: &mut Vec<u8>, uv: &mut Vec<u8>, vv: &mut Vec<u8>, Ghost(pl): Ghost<Planes>)
    requires hd.wf(), mb.wf(), x < mbw, y < mbh, 1 <= mbw <= 1024, 1 <= mbh <= 1024,
        holds3(old(yv)@, old(uv)@, old(vv)@, mbw as nat, mbh as nat, pl),
    ensures holds3(final(yv)@, final(uv)@, final(vv)@, mbw as nat, mbh as nat,
        filter_mb(hd.view(), mb.view(), nz, x as int, y as int, pl)),
{
    proof { reveal(filter_mb); }
    let (e, i, h) = filter_params_x(hd, mb);
    let inner = nz || mb.y_mode == 4;
    let (yx, yy, cx, cy) = (x * 16, y * 16, x * 8, y * 8);
    let yw = mbw * 16;
    let cw = mbw * 8;
    if e == 0 {
        return;
    }
    if hd.filt.simple {
        let mbl = (e + 2) * 2 + i;
        let bl = e * 2 + i;
        let ghost p0 = pl.y;
        let ghost mut cur = p0;
        if x > 0 {
            vedge16(yv, yw, yx, yy, 2, mbl, 0, 0, Ghost(cur));
            proof { cur = filter_edge(cur, yx as int, yy as int, 0, 16, 2, mbl as int, 0, 0, 0); }
        }
        if inner {
            vedge16(yv, yw, yx + 4, yy, 2, bl, 0, 0, Ghost(cur));
            proof { cur = filter_edge(cur, yx + 4, yy as int, 0, 16, 2, bl as int, 0, 0, 0); }
            vedge16(yv, yw, yx + 8, yy, 2, bl, 0, 0, Ghost(cur));
            proof { cur = filter_edge(cur, yx + 8, yy as int, 0, 16, 2, bl as int, 0, 0, 0); }
            vedge16(yv, yw, yx + 12, yy, 2, bl, 0, 0, Ghost(cur));
            proof { cur = filter_edge(cur, yx + 12, yy as int, 0, 16, 2, bl as int, 0, 0, 0); }
        }
        if y > 0 {
            hedge16(yv, yw, yx, yy, 2, mbl, 0, 0, Ghost(cur));
            proof { cur = filter_edge(cur, yx as int, yy as int, 1, 16, 2, mbl as int, 0, 0, 0); }
        }
        if inner {
            hedge16(yv, yw, yx, yy + 4, 2, bl, 0, 0, Ghost(cur));
            proof { cur = filter_edge(cur, yx as int, yy + 4, 1, 16, 2, bl as int, 0, 0, 0); }
            hedge16(yv, yw, yx, yy + 8, 2, bl, 0, 0, Ghost(cur));
            proof { cur = filter_edge(cur, yx as int, yy + 8, 1, 16, 2, bl as int, 0, 0, 0); }
            hedge16(yv, yw, yx, yy + 12, 2, bl, 0, 0, Ghost(cur));
            proof { cur = filter_edge(cur, yx as int, yy + 12, 1, 16, 2, bl as int, 0, 0, 0); }
        }
        return;
    }
    let ghost mut cy_ = pl.y;
    let ghost mut cu = pl.u;
    let ghost mut cv = pl.v;
    if x > 0 {
        vedge16(yv, yw, yx, yy, 0, e + 2, i, h, Ghost(cy_));
        edge_uv(uv, vv, cw, cx, cy, 0, 0, e + 2, i, h, Ghost(cu), Ghost(cv));
        proof {
            cy_ = filter_edge(cy_, yx as int, yy as int, 0, 16, 0, e + 2, i as int, h as int, 0);
            cu = filter_edge(cu, cx as int, cy as int, 0, 8, 0, e + 2, i as int, h as int, 0);
            cv = filter_edge(cv, cx as int, cy as int, 0, 8, 0, e + 2, i as int, h as int, 0);
        }
    }
    if inner {
        vedge3(yv, yw, yx, yy, e, i, h, Ghost(cy_));
        proof {
            cy_ = filter_edge(cy_, yx + 4, yy as int, 0, 16, 1, e as int, i as int, h as int, 0);
            cy_ = filter_edge(cy_, yx + 8, yy as int, 0, 16, 1, e as int, i as int, h as int, 0);
            cy_ = filter_edge(cy_, yx + 12, yy as int, 0, 16, 1, e as int, i as int, h as int, 0);
        }
        edge_uv(uv, vv, cw, cx + 4, cy, 0, 1, e, i, h, Ghost(cu), Ghost(cv));
        proof {
            cu = filter_edge(cu, cx + 4, cy as int, 0, 8, 1, e as int, i as int, h as int, 0);
            cv = filter_edge(cv, cx + 4, cy as int, 0, 8, 1, e as int, i as int, h as int, 0);
        }
    }
    if y > 0 {
        hedge16(yv, yw, yx, yy, 0, e + 2, i, h, Ghost(cy_));
        edge_uv(uv, vv, cw, cx, cy, 1, 0, e + 2, i, h, Ghost(cu), Ghost(cv));
        proof {
            cy_ = filter_edge(cy_, yx as int, yy as int, 1, 16, 0, e + 2, i as int, h as int, 0);
            cu = filter_edge(cu, cx as int, cy as int, 1, 8, 0, e + 2, i as int, h as int, 0);
            cv = filter_edge(cv, cx as int, cy as int, 1, 8, 0, e + 2, i as int, h as int, 0);
        }
    }
    if inner {
        hedge16(yv, yw, yx, yy + 4, 1, e, i, h, Ghost(cy_));
        proof { cy_ = filter_edge(cy_, yx as int, yy + 4, 1, 16, 1, e as int, i as int, h as int, 0); }
        hedge16(yv, yw, yx, yy + 8, 1, e, i, h, Ghost(cy_));
        proof { cy_ = filter_edge(cy_, yx as int, yy + 8, 1, 16, 1, e as int, i as int, h as int, 0); }
        hedge16(yv, yw, yx, yy + 12, 1, e, i, h, Ghost(cy_));
        proof { cy_ = filter_edge(cy_, yx as int, yy + 12, 1, 16, 1, e as int, i as int, h as int, 0); }
        edge_uv(uv, vv, cw, cx, cy + 4, 1, 1, e, i, h, Ghost(cu), Ghost(cv));
    }
}

/// The loop filter over the frame (`loop_filter`).
pub fn loop_filter_x(hd: &HdrX, mbs: &Vec<Vec<MbX>>, nz: &Vec<Vec<bool>>, mbw: usize, mbh: usize,
    yv: &mut Vec<u8>, uv: &mut Vec<u8>, vv: &mut Vec<u8>, Ghost(pl): Ghost<Planes>)
    requires hd.wf(), 1 <= mbw <= 1024, 1 <= mbh <= 1024,
        mbs@.len() == mbh, forall|j: int| 0 <= j < mbh ==> (#[trigger] mbs@[j])@.len() == mbw,
        forall|j: int, x: int| 0 <= j < mbh && 0 <= x < mbw ==> (#[trigger] mbs@[j]@[x]).wf(),
        nz@.len() == mbh, forall|j: int| 0 <= j < mbh ==> (#[trigger] nz@[j])@.len() == mbw,
        holds3(old(yv)@, old(uv)@, old(vv)@, mbw as nat, mbh as nat, pl),
    ensures holds3(final(yv)@, final(uv)@, final(vv)@, mbw as nat, mbh as nat,
        loop_filter(hd.view(), super::modes::rows_view(mbs@), nz@.map_values(|r: Vec<bool>| r@), mbw as int, mbh as int, 0, pl)),
{
    let ghost mv = super::modes::rows_view(mbs@);
    let ghost nv = nz@.map_values(|r: Vec<bool>| r@);
    if hd.filt.level == 0 {
        return;
    }
    let ghost mut cur = pl;
    let mut y: usize = 0;
    while y < mbh
        invariant
            hd.wf(), hd.filt.level != 0, 1 <= mbw <= 1024, 1 <= mbh <= 1024, y <= mbh,
            mbs@.len() == mbh, forall|j: int| 0 <= j < mbh ==> (#[trigger] mbs@[j])@.len() == mbw,
            forall|j: int, x: int| 0 <= j < mbh && 0 <= x < mbw ==> (#[trigger] mbs@[j]@[x]).wf(),
            nz@.len() == mbh, forall|j: int| 0 <= j < mbh ==> (#[trigger] nz@[j])@.len() == mbw,
            mv == super::modes::rows_view(mbs@), nv == nz@.map_values(|r: Vec<bool>| r@),
            holds3(yv@, uv@, vv@, mbw as nat, mbh as nat, cur),
            loop_filter(hd.view(), mv, nv, mbw as int, mbh as int, y as int, cur)
                == loop_filter(hd.view(), mv, nv, mbw as int, mbh as int, 0, pl),
        decreases mbh - y,
    {
        let ghost row0 = cur;
        let mut x: usize = 0;
        while x < mbw
            invariant
                hd.wf(), 1 <= mbw <= 1024, 1 <= mbh <= 1024, y < mbh, x <= mbw,
                mbs@.len() == mbh, forall|j: int| 0 <= j < mbh ==> (#[trigger] mbs@[j])@.len() == mbw,
                forall|j: int, x: int| 0 <= j < mbh && 0 <= x < mbw ==> (#[trigger] mbs@[j]@[x]).wf(),
                nz@.len() == mbh, forall|j: int| 0 <= j < mbh ==> (#[trigger] nz@[j])@.len() == mbw,
                mv == super::modes::rows_view(mbs@), nv == nz@.map_values(|r: Vec<bool>| r@),
                holds3(yv@, uv@, vv@, mbw as nat, mbh as nat, cur),
                filter_row(hd.view(), mv, nv, mbw as int, x as int, y as int, cur)
                    == filter_row(hd.view(), mv, nv, mbw as int, 0, y as int, row0),
            decreases mbw - x,
        {
            let mb = &mbs[y][x];
            let n = nz[y][x];
            proof {
                assert(mv[y as int][x as int] == mb.view());
                assert(nv[y as int][x as int] == n);
            }
            filter_mb_x(hd, mb, n, x, y, mbw, mbh, yv, uv, vv, Ghost(cur));
            proof { cur = filter_mb(hd.view(), mb.view(), n, x as int, y as int, cur); }
            x = x + 1;
        }
        y = y + 1;
    }
}

} // verus!
