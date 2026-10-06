//! Prefix code groups and the entropy-coded pixels (RFC 9649 3.6, 3.7.2):
//! literals, LZ77 copies and the color cache, proved to compute
//! `decode_pixels` on `lbits(input)`.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
use vbits::lsb::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::getbits;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbrotli::spec::dsym;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::huff::win_k;
use crate::code::*;
use crate::spec::*;

verus! {

// ------------------------------------------------------------- groups

/// The code lengths of a list of codes.
pub open spec fn codes_view(v: Seq<Code>) -> Seq<Seq<u8>> {
    Seq::new(v.len(), |k: int| v[k].lens@)
}

/// The code lengths of a list of groups.
pub open spec fn groups_view(v: Seq<Vec<Code>>) -> Seq<Seq<Seq<u8>>> {
    Seq::new(v.len(), |k: int| codes_view(v[k]@))
}

/// Five codes, of the group's alphabets, ready to decode with.
pub open spec fn group_wf(g: Seq<Code>, cache_bits: nat) -> bool {
    &&& g.len() == 5
    &&& forall|j: int| 0 <= j < 5 ==> #[trigger] code_wf(&g[j]) && g[j].lens@.len() == asize(j as nat, cache_bits)
}

pub fn asize_x(j: u64, cache_bits: u64) -> (r: u64)
    requires j < 5, cache_bits <= 11,
    ensures r as nat == asize(j as nat, cache_bits as nat), r <= 2328,
{
    if j == 0 {
        if cache_bits > 0 {
            proof { lemma_shl1(cache_bits); vbits::prim_read::lemma_p2_mono(cache_bits as nat, 11); lemma_p2_11(); }
            280 + (1u64 << cache_bits)
        } else {
            280
        }
    } else if j < 4 {
        256
    } else {
        40
    }
}

pub proof fn lemma_p2_11()
    ensures p2(11) == 2048, p2(32) == 0x1_0000_0000,
{
    reveal_with_fuel(p2, 33);
}

/// A prefix code group: `read_codes`.
pub fn read_group_x(buf: &[u8], pos: usize, cache_bits: u64) -> (r: Option<(Vec<Code>, usize, bool)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), cache_bits <= 11,
    ensures
        match r {
            Some((g, q, st)) => read_codes(lbits(buf@), pos as int, cache_bits as nat, Seq::empty(), true)
                    == Some((codes_view(g@), q as int, st))
                && group_wf(g@, cache_bits as nat) && q <= 8 * buf.len(),
            None => read_codes(lbits(buf@), pos as int, cache_bits as nat, Seq::empty(), true) is None,
        },
{
    let ghost b = lbits(buf@);
    let ghost target = read_codes(b, pos as int, cache_bits as nat, Seq::empty(), true);
    let mut g: Vec<Code> = Vec::new();
    let mut p = pos;
    let mut st = true;
    proof { assert(codes_view(g@) =~= Seq::<Seq<u8>>::empty()); }
    while g.len() < 5
        invariant
            buf_ok(buf@), p <= 8 * buf.len(), b == lbits(buf@), cache_bits <= 11, g@.len() <= 5,
            read_codes(b, p as int, cache_bits as nat, codes_view(g@), st) == target,
            target == read_codes(lbits(buf@), pos as int, cache_bits as nat, Seq::empty(), true),
            forall|j: int| 0 <= j < g@.len() ==> #[trigger] code_wf(&g@[j]) && g@[j].lens@.len() == asize(j as nat, cache_bits as nat),
        decreases 5 - g@.len(),
    {
        let a = asize_x(g.len() as u64, cache_bits);
        proof { assert(codes_view(g@).len() == g@.len()); }
        let (c, q, st2) = match read_code_x(buf, p, a) { None => return None, Some(x) => x };
        let ghost gv = g@;
        g.push(c);
        proof { assert(codes_view(g@) =~= codes_view(gv).push(c.lens@)); }
        p = q;
        st = st && st2;
    }
    Some((g, p, st))
}

/// `n` prefix code groups: `read_groups`.
pub fn read_groups_x(buf: &[u8], pos: usize, cache_bits: u64, n: usize) -> (r: Option<(Vec<Vec<Code>>, usize, bool)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), cache_bits <= 11,
    ensures
        match r {
            Some((gs, q, st)) => read_groups(lbits(buf@), pos as int, cache_bits as nat, n as nat, Seq::empty(), true)
                    == Some((groups_view(gs@), q as int, st))
                && gs@.len() == n && q <= 8 * buf.len()
                && forall|k: int| 0 <= k < n ==> #[trigger] group_wf(gs@[k]@, cache_bits as nat),
            None => read_groups(lbits(buf@), pos as int, cache_bits as nat, n as nat, Seq::empty(), true) is None,
        },
{
    let ghost b = lbits(buf@);
    let ghost target = read_groups(b, pos as int, cache_bits as nat, n as nat, Seq::empty(), true);
    let mut gs: Vec<Vec<Code>> = Vec::new();
    let mut p = pos;
    let mut st = true;
    proof { assert(groups_view(gs@) =~= Seq::<Seq<Seq<u8>>>::empty()); }
    while gs.len() < n
        invariant
            buf_ok(buf@), p <= 8 * buf.len(), b == lbits(buf@), cache_bits <= 11, gs@.len() <= n,
            read_groups(b, p as int, cache_bits as nat, n as nat, groups_view(gs@), st) == target,
            target == read_groups(lbits(buf@), pos as int, cache_bits as nat, n as nat, Seq::empty(), true),
            forall|k: int| 0 <= k < gs@.len() ==> #[trigger] group_wf(gs@[k]@, cache_bits as nat),
        decreases n - gs@.len(),
    {
        proof { assert(groups_view(gs@).len() == gs@.len()); }
        let (g, q, st2) = match read_group_x(buf, p, cache_bits) { None => return None, Some(x) => x };
        let ghost gv = gs@;
        gs.push(g);
        proof { assert(groups_view(gs@) =~= groups_view(gv).push(codes_view(g@))); }
        p = q;
        st = st && st2;
    }
    Some((gs, p, st))
}

// ---------------------------------------------------------- LZ77 values

/// `prefix_value` for a symbol below 40.
pub fn prefix_value_x(buf: &[u8], pos: usize, s: u64) -> (r: Option<(u64, usize)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), s < 40,
    ensures
        match r {
            Some((v, q)) => prefix_value(lbits(buf@), pos as int, s as nat) == Some((v as nat, q as int))
                && q <= 8 * buf.len() && 1 <= v <= 0x10_0000,
            None => prefix_value(lbits(buf@), pos as int, s as nat) is None,
        },
{
    if s < 4 {
        return Some((s + 1, pos));
    }
    let s2: u64 = s - 2;
    let eb: u64 = s2 >> 1u64;
    let odd: u64 = s & 1u64;
    assert(eb == s2 / 2) by (bit_vector) requires eb == s2 >> 1u64;
    assert(odd == s % 2) by (bit_vector) requires odd == s & 1u64;
    let base: u64 = 2 + odd;
    let off: u64 = base << eb;
    proof {
        assert(eb <= 18);
        lemma_shl1(eb);
        vbits::prim_read::lemma_p2_mono(eb as nat, 18);
        lemma_p2_18();
        let one: u64 = 1;
        assert(off == base * (one << eb)) by (bit_vector)
            requires off == base << eb, eb <= 18, base <= 3, one == 1;
    }
    let e = match getbits_x(buf, pos, eb) { None => return None, Some(e) => e };
    proof {
        assert((2 + s % 2) * p2(eb as nat) + p2(eb as nat) <= 4 * p2(18)) by (nonlinear_arith)
            requires p2(eb as nat) <= p2(18), s % 2 <= 1;
    }
    Some((off + e + 1, pos + eb as usize))
}

pub proof fn lemma_p2_18()
    ensures p2(18) == 0x4_0000,
{
    reveal_with_fuel(p2, 19);
}

pub const DIST_X: [i8; 120] = [
    0, 1, 1, -1, 0, 2, 1, -1, 2, -2, 2, -2, 0, 3, 1, -1, 3, -3, 2, -2, 3, -3, 0, 4,
    1, -1, 4, -4, 3, -3, 2, -2, 4, -4, 0, 3, -3, 4, -4, 5, 1, -1, 5, -5, 2, -2, 5, -5,
    4, -4, 3, -3, 5, -5, 0, 6, 1, -1, 6, -6, 2, -2, 6, -6, 4, -4, 5, -5, 3, -3, 6, -6,
    0, 7, 1, -1, 5, -5, 7, -7, 4, -4, 6, -6, 2, -2, 7, -7, 3, -3, 7, -7, 5, -5, 6, -6,
    8, 4, -4, 7, -7, 8, 8, 6, -6, 8, 5, -5, 7, -7, 8, 6, -6, 7, -7, 8, 7, -7, 8, 8,
];

pub const DIST_Y: [u8; 120] = [
    1, 0, 1, 1, 2, 0, 2, 2, 1, 1, 2, 2, 3, 0, 3, 3, 1, 1, 3, 3, 2, 2, 4, 0,
    4, 4, 1, 1, 3, 3, 4, 4, 2, 2, 5, 4, 4, 3, 3, 0, 5, 5, 1, 1, 5, 5, 2, 2,
    4, 4, 5, 5, 3, 3, 6, 0, 6, 6, 1, 1, 6, 6, 2, 2, 5, 5, 4, 4, 6, 6, 3, 3,
    7, 0, 7, 7, 5, 5, 1, 1, 6, 6, 4, 4, 7, 7, 2, 2, 7, 7, 3, 3, 6, 6, 5, 5,
    0, 7, 7, 4, 4, 1, 2, 6, 6, 3, 7, 7, 5, 5, 4, 7, 7, 6, 6, 5, 7, 7, 6, 7,
];

proof fn lemma_dist_tables()
    ensures forall|i: int| 0 <= i < 120 ==>
        #[trigger] DIST_X@[i] as int == dist_map()[i].0 && DIST_Y@[i] as int == dist_map()[i].1,
{
    assert(forall|i: int| 0 <= i < 120 ==>
        #[trigger] DIST_X@[i] as int == dist_map()[i].0 && DIST_Y@[i] as int == dist_map()[i].1) by (compute);
}

/// `plane_dist` in an image at most 16384 wide.
pub fn plane_dist_x(dcode: u64, w: u64) -> (r: u64)
    requires 1 <= dcode <= 0x10_0000, 1 <= w <= 16384,
    ensures r as nat == plane_dist(dcode as nat, w as nat), 1 <= r <= 0x10_0000,
{
    if dcode > 120 {
        return dcode - 120;
    }
    proof { lemma_dist_tables(); }
    let xi = DIST_X[(dcode - 1) as usize] as i64;
    let yi = DIST_Y[(dcode - 1) as usize] as i64;
    proof {
        assert(-8 <= xi <= 8 && 0 <= yi <= 7) by {
            assert(forall|i: int| 0 <= i < 120 ==> -8 <= #[trigger] DIST_X@[i] <= 8 && DIST_Y@[i] <= 7) by (compute);
        }
    }
    proof {
        assert(yi * (w as i64) <= 7 * 16384 && yi * (w as i64) >= 0) by (nonlinear_arith)
            requires 0 <= yi <= 7, 1 <= w <= 16384;
    }
    let d = xi + yi * (w as i64);
    if d < 1 { 1 } else { d as u64 }
}

// ------------------------------------------------------------ the cache

/// `cache_key`, computed in 64 bits.
pub fn cache_key_x(c: u32, cache_bits: u64) -> (r: usize)
    requires 1 <= cache_bits <= 11,
    ensures r as int == cache_key(c, cache_bits as nat), (r as nat) < p2(cache_bits as nat),
{
    let x: u64 = (c as u64) * 0x1e35a7bd;
    let y: u64 = x & 0xffff_ffff;
    let k: u64 = y >> (32 - cache_bits);
    proof {
        lemma_p2_11();
        assert(y == x % 0x1_0000_0000) by (bit_vector) requires y == x & 0xffff_ffff;
        vstd::bits::lemma_u64_shr_is_div(y, (32 - cache_bits) as u64);
        vbits::prim_read::lemma_p2_eq_pow2((32 - cache_bits) as nat);
        vbits::bitspec::lemma_p2_adds((32 - cache_bits) as nat, cache_bits as nat);
        vbits::bitspec::lemma_p2_pos((32 - cache_bits) as nat);
        let a = p2((32 - cache_bits) as nat);
        let bb = p2(cache_bits as nat);
        assert(y < a * bb);
        assert((y as int) / (a as int) < bb) by (nonlinear_arith) requires (y as int) < a * bb, a > 0;
    }
    k as usize
}

// ------------------------------------------------------------ the pixels

/// Which group each pixel uses, in exec form.
pub enum MetaX {
    One,
    Tiles { bits: u64, ew: usize, img: Vec<u32> },
}

pub open spec fn meta_view(m: &MetaX) -> Meta {
    match m {
        MetaX::One => Meta::One,
        MetaX::Tiles { bits, ew, img } => Meta::Tiles { bits: *bits as nat, ew: *ew as nat, img: img@ },
    }
}

/// Every pixel of a `w` x `h` image has a tile, and its group is one of `ng`.
pub open spec fn meta_wf(m: &MetaX, w: nat, h: nat, ng: nat) -> bool {
    match m {
        MetaX::One => ng >= 1,
        MetaX::Tiles { bits, ew, img } => {
            &&& 2 <= *bits <= 9
            &&& *ew as nat == div_round_up(w, p2(*bits as nat))
            &&& img@.len() == *ew as nat * div_round_up(h, p2(*bits as nat))
            &&& forall|k: int| 0 <= k < img@.len() ==> #[trigger] meta_code(img@[k]) < ng
        },
    }
}

/// A tile index in range: for x < w and y < h, (y >> bits) * ew + (x >> bits)
/// is below ew * eh.
pub proof fn lemma_tile_in(w: nat, h: nat, bits: nat, x: nat, y: nat)
    requires x < w, y < h, 1 <= w, 1 <= h,
    ensures
        ({
            let t = p2(bits);
            let ew = div_round_up(w, t);
            let eh = div_round_up(h, t);
            (y / t) * ew + x / t < ew * eh && x / t < ew && y / t < eh
        }),
{
    let t = p2(bits);
    vbits::bitspec::lemma_p2_pos(bits);
    let ew = div_round_up(w, t);
    let eh = div_round_up(h, t);
    assert(x / t < ew) by (nonlinear_arith) requires x < w, t > 0, ew == ((w + t - 1) / (t as int)) as nat;
    assert(y / t < eh) by (nonlinear_arith) requires y < h, t > 0, eh == ((h + t - 1) / (t as int)) as nat;
    let a = (y / t) as int;
    let c = (x / t) as int;
    assert(a * ew <= (eh - 1) * ew) by (nonlinear_arith) requires a <= eh - 1, ew >= 0;
    assert((eh - 1) * ew + ew == eh * ew) by (nonlinear_arith);
    assert(eh * ew == ew * eh) by (nonlinear_arith);
}

/// Where row `y`'s tiles start in the entropy image (0 for one group).
pub open spec fn meta_row(m: &MetaX, y: nat) -> int {
    match m {
        MetaX::One => 0,
        MetaX::Tiles { bits, ew, img } => ((y / p2(*bits as nat)) * *ew as nat) as int,
    }
}

/// An entropy image is at most 16384 tiles each way.
proof fn lemma_meta_dims(w: nat, h: nat, bits: nat, ew: nat)
    requires 1 <= w <= 16384, h <= 16384, ew == div_round_up(w, p2(bits)),
    ensures ew <= 16384, div_round_up(h, p2(bits)) <= 16384,
{
    vbits::bitspec::lemma_p2_pos(bits);
    let t = p2(bits);
    assert((w + t - 1) / (t as int) <= w) by (nonlinear_arith) requires w >= 1, t >= 1;
    assert((h + t - 1) / (t as int) <= 16384) by (nonlinear_arith) requires h <= 16384, t >= 1;
}

/// `meta_row`.
fn meta_row_x(m: &MetaX, y: usize, Ghost(w): Ghost<nat>, Ghost(h): Ghost<nat>, Ghost(ng): Ghost<nat>) -> (r: usize)
    requires meta_wf(m, w, h, ng), y < h, 1 <= w <= 16384, h <= 16384,
    ensures r as int == meta_row(m, y as nat),
{
    match m {
        MetaX::One => 0,
        MetaX::Tiles { bits, ew, img } => {
            proof {
                lemma_tile_in(w, h, *bits as nat, 0, y as nat);
                vstd::bits::lemma_u64_shr_is_div(y as u64, *bits);
                vbits::prim_read::lemma_p2_eq_pow2(*bits as nat);
                lemma_meta_dims(w, h, *bits as nat, *ew as nat);
                let t = p2(*bits as nat);
                let ty = y as nat / t;
                assert(ty * *ew <= 16384 * 16384) by (nonlinear_arith) requires ty <= 16384, *ew <= 16384;
            }
            let ty = (y as u64 >> *bits) as usize;
            ty * *ew
        },
    }
}

/// `group_at` with the row's start in the entropy image given.
#[inline(always)]
fn group_in_row(m: &MetaX, trow: usize, x: usize, y: usize, Ghost(w): Ghost<nat>, Ghost(h): Ghost<nat>, Ghost(ng): Ghost<nat>)
    -> (r: usize)
    requires meta_wf(m, w, h, ng), x < w, y < h, w <= 16384, h <= 16384, trow as int == meta_row(m, y as nat),
    ensures r as int == group_at(meta_view(m), x as nat, y as nat), r < ng,
{
    match m {
        MetaX::One => 0,
        MetaX::Tiles { bits, ew, img } => {
            proof {
                lemma_tile_in(w, h, *bits as nat, x as nat, y as nat);
                vstd::bits::lemma_u64_shr_is_div(x as u64, *bits);
                vbits::prim_read::lemma_p2_eq_pow2(*bits as nat);
                lemma_meta_dims(w, h, *bits as nat, *ew as nat);
                let t = p2(*bits as nat);
                assert(img@.len() <= 16384 * 16384) by (nonlinear_arith)
                    requires img@.len() == *ew as nat * div_round_up(h, t), *ew <= 16384, div_round_up(h, t) <= 16384;
            }
            let tx = (x as u64 >> *bits) as usize;
            let c = vsimd::mem::get(img.as_slice(), trow + tx);
            proof {
                assert(meta_code(img@[(trow + tx) as int]) < ng);
            }
            ((c >> 8u32) & 0xffffu32) as usize
        },
    }
}

/// The pixels so far, the first `i` of `px`, and the color cache.
pub open spec fn stv(px: Seq<u32>, i: int, cache: Seq<u32>) -> St { St { px: px.take(i), cache } }

pub open spec fn cache_size(cache_bits: nat) -> nat { if cache_bits > 0 { p2(cache_bits) } else { 0 } }

/// `put`, into the preallocated pixels.
#[inline(always)]
pub fn put_px(px: &mut Vec<u32>, i: usize, cache: &mut Vec<u32>, c: u32, cache_bits: u64)
    requires i < old(px)@.len(), cache_bits <= 11, old(cache)@.len() == cache_size(cache_bits as nat),
    ensures
        stv(final(px)@, i + 1, final(cache)@) == put(stv(old(px)@, i as int, old(cache)@), c, cache_bits as nat),
        final(px)@.len() == old(px)@.len(), final(cache)@.len() == old(cache)@.len(),
{
    let ghost p0 = px@;
    vsimd::mem::vset(px, i, c);
    if cache_bits > 0 {
        let k = cache_key_x(c, cache_bits);
        vsimd::mem::vset(cache, k, c);
    }
    proof { assert(px@.take(i + 1) =~= p0.take(i as int).push(c)); }
}

/// `copy_px`: `n` pixels from `d` back, one at a time.
pub fn copy_px_x(px: &mut Vec<u32>, i: usize, cache: &mut Vec<u32>, d: usize, n: usize, cache_bits: u64)
    requires
        1 <= d <= i, i + n <= old(px)@.len(), cache_bits <= 11,
        old(cache)@.len() == cache_size(cache_bits as nat),
    ensures
        stv(final(px)@, i + n, final(cache)@) == copy_px(stv(old(px)@, i as int, old(cache)@), d as nat, n as nat, cache_bits as nat),
        final(px)@.len() == old(px)@.len(), final(cache)@.len() == old(cache)@.len(),
{
    let ghost target = copy_px(stv(old(px)@, i as int, old(cache)@), d as nat, n as nat, cache_bits as nat);
    let plen = px.len();
    let end = i + n;
    let mut j = i;
    while j < end
        invariant
            1 <= d <= j, i <= j <= end, end == i + n, end <= px@.len(), px@.len() == old(px)@.len(),
            cache_bits <= 11, cache@.len() == cache_size(cache_bits as nat),
            copy_px(stv(px@, j as int, cache@), d as nat, (end - j) as nat, cache_bits as nat) == target,
        decreases end - j,
    {
        let c = vsimd::mem::get(px.as_slice(), j - d);
        proof { assert(stv(px@, j as int, cache@).px[stv(px@, j as int, cache@).px.len() - d] == c); }
        put_px(px, j, cache, c, cache_bits);
        j = j + 1;
    }
}

/// The groups `gs` for an image `w` wide of `total` pixels: each good.
pub open spec fn gs_wf(gs: Seq<Vec<Code>>, cache_bits: nat) -> bool {
    forall|k: int| 0 <= k < gs.len() ==> #[trigger] group_wf(gs[k]@, cache_bits)
}

/// The literal branch of `pix_step`, after the green symbol `sg` (< 256).
pub open spec fn lit_branch(b: Seq<bool>, q: int, g: Seq<Seq<u8>>, st: St, cache_bits: nat, sg: nat) -> Option<(St, int)> {
    match dsym(g[1], b, q) {
        None => None,
        Some((r, q1)) => match dsym(g[2], b, q1) {
            None => None,
            Some((bl, q2)) => match dsym(g[3], b, q2) {
                None => None,
                Some((a, q3)) => Some((put(st, argb(a as int, r as int, sg as int, bl as int), cache_bits), q3)),
            },
        },
    }
}

/// The copy branch, after the green symbol `sg` (256..280).
pub open spec fn copy_branch(b: Seq<bool>, q: int, g: Seq<Seq<u8>>, w: nat, total: nat, st: St, cache_bits: nat, sg: nat)
    -> Option<(St, int)> {
    let i = st.px.len();
    match prefix_value(b, q, (sg - 256) as nat) {
        None => None,
        Some((len, q1)) => match dsym(g[4], b, q1) {
            None => None,
            Some((ds, q2)) => match prefix_value(b, q2, ds) {
                None => None,
                Some((dcode, q3)) => {
                    let d = plane_dist(dcode, w);
                    if d > i || len > total - i { None } else { Some((copy_px(st, d, len, cache_bits), q3)) }
                },
            },
        },
    }
}

/// The literal branch: red, blue and alpha from the window, the pixel put.
#[inline(always)]
fn lit_w(buf: &[u8], Ghost(b): Ghost<Seq<bool>>, q: usize, win: u64, k: u64, g: &Vec<Code>, cache_bits: u64, sg: u16,
         px: &mut Vec<u32>, i: usize, cache: &mut Vec<u32>) -> (r: Option<(usize, u64, u64)>)
    requires
        buf_ok(buf@), b == lbits(buf@), q <= 8 * buf.len(), k <= 56, win_k(b, q as int, win, k as nat),
        cache_bits <= 11, group_wf(g@, cache_bits as nat), sg < 256,
        i < old(px)@.len(), old(cache)@.len() == cache_size(cache_bits as nat),
    ensures
        final(px)@.len() == old(px)@.len(), final(cache)@.len() == old(cache)@.len(),
        match r {
            Some((q3, w3, k3)) => lit_branch(b, q as int, codes_view(g@), stv(old(px)@, i as int, old(cache)@),
                                             cache_bits as nat, sg as nat)
                    == Some((stv(final(px)@, i + 1, final(cache)@), q3 as int))
                && q3 <= 8 * buf.len() && k3 <= 56 && win_k(b, q3 as int, w3, k3 as nat),
            None => lit_branch(b, q as int, codes_view(g@), stv(old(px)@, i as int, old(cache)@),
                               cache_bits as nat, sg as nat) is None,
        },
{
    proof {
        assert(code_wf(&g@[1]) && code_wf(&g@[2]) && code_wf(&g@[3]));
        assert(g@[1].lens@.len() == 256 && g@[2].lens@.len() == 256 && g@[3].lens@.len() == 256);
        assert(codes_view(g@)[1] == g@[1].lens@ && codes_view(g@)[2] == g@[2].lens@ && codes_view(g@)[3] == g@[3].lens@);
    }
    let (r, q1, w1, k1) = match dsym_w(vsimd::mem::get_ref(g.as_slice(), 1), buf, Ghost(b), q, win, k) { None => return None, Some(x) => x };
    let (bl, q2, w2, k2) = match dsym_w(vsimd::mem::get_ref(g.as_slice(), 2), buf, Ghost(b), q1, w1, k1) { None => return None, Some(x) => x };
    let (a, q3, w3, k3) = match dsym_w(vsimd::mem::get_ref(g.as_slice(), 3), buf, Ghost(b), q2, w2, k2) { None => return None, Some(x) => x };
    let c = pixel_x(a as u32, r as u32, sg as u32, bl as u32);
    put_px(px, i, cache, c, cache_bits);
    Some((q3, w3, k3))
}

/// `argb` of channel values below 256.
#[inline(always)]
pub fn pixel_x(a: u32, r: u32, g: u32, b: u32) -> (c: u32)
    requires a < 256, r < 256, g < 256, b < 256,
    ensures c == argb(a as int, r as int, g as int, b as int),
{
    proof {
        assert(byte(a as int) == a && byte(r as int) == r && byte(g as int) == g && byte(b as int) == b);
    }
    (a << 24u32) | (r << 16u32) | (g << 8u32) | b
}

/// The copy branch: the length, the distance, and the copy. The position
/// after it and the length.
#[inline(always)]
fn copy_w(buf: &[u8], q: usize, g: &Vec<Code>, w: usize, total: usize, cache_bits: u64, sg: u16,
          px: &mut Vec<u32>, i: usize, cache: &mut Vec<u32>) -> (r: Option<(usize, usize)>)
    requires
        buf_ok(buf@), q <= 8 * buf.len(), cache_bits <= 11, group_wf(g@, cache_bits as nat), 256 <= sg < 280,
        1 <= w <= 16384, total <= 0x1000_0000, old(px)@.len() == total, i < total,
        old(cache)@.len() == cache_size(cache_bits as nat),
    ensures
        final(px)@.len() == old(px)@.len(), final(cache)@.len() == old(cache)@.len(),
        match r {
            Some((q3, n)) => copy_branch(lbits(buf@), q as int, codes_view(g@), w as nat, total as nat,
                                         stv(old(px)@, i as int, old(cache)@), cache_bits as nat, sg as nat)
                    == Some((stv(final(px)@, i + n, final(cache)@), q3 as int))
                && q3 <= 8 * buf.len() && 1 <= n && i + n <= total,
            None => copy_branch(lbits(buf@), q as int, codes_view(g@), w as nat, total as nat,
                                stv(old(px)@, i as int, old(cache)@), cache_bits as nat, sg as nat) is None,
        },
{
    proof {
        assert(code_wf(&g@[4]) && g@[4].lens@.len() == asize(4, cache_bits as nat));
        assert(asize(4, cache_bits as nat) == 40);
        assert(codes_view(g@)[4] == g@[4].lens@);
        assert(stv(px@, i as int, cache@).px.len() == i);
    }
    let (len, q1) = match prefix_value_x(buf, q, (sg - 256) as u64) { None => return None, Some(x) => x };
    let (ds, q2) = match dsym_x(&g[4], buf, q1) { None => return None, Some(x) => x };
    let (dcode, q3) = match prefix_value_x(buf, q2, ds as u64) { None => return None, Some(x) => x };
    let d = plane_dist_x(dcode, w as u64);
    if d as usize > i || len as usize > total - i {
        return None;
    }
    copy_px_x(px, i, cache, d as usize, len as usize, cache_bits);
    Some((q3, len as usize))
}

/// What a group's literals need: below 2^32, the red, blue and alpha codes
/// each have one symbol (read with no bits), and this is their pixel with
/// green 0 (libwebp's `is_trivial_literal`); else nothing.
pub open spec fn info_ok(r: u64, g: Seq<Code>) -> bool {
    r < 0x1_0000_0000 ==> g[1].single && g[2].single && g[3].single
        && r as u32 == argb(g[3].sym as int, g[1].sym as int, 0, g[2].sym as int)
}

fn group_info(g: &Vec<Code>, Ghost(cache_bits): Ghost<nat>) -> (r: u64)
    requires group_wf(g@, cache_bits),
    ensures info_ok(r, g@),
{
    if g[1].single && g[2].single && g[3].single {
        proof {
            assert(code_wf(&g@[1]) && code_wf(&g@[2]) && code_wf(&g@[3]));
            assert(g@[1].lens@.len() == 256 && g@[2].lens@.len() == 256 && g@[3].lens@.len() == 256);
        }
        pixel_x(g[3].sym as u32, g[1].sym as u32, 0, g[2].sym as u32) as u64
    } else {
        0xffff_ffff_ffff_ffffu64
    }
}

/// One step of `pix_step`, with the group `g` of pixel `i`: the position,
/// the window after it, and the number of pixels it added.
#[inline(always)]
fn pix_step_w(buf: &[u8], Ghost(b): Ghost<Seq<bool>>, p: usize, win: u64, k: u64, w: usize, total: usize,
              cache_bits: u64, g: &Vec<Code>, info: u64, Ghost(gsv): Ghost<Seq<Seq<Seq<u8>>>>, Ghost(mv): Ghost<Meta>,
              px: &mut Vec<u32>, i: usize, cache: &mut Vec<u32>) -> (r: Option<(usize, u64, u64, usize)>)
    requires
        info_ok(info, g@),
        buf_ok(buf@), b == lbits(buf@), p <= 8 * buf.len(), k <= 56, win_k(b, p as int, win, k as nat),
        cache_bits <= 11, group_wf(g@, cache_bits as nat), 1 <= w <= 16384, total <= 0x1000_0000,
        old(px)@.len() == total, i < total, old(cache)@.len() == cache_size(cache_bits as nat),
        gsv[group_at(mv, (i as int % w as int) as nat, (i as int / w as int) as nat)] == codes_view(g@),
    ensures
        final(px)@.len() == old(px)@.len(), final(cache)@.len() == old(cache)@.len(),
        match r {
            Some((q, w2, k2, n)) => pix_step(b, p as int, w as nat, total as nat, cache_bits as nat, gsv, mv,
                                             stv(old(px)@, i as int, old(cache)@))
                    == Some((stv(final(px)@, i + n, final(cache)@), q as int))
                && q <= 8 * buf.len() && k2 <= 56 && win_k(b, q as int, w2, k2 as nat) && 1 <= n && i + n <= total,
            None => pix_step(b, p as int, w as nat, total as nat, cache_bits as nat, gsv, mv,
                             stv(old(px)@, i as int, old(cache)@)) is None,
        },
{
    let ghost st = stv(px@, i as int, cache@);
    proof {
        assert(st.px.len() == i);
        assert(code_wf(&g@[0]) && codes_view(g@)[0] == g@[0].lens@);
    }
    let (sg, q, w1, k1) = match dsym_w(vsimd::mem::get_ref(g.as_slice(), 0), buf, Ghost(b), p, win, k) { None => return None, Some(v) => v };
    if sg < 256 {
        if info < 0x1_0000_0000 {
            // red, blue and alpha have one symbol each: no bits
            let c = (info as u32) | ((sg as u32) << 8u32);
            proof {
                let (a, r, bl) = (g@[3].sym, g@[1].sym, g@[2].sym);
                assert(code_wf(&g@[1]) && code_wf(&g@[2]) && code_wf(&g@[3]));
                assert(g@[1].lens@.len() == 256 && g@[2].lens@.len() == 256 && g@[3].lens@.len() == 256);
                assert(codes_view(g@)[1] == g@[1].lens@ && codes_view(g@)[2] == g@[2].lens@ && codes_view(g@)[3] == g@[3].lens@);
                assert(byte(a as int) == a as u32 && byte(r as int) == r as u32 && byte(bl as int) == bl as u32
                    && byte(sg as int) == sg as u32 && byte(0) == 0u32);
                let a32 = a as u32;
                let r32 = r as u32;
                let b32 = bl as u32;
                let g32 = sg as u32;
                assert(c == (a32 << 24u32) | (r32 << 16u32) | (g32 << 8u32) | b32) by (bit_vector)
                    requires c == ((a32 << 24u32) | (r32 << 16u32) | (0u32 << 8u32) | b32) | (g32 << 8u32), g32 < 256;
            }
            put_px(px, i, cache, c, cache_bits);
            return Some((q, w1, k1, 1));
        }
        match lit_w(buf, Ghost(b), q, w1, k1, g, cache_bits, sg, px, i, cache) {
            None => None,
            Some((q3, w3, k3)) => Some((q3, w3, k3, 1)),
        }
    } else if sg < 280 {
        match copy_w(buf, q, g, w, total, cache_bits, sg, px, i, cache) {
            None => None,
            Some((q3, n)) => Some((q3, 0, 0, n)),
        }
    } else {
        let kk = (sg - 280) as usize;
        if kk >= cache.len() {
            return None;
        }
        let c = cache[kk];
        put_px(px, i, cache, c, cache_bits);
        Some((q, w1, k1, 1))
    }
}

/// `decode_pixels`, opaque in the pixel loop.
#[verifier::opaque]
pub open spec fn dp(b: Seq<bool>, p: int, w: nat, total: nat, cache_bits: nat, gs: Seq<Seq<Seq<u8>>>, m: Meta, st: St)
    -> Option<(Seq<u32>, int)> {
    decode_pixels(b, p, w, total, cache_bits, gs, m, st)
}

/// A step of the pixel loop.
proof fn lemma_dp_step(b: Seq<bool>, p: int, w: nat, total: nat, cache_bits: nat, gs: Seq<Seq<Seq<u8>>>, m: Meta,
                       st: St, st2: St, q: int)
    requires st.px.len() < total, pix_step(b, p, w, total, cache_bits, gs, m, st) == Some((st2, q)),
        st.px.len() < st2.px.len() <= total,
    ensures dp(b, p, w, total, cache_bits, gs, m, st) == dp(b, q, w, total, cache_bits, gs, m, st2),
{
    reveal(dp);
}

proof fn lemma_dp_def(b: Seq<bool>, p: int, w: nat, total: nat, cache_bits: nat, gs: Seq<Seq<Seq<u8>>>, m: Meta, st: St)
    ensures dp(b, p, w, total, cache_bits, gs, m, st) == decode_pixels(b, p, w, total, cache_bits, gs, m, st),
{
    reveal(dp);
}

proof fn lemma_dp_none(b: Seq<bool>, p: int, w: nat, total: nat, cache_bits: nat, gs: Seq<Seq<Seq<u8>>>, m: Meta, st: St)
    requires st.px.len() < total, pix_step(b, p, w, total, cache_bits, gs, m, st) is None,
    ensures dp(b, p, w, total, cache_bits, gs, m, st) is None,
{
    reveal(dp);
}

proof fn lemma_dp_end(b: Seq<bool>, p: int, w: nat, total: nat, cache_bits: nat, gs: Seq<Seq<Seq<u8>>>, m: Meta, st: St)
    requires st.px.len() >= total,
    ensures dp(b, p, w, total, cache_bits, gs, m, st) == Some((st.px, p)),
{
    reveal(dp);
}

/// The pixels until there are `w * h`: `decode_pixels` from the empty state.
/// The pixels go into a buffer of `w * h`, the column and row are counted
/// (no division), and the bits come from a 64-bit window.
pub fn decode_pixels_x(buf: &[u8], pos: usize, w: usize, h: usize, cache_bits: u64, gs: &Vec<Vec<Code>>, m: &MetaX)
    -> (r: Option<(Vec<u32>, usize)>)
    requires
        buf_ok(buf@), pos <= 8 * buf.len(), 1 <= w <= 16384, 1 <= h <= 16384, cache_bits <= 11,
        gs_wf(gs@, cache_bits as nat), meta_wf(m, w as nat, h as nat, gs@.len()),
    ensures
        match r {
            Some((px, q)) => decode_pixels(lbits(buf@), pos as int, w as nat, (w * h) as nat, cache_bits as nat,
                                           groups_view(gs@), meta_view(m), st0(cache_bits as nat)) == Some((px@, q as int))
                && q <= 8 * buf.len() && px@.len() == w * h,
            None => decode_pixels(lbits(buf@), pos as int, w as nat, (w * h) as nat, cache_bits as nat,
                                  groups_view(gs@), meta_view(m), st0(cache_bits as nat)) is None,
        },
{
    let ghost b = lbits(buf@);
    let ghost gsv = groups_view(gs@);
    let ghost mv = meta_view(m);
    let ghost target = decode_pixels(b, pos as int, w as nat, (w * h) as nat, cache_bits as nat, gsv, mv, st0(cache_bits as nat));
    proof { lemma_dp_def(b, pos as int, w as nat, (w * h) as nat, cache_bits as nat, gsv, mv, st0(cache_bits as nat)); }
    proof { assert(w * h <= 0x1000_0000) by (nonlinear_arith) requires w <= 16384, h <= 16384; }
    let total = w * h;
    let csize: usize = if cache_bits > 0 {
        proof { lemma_shl1(cache_bits); }
        (1u64 << cache_bits) as usize
    } else {
        0
    };
    let mut px: Vec<u32> = vec![0u32; total];
    let mut cache: Vec<u32> = vec![0u32; csize];
    proof {
        assert(stv(px@, 0, cache@) == st0(cache_bits as nat)) by {
            assert(cache@ =~= Seq::new(cache_size(cache_bits as nat), |_i: int| 0u32));
            assert(px@.take(0) =~= Seq::<u32>::empty());
        }
    }
    let mut infos: Vec<u64> = Vec::with_capacity(gs.len());
    let mut j: usize = 0;
    while j < gs.len()
        invariant
            infos@.len() == j, j <= gs@.len(), gs_wf(gs@, cache_bits as nat),
            forall|t: int| 0 <= t < j ==> #[trigger] info_ok(infos@[t], gs@[t]@),
        decreases gs@.len() - j,
    {
        proof { assert(group_wf(gs@[j as int]@, cache_bits as nat)); }
        infos.push(group_info(&gs[j], Ghost(cache_bits as nat)));
        j = j + 1;
    }
    let mut i: usize = 0;
    let mut x: usize = 0;
    let mut y: usize = 0;
    let mut trow = meta_row_x(m, 0, Ghost(w as nat), Ghost(h as nat), Ghost(gs@.len()));
    let mut p = pos;
    let mut win: u64 = 0;
    let mut k: u64 = 0;
    while i < total
        invariant
            buf_ok(buf@), p <= 8 * buf.len(), b == lbits(buf@), 1 <= w <= 16384, 1 <= h <= 16384,
            cache_bits <= 11, total == w * h, total <= 0x1000_0000, gs_wf(gs@, cache_bits as nat),
            meta_wf(m, w as nat, h as nat, gs@.len()), gsv == groups_view(gs@), mv == meta_view(m),
            px@.len() == total, cache@.len() == cache_size(cache_bits as nat), i <= total,
            x < w, i == y * w + x, k <= 56, win_k(b, p as int, win, k as nat),
            i < total ==> trow as int == meta_row(m, y as nat),
            infos@.len() == gs@.len(), forall|t: int| 0 <= t < gs@.len() ==> #[trigger] info_ok(infos@[t], gs@[t]@),
            dp(b, p as int, w as nat, total as nat, cache_bits as nat, gsv, mv, stv(px@, i as int, cache@))
                == target,
            target == decode_pixels(lbits(buf@), pos as int, w as nat, (w * h) as nat, cache_bits as nat,
                                    groups_view(gs@), meta_view(m), st0(cache_bits as nat)),
        decreases total - i,
    {
        let ghost st = stv(px@, i as int, cache@);
        proof {
            assert(y < h) by (nonlinear_arith) requires i == y * w + x, x < w, i < w * h, w >= 1;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(i as int, w as int, y as int, x as int);
            assert(st.px.len() == i);
        }
        let gi = group_in_row(m, trow, x, y, Ghost(w as nat), Ghost(h as nat), Ghost(gs@.len()));
        let g = vsimd::mem::get_ref(gs.as_slice(), gi);
        let info = vsimd::mem::get(infos.as_slice(), gi);
        proof {
            assert(group_wf(gs@[gi as int]@, cache_bits as nat));
            assert(gsv[gi as int] == codes_view(g@));
            assert(code_wf(&g@[0]) && codes_view(g@)[0] == g@[0].lens@);
        }
        proof {
            assert(group_at(mv, (i as int % w as int) as nat, (i as int / w as int) as nat) == gi);
            assert(gsv[group_at(mv, (st.px.len() as int % w as int) as nat, (st.px.len() as int / w as int) as nat)][0]
                == g@[0].lens@);
        }
        let ghost p0 = p;
        let (q, w1, k1, n) = match pix_step_w(buf, Ghost(b), p, win, k, w, total, cache_bits, g, info,
                                               Ghost(gsv), Ghost(mv), &mut px, i, &mut cache) {
            None => {
                proof {
                    lemma_dp_none(b, p as int, w as nat, total as nat, cache_bits as nat, gsv, mv, st);
                }
                return None;
            }
            Some(v) => v,
        };
        p = q;
        win = w1;
        k = k1;
        i = i + n;
        x = x + n;
        if x >= w {
            proof {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, w as int);
                assert(x / w <= x) by (nonlinear_arith) requires w >= 1;
                assert(i == (y + x / w) * w + x % w) by (nonlinear_arith)
                    requires x == (x / w) * w + x % w, i == y * w + x;
                assert(x % w < w) by (nonlinear_arith) requires w >= 1;
            }
            y = y + x / w;
            x = x % w;
            if i < total {
                proof { assert(y < h) by (nonlinear_arith) requires i == y * w + x, x < w, i < w * h, w >= 1; }
                trow = meta_row_x(m, y, Ghost(w as nat), Ghost(h as nat), Ghost(gs@.len()));
            }
        }
        proof {
            assert(stv(px@, i as int, cache@).px.len() == i);
            lemma_dp_step(b, p0 as int, w as nat, total as nat, cache_bits as nat, gsv, mv, st, stv(px@, i as int, cache@), p as int);
        }
    }
    proof {
        lemma_dp_end(b, p as int, w as nat, total as nat, cache_bits as nat, gsv, mv, stv(px@, i as int, cache@));
        assert(px@.take(total as int) =~= px@);
    }
    Some((px, p))
}

} // verus!
