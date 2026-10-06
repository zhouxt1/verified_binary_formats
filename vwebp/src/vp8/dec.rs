//! The verified VP8 key frame decoder: `vp8_x` computes `spec::vp8`.
use vstd::prelude::*;
use super::spec::*;
use super::bd::Bd;
use super::hdr::*;
use super::modes::*;
use super::tok::*;
use super::recon::*;
use super::lf::*;
use super::plane::*;

verus! {

pub enum Error {
    /// The frame is not a valid VP8 key frame (`spec::vp8` is None).
    Bad,
    /// The frame header says more than the allowed number of pixels.
    TooBig,
}

/// A decoded frame: `w` x `h` luma samples, and chroma planes of
/// `(w+1)/2` x `(h+1)/2`, each row by row.
pub struct FrameX {
    pub w: usize,
    pub h: usize,
    pub y: Vec<u8>,
    pub u: Vec<u8>,
    pub v: Vec<u8>,
}

impl FrameX {
    /// The buffers hold the spec's frame.
    pub open spec fn is(&self, f: Frame) -> bool {
        &&& self.w == f.w && self.h == f.h
        &&& holds(self.y@, f.w, f.y) && holds(self.u@, (f.w + 1) / 2, f.u) && holds(self.v@, (f.w + 1) / 2, f.v)
    }
}

/// A token partition's reader, without its buffer.
pub type St = (usize, usize, u32, u32, u32);

pub open spec fn st_view(s: St) -> BState { BState { pos: s.0 as nat, end: s.1 as nat, range: s.2, value: s.3, bit_count: s.4 } }

/// A reader's state, with dixie's zeros in the low `bit_count` bits of `value`.
pub open spec fn st_wf(s: St, n: nat) -> bool {
    128 <= s.2 <= 255 && s.4 < 8 && s.0 <= s.1 <= n && (s.3 >> s.4) << s.4 == s.3
}

/// What `spec::Dec` is, in the decoder's state.
pub open spec fn dec_view(yv: Seq<u8>, uv: Seq<u8>, vv: Seq<u8>, mbw: nat, mbh: nat, pl: Planes,
    ps: Seq<St>, above: Seq<[i32; 9]>, left: [i32; 9], rows: Seq<Vec<bool>>, row: Seq<bool>, cur_row: bool) -> Dec {
    Dec {
        pl,
        ps: ps.map_values(|s: St| st_view(s)),
        above: above.map_values(|a: [i32; 9]| ints(a@)),
        left: ints(left@),
        nz: if cur_row { rows.map_values(|r: Vec<bool>| r@).push(row) } else { rows.map_values(|r: Vec<bool>| r@) },
    }
}

/// The frame's planes, cropped (`crop`), in place: row `y` moves from
/// `y * wf` to `y * w`, below every row not moved yet.
fn crop_x(v: Vec<u8>, wf: usize, w: usize, h: usize, Ghost(pl): Ghost<Plane>) -> (r: Vec<u8>)
    requires holds(v@, wf as nat, pl), 1 <= w <= wf, h <= pl.len(),
    ensures holds(r@, w as nat, crop(pl, w as nat, h as nat)),
{
    let mut v = v;
    let n = v.len();
    if w < wf {
        let mut y: usize = 1;
        proof {
            assert forall|yy: int, xx: int| 0 <= yy < 1 && yy < h && 0 <= xx < w implies #[trigger] v@[yy * w + xx] == pl[yy][xx] by {
                assert(yy == 0 && yy * w + xx == yy * wf + xx);
            }
        }
        while y < h
            invariant
                1 <= w <= wf, h <= pl.len(), 1 <= y, y <= h || h == 0, n == v@.len(), n == pl.len() * wf, wf <= 16384, pl.len() <= 16384,
                forall|yy: int| 0 <= yy < pl.len() ==> (#[trigger] pl[yy]).len() == wf,
                forall|yy: int, xx: int| 0 <= yy < y && yy < h && 0 <= xx < w ==> #[trigger] v@[yy * w + xx] == pl[yy][xx],
                forall|yy: int, xx: int| y <= yy < pl.len() && 0 <= xx < wf ==> #[trigger] v@[yy * wf + xx] == pl[yy][xx],
            decreases h - y,
        {
            proof {
                lemma_idx(wf as nat, pl.len(), (w - 1) as int, y as int);
                assert(y * w <= y * wf) by (nonlinear_arith) requires w <= wf, y >= 0;
            }
            let ghost v0 = v@;
            vsimd::mem::copy_within(&mut v, y * wf, y * w, w);
            proof {
                assert forall|yy: int, xx: int| 0 <= yy < y + 1 && yy < h && 0 <= xx < w implies #[trigger] v@[yy * w + xx] == pl[yy][xx] by {
                    lemma_idx(w as nat, (y + 1) as nat, xx, yy);
                    if yy < y {
                        assert(yy * w + xx < y * w) by (nonlinear_arith) requires yy < y, 0 <= xx < w;
                        assert(v@[yy * w + xx] == v0[yy * w + xx]);
                    } else {
                        assert(yy * w + xx - y * w == xx);
                        assert(v@[yy * w + xx] == v0[y * wf + xx]);
                    }
                }
                assert forall|yy: int, xx: int| y + 1 <= yy < pl.len() && 0 <= xx < wf implies #[trigger] v@[yy * wf + xx] == pl[yy][xx] by {
                    lemma_idx(wf as nat, pl.len(), xx, yy);
                    assert(y * w + w <= yy * wf) by (nonlinear_arith) requires w <= wf, y + 1 <= yy, wf >= 0;
                    assert(yy * wf + xx >= y * w + w) by (nonlinear_arith) requires y * w + w <= yy * wf, xx >= 0;
                    assert(v@[yy * wf + xx] == v0[yy * wf + xx]);
                }
            }
            y = y + 1;
        }
    }
    proof {
        assert(w * h <= wf * pl.len()) by (nonlinear_arith) requires w <= wf, h <= pl.len();
        if w == wf {
            assert forall|yy: int, xx: int| 0 <= yy < h && 0 <= xx < w implies #[trigger] v@[yy * w + xx] == pl[yy][xx] by {}
        }
    }
    v.truncate(w * h);
    proof {
        let c = crop(pl, w as nat, h as nat);
        assert(v@.len() == c.len() * w) by (nonlinear_arith) requires v@.len() == w * h, c.len() == h;
        assert forall|yy: int, xx: int| 0 <= yy < c.len() && 0 <= xx < w implies v@[yy * w + xx] == #[trigger] c[yy][xx] by {
            lemma_idx(w as nat, h as nat, xx, yy);
        }
    }
    v
}

/// The decoder's state is a valid `Dec` for the frame.
pub open spec fn dec_ok(hd: &HdrX, parts: Seq<&[u8]>, fs: Seq<FacX>, mbs: Seq<Vec<MbX>>, mbw: nat, mbh: nat,
    pst: Seq<St>, above: Seq<[i32; 9]>, left: [i32; 9]) -> bool {
    &&& hd.wf() && 1 <= mbw <= 1024 && 1 <= mbh <= 1024
    &&& 1 <= parts.len() <= 8 && pst.len() == parts.len() && above.len() == mbw
    &&& forall|j: int| 0 <= j < parts.len() ==> st_wf(#[trigger] pst[j], parts[j]@.len())
    &&& forall|j: int| 0 <= j < mbw ==> ctx01(#[trigger] above[j]@)
    &&& ctx01(left@)
    &&& fs.len() == 4 && forall|i: int| 0 <= i < 4 ==> (#[trigger] fs[i]).view() == facs(hd.view())[i] && fs[i].wf()
    &&& hd.probs@.len() == 1056 && mbs.len() == mbh
    &&& forall|j: int| 0 <= j < mbh ==> (#[trigger] mbs[j])@.len() == mbw
    &&& forall|j: int, x: int| 0 <= j < mbh && 0 <= x < mbw ==> (#[trigger] mbs[j]@[x]).wf()
}

/// The tokens of macroblock (x, y) from its row's partition.
pub open spec fn mb_toks(hd: &HdrX, parts: Seq<&[u8]>, mbs: Seq<Vec<MbX>>, x: int, y: int, pst: Seq<St>, above: Seq<[i32; 9]>, left: [i32; 9]) -> TokState {
    let k = y % (parts.len() as int);
    let mb = mbs[y]@[x].view();
    mb_tokens(parts[k]@, hd.view().probs, facs(hd.view())[mb.segment as int], mb, st_view(pst[k]), ints(left@), ints(above[x]@))
}

/// A macroblock's tokens (`tokens_in`), with the token parser compiled for
/// BMI2 and LZCNT where the CPU has them. Trusted: only the CPU check.
#[verifier::external_body]
fn tokens_step(hd: &HdrX, parts: &Vec<&[u8]>, fs: &Vec<FacX>, mbs: &Vec<Vec<MbX>>, mbw: usize, mbh: usize, x: usize, y: usize,
    pst: &mut Vec<St>, above: &mut Vec<[i32; 9]>, left: &mut [i32; 9], co: &mut [i32; 400]) -> (r: (bool, u32))
    requires
        dec_ok(hd, parts@, fs@, mbs@, mbw as nat, mbh as nat, old(pst)@, old(above)@, *old(left)),
        x < mbw, y < mbh, old(co)@ == Seq::new(400, |k: int| 0i32),
    ensures
        dec_ok(hd, parts@, fs@, mbs@, mbw as nat, mbh as nat, final(pst)@, final(above)@, *final(left)), c16(final(co)@),
        ({
            let t = mb_toks(hd, parts@, mbs@, x as int, y as int, old(pst)@, old(above)@, *old(left));
            let k = (y as int) % (parts@.len() as int);
            &&& final(pst)@ == old(pst)@.update(k as int, final(pst)@[k as int]) && st_view(final(pst)@[k as int]) == t.s
            &&& final(above)@ == old(above)@.update(x as int, final(above)@[x as int]) && ints(final(above)@[x as int]@) == t.above
            &&& ints(final(left)@) == t.left && blocks(final(co)@) == t.coeffs && r.0 == t.nonzero
        }),
        forall|j: int| 0 <= j < 25 && #[trigger] bit(r.1, j) ==> acz(final(co)@, j),
{
    #[cfg(target_arch = "x86_64")]
    {
        if std::arch::is_x86_feature_detected!("bmi2") && std::arch::is_x86_feature_detected!("lzcnt") {
            // Sound: the CPU has the features tokens_bmi is compiled with.
            return unsafe { tokens_bmi(hd, parts, fs, mbs, mbw, mbh, x, y, pst, above, left, co) };
        }
    }
    tokens_in::<false>(hd, parts, fs, mbs, mbw, mbh, x, y, pst, above, left, co)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "bmi2,lzcnt")]
fn tokens_bmi(hd: &HdrX, parts: &Vec<&[u8]>, fs: &Vec<FacX>, mbs: &Vec<Vec<MbX>>, mbw: usize, mbh: usize, x: usize, y: usize,
    pst: &mut Vec<St>, above: &mut Vec<[i32; 9]>, left: &mut [i32; 9], co: &mut [i32; 400]) -> (r: (bool, u32))
    requires
        dec_ok(hd, parts@, fs@, mbs@, mbw as nat, mbh as nat, old(pst)@, old(above)@, *old(left)),
        x < mbw, y < mbh, old(co)@ == Seq::new(400, |k: int| 0i32),
    ensures
        dec_ok(hd, parts@, fs@, mbs@, mbw as nat, mbh as nat, final(pst)@, final(above)@, *final(left)), c16(final(co)@),
        ({
            let t = mb_toks(hd, parts@, mbs@, x as int, y as int, old(pst)@, old(above)@, *old(left));
            let k = (y as int) % (parts@.len() as int);
            &&& final(pst)@ == old(pst)@.update(k as int, final(pst)@[k as int]) && st_view(final(pst)@[k as int]) == t.s
            &&& final(above)@ == old(above)@.update(x as int, final(above)@[x as int]) && ints(final(above)@[x as int]@) == t.above
            &&& ints(final(left)@) == t.left && blocks(final(co)@) == t.coeffs && r.0 == t.nonzero
        }),
        forall|j: int| 0 <= j < 25 && #[trigger] bit(r.1, j) ==> acz(final(co)@, j),
{
    tokens_in::<true>(hd, parts, fs, mbs, mbw, mbh, x, y, pst, above, left, co)
}

#[inline(always)]
fn tokens_in<const BMI: bool>(hd: &HdrX, parts: &Vec<&[u8]>, fs: &Vec<FacX>, mbs: &Vec<Vec<MbX>>, mbw: usize, mbh: usize, x: usize, y: usize,
    pst: &mut Vec<St>, above: &mut Vec<[i32; 9]>, left: &mut [i32; 9], co: &mut [i32; 400]) -> (r: (bool, u32))
    requires
        dec_ok(hd, parts@, fs@, mbs@, mbw as nat, mbh as nat, old(pst)@, old(above)@, *old(left)),
        x < mbw, y < mbh, old(co)@ == Seq::new(400, |k: int| 0i32),
    ensures
        dec_ok(hd, parts@, fs@, mbs@, mbw as nat, mbh as nat, final(pst)@, final(above)@, *final(left)), c16(final(co)@),
        ({
            let t = mb_toks(hd, parts@, mbs@, x as int, y as int, old(pst)@, old(above)@, *old(left));
            let k = (y as int) % (parts@.len() as int);
            &&& final(pst)@ == old(pst)@.update(k as int, final(pst)@[k as int]) && st_view(final(pst)@[k as int]) == t.s
            &&& final(above)@ == old(above)@.update(x as int, final(above)@[x as int]) && ints(final(above)@[x as int]@) == t.above
            &&& ints(final(left)@) == t.left && blocks(final(co)@) == t.coeffs && r.0 == t.nonzero
        }),
        forall|j: int| 0 <= j < 25 && #[trigger] bit(r.1, j) ==> acz(final(co)@, j),
{
    let n = parts.len();
    let kk = y % n;
    let mb = &mbs[y][x];
    let st = pst[kk];
    let mut t = Bd::from_st(parts[kk], st);
    let mut ab = above[x];
    let f = &fs[mb.segment as usize];
    let r = mb_tokens_x::<BMI>(&mut t, &hd.probs, f, mb, left, &mut ab, co);
    pst.set(kk, t.to_st());
    above.set(x, ab);
    r
}

/// Macroblock (x, y): its tokens, then its reconstruction (`decode_mb`).
fn decode_mb_x(hd: &HdrX, parts: &Vec<&[u8]>, fs: &Vec<FacX>, mbs: &Vec<Vec<MbX>>, mbw: usize, mbh: usize, x: usize, y: usize,
    pst: &mut Vec<St>, above: &mut Vec<[i32; 9]>, left: &mut [i32; 9], rows: &Vec<Vec<bool>>, row: &mut Vec<bool>,
    yv: &mut Vec<u8>, uv: &mut Vec<u8>, vv: &mut Vec<u8>, Ghost(pl): Ghost<Planes>) -> (pl2: Ghost<Planes>)
    requires
        dec_ok(hd, parts@, fs@, mbs@, mbw as nat, mbh as nat, old(pst)@, old(above)@, *old(left)),
        x < mbw, y < mbh, holds3(old(yv)@, old(uv)@, old(vv)@, mbw as nat, mbh as nat, pl), rows@.len() == y,
    ensures
        dec_ok(hd, parts@, fs@, mbs@, mbw as nat, mbh as nat, final(pst)@, final(above)@, *final(left)),
        holds3(final(yv)@, final(uv)@, final(vv)@, mbw as nat, mbh as nat, pl2@), final(row)@.len() == old(row)@.len() + 1,
        dec_view(final(yv)@, final(uv)@, final(vv)@, mbw as nat, mbh as nat, pl2@, final(pst)@, final(above)@, *final(left), rows@, final(row)@, true)
            == decode_mb(hd.view(), views(parts@), rows_view(mbs@), mbw as int, x as int, y as int,
                dec_view(old(yv)@, old(uv)@, old(vv)@, mbw as nat, mbh as nat, pl, old(pst)@, old(above)@, *old(left), rows@, old(row)@, true)),
{
    let ghost d = dec_view(yv@, uv@, vv@, mbw as nat, mbh as nat, pl, pst@, above@, *left, rows@, row@, true);
    let ghost t = mb_toks(hd, parts@, mbs@, x as int, y as int, pst@, above@, *left);
    let ghost pst0 = pst@;
    let ghost above0 = above@;
    let mut co: [i32; 400] = [0; 400];
    proof { assert(co@ =~= Seq::new(400, |k: int| 0i32)); }
    let (nz, dcx) = tokens_step(hd, parts, fs, mbs, mbw, mbh, x, y, pst, above, left, &mut co);
    let mb = &mbs[y][x];
    let yw = mbw * 16;
    let cw = mbw * 8;
    luma_x(yv, yw, mbw, x, y, mb, &co, dcx, Ghost(pl.y));
    chroma_x(uv, cw, mbw, x, y, mb.uv_mode, &co, 16, dcx, Ghost(pl.u));
    chroma_x(vv, cw, mbw, x, y, mb.uv_mode, &co, 20, dcx, Ghost(pl.v));
    let ghost r0 = row@;
    row.push(nz);
    let ghost pl2 = Planes {
        y: luma(pl.y, mbw as int, x as int, y as int, mb.view(), t.coeffs),
        u: chroma(pl.u, x as int, y as int, mb.uv_mode as nat, t.coeffs, 16),
        v: chroma(pl.v, x as int, y as int, mb.uv_mode as nat, t.coeffs, 20),
    };
    proof {
        reveal(decode_mb);
        let psv = views(parts@);
        let mv = rows_view(mbs@);
        let k = (y as int) % (parts@.len() as int);
        assert(mv[y as int][x as int] == mb.view());
        assert(psv[k as int] == parts@[k as int]@);
        assert(d.ps[k as int] == st_view(pst0[k as int]));
        assert(d.above[x as int] == ints(above0[x as int]@));
        let got = dec_view(yv@, uv@, vv@, mbw as nat, mbh as nat, pl2, pst@, above@, *left, rows@, row@, true);
        let want = decode_mb(hd.view(), psv, mv, mbw as int, x as int, y as int, d);
        assert(got.ps =~= want.ps);
        assert(got.above =~= want.above);
        assert(got.nz =~= want.nz);
        assert(got == want);
    }
    Ghost(pl2)
}

pub open spec fn hv_of(hd: &HdrX) -> Hdr { hd.view() }

/// Decode a VP8 key frame (`spec::vp8`), refusing one whose header says
/// more than `max_pixels` pixels.
pub fn vp8_x(b: &[u8], max_pixels: u64) -> (r: Result<FrameX, Error>)
    ensures
        match r {
            Ok(f) => vp8(b@).is_some() && f.is(vp8(b@).unwrap()),
            Err(Error::Bad) => vp8(b@).is_none(),
            Err(Error::TooBig) => header(b@).is_some() && header(b@).unwrap().0.w * header(b@).unwrap().0.h > max_pixels,
        },
{
    let (hd, mut bd, parts) = match header_x(b) {
        None => return Err(Error::Bad),
        Some(t) => t,
    };
    proof { assert((hd.w as u64) * (hd.h as u64) < 16384 * 16384) by (nonlinear_arith) requires hd.w < 16384, hd.h < 16384; }
    if (hd.w as u64) * (hd.h as u64) > max_pixels {
        return Err(Error::TooBig);
    }
    let ghost hv = hd.view();
    let ghost psv = views(parts@);
    let mbw = (hd.w + 15) / 16;
    let mbh = (hd.h + 15) / 16;
    let mbs = modes_x(&hd, &mut bd, mbw, mbh);
    let ghost mv = rows_view(mbs@);
    let fs = facs_x(&hd);
    // Token partitions' readers.
    let n = parts.len();
    let mut pst: Vec<St> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n, n == parts@.len(), 1 <= n <= 8, pst@.len() == k, psv == views(parts@),
            forall|j: int| 0 <= j < k ==> st_wf(#[trigger] pst@[j], parts@[j]@.len()) && st_view(pst@[j]) == b_init(parts@[j]@),
        decreases n - k,
    {
        let t = Bd::new(parts[k]);
        pst.push(t.to_st());
        k = k + 1;
    }
    let yw = mbw * 16;
    let cw = mbw * 8;
    let mut yv = zeroed(yw, mbh * 16);
    let mut uv = zeroed(cw, mbh * 8);
    let mut vv = zeroed(cw, mbh * 8);
    let mut above: Vec<[i32; 9]> = Vec::new();
    let mut x: usize = 0;
    while x < mbw
        invariant x <= mbw, above@.len() == x,
            forall|j: int| 0 <= j < x ==> #[trigger] ints(above@[j]@) == zeros9(),
            forall|j: int| 0 <= j < x ==> ctx01(#[trigger] above@[j]@),
        decreases mbw - x,
    {
        let z: [i32; 9] = [0; 9];
        proof { assert(ints(z@) =~= zeros9()); }
        above.push(z);
        x = x + 1;
    }
    let mut rows: Vec<Vec<bool>> = Vec::new();
    let ghost d0 = dec0(psv, mbw as int, mbh as int);
    let mut left: [i32; 9] = [0; 9];
    let ghost mut pl = d0.pl;
    proof {
        assert(pst@.map_values(|s: St| st_view(s)) =~= d0.ps);
        assert(above@.map_values(|a: [i32; 9]| ints(a@)) =~= d0.above);
        assert(rows@.map_values(|r: Vec<bool>| r@) =~= d0.nz);
        assert(ints(left@) =~= zeros9());
        assert(dec_view(yv@, uv@, vv@, mbw as nat, mbh as nat, pl, pst@, above@, left, rows@, Seq::empty(), false) == d0);
    }
    let mut y: usize = 0;
    while y < mbh
        invariant
            dec_ok(&hd, parts@, fs@, mbs@, mbw as nat, mbh as nat, pst@, above@, left),
            hv == hd.view(), psv == views(parts@), mv == rows_view(mbs@), y <= mbh, rows@.len() == y,
            forall|j: int| 0 <= j < y ==> (#[trigger] rows@[j])@.len() == mbw,
            holds3(yv@, uv@, vv@, mbw as nat, mbh as nat, pl),
            decode_rows(hv, psv, mv, mbw as int, mbh as int, y as int,
                dec_view(yv@, uv@, vv@, mbw as nat, mbh as nat, pl, pst@, above@, left, rows@, Seq::empty(), false))
                == decode_rows(hv, psv, mv, mbw as int, mbh as int, 0, d0),
        decreases mbh - y,
    {
        let ghost dprev = dec_view(yv@, uv@, vv@, mbw as nat, mbh as nat, pl, pst@, above@, left, rows@, Seq::empty(), false);
        left = [0; 9];
        let mut row: Vec<bool> = Vec::new();
        let ghost dstart = dec_view(yv@, uv@, vv@, mbw as nat, mbh as nat, pl, pst@, above@, left, rows@, row@, true);
        proof {
            assert(ints(left@) =~= zeros9());
            assert(dstart =~~= Dec { pl: dprev.pl, ps: dprev.ps, above: dprev.above, left: zeros9(), nz: dprev.nz.push(Seq::empty()) });
        }
        let mut x: usize = 0;
        while x < mbw
            invariant
                dec_ok(&hd, parts@, fs@, mbs@, mbw as nat, mbh as nat, pst@, above@, left),
                hv == hd.view(), psv == views(parts@), mv == rows_view(mbs@), y < mbh, x <= mbw, rows@.len() == y, row@.len() == x,
                forall|j: int| 0 <= j < y ==> (#[trigger] rows@[j])@.len() == mbw,
                holds3(yv@, uv@, vv@, mbw as nat, mbh as nat, pl),
                decode_row(hv, psv, mv, mbw as int, x as int, y as int,
                    dec_view(yv@, uv@, vv@, mbw as nat, mbh as nat, pl, pst@, above@, left, rows@, row@, true))
                    == decode_row(hv, psv, mv, mbw as int, 0, y as int, dstart),
            decreases mbw - x,
        {
            let p2 = decode_mb_x(&hd, &parts, &fs, &mbs, mbw, mbh, x, y, &mut pst, &mut above, &mut left, &rows, &mut row,
                &mut yv, &mut uv, &mut vv, Ghost(pl));
            proof { pl = p2@; }
            x = x + 1;
        }
        let ghost dend = dec_view(yv@, uv@, vv@, mbw as nat, mbh as nat, pl, pst@, above@, left, rows@, row@, true);
        let ghost r0 = rows@;
        rows.push(row);
        proof {
            assert(rows@.map_values(|r: Vec<bool>| r@) =~= r0.map_values(|r: Vec<bool>| r@).push(dend.nz.last()));
            assert(dec_view(yv@, uv@, vv@, mbw as nat, mbh as nat, pl, pst@, above@, left, rows@, Seq::empty(), false) =~~= dend);
        }
        y = y + 1;
    }
    loop_filter_x(&hd, &mbs, &rows, mbw, mbh, &mut yv, &mut uv, &mut vv, Ghost(pl));
    let ghost fl = loop_filter(hv, mv, rows@.map_values(|r: Vec<bool>| r@), mbw as int, mbh as int, 0, pl);
    let w = hd.w;
    let h = hd.h;
    let cwo = (w + 1) / 2;
    let cho = (h + 1) / 2;
    proof {
        assert(planes(b@) == Some((hv, fl)));
    }
    let fy = crop_x(yv, yw, w, h, Ghost(fl.y));
    let fu = crop_x(uv, cw, cwo, cho, Ghost(fl.u));
    let fv = crop_x(vv, cw, cwo, cho, Ghost(fl.v));
    Ok(FrameX { w, h, y: fy, u: fu, v: fv })
}

} // verus!
