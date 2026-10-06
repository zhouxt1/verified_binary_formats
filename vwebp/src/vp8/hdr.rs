//! The frame header and the first partition's header, proved to follow
//! `spec::header`.
use vstd::prelude::*;
use super::spec::*;
use super::tab::*;
use super::bd::Bd;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;

verus! {

/// Machine integers as the spec's.
pub open spec fn ints(s: Seq<i32>) -> Seq<int> { s.map_values(|x: i32| x as int) }

pub struct SegX {
    pub enabled: bool,
    pub update_map: bool,
    pub update_data: bool,
    pub abs: bool,
    pub tree: Vec<u8>,
    pub lf: Vec<i32>,
    pub quant: Vec<i32>,
}

pub struct FiltX {
    pub simple: bool,
    pub level: i32,
    pub sharpness: i32,
    pub delta: bool,
    pub ref_delta: Vec<i32>,
    pub mode_delta: Vec<i32>,
}

pub struct QuantX {
    pub q: i32,
    pub y1_dc: i32,
    pub y2_dc: i32,
    pub y2_ac: i32,
    pub uv_dc: i32,
    pub uv_ac: i32,
}

pub struct HdrX {
    pub w: usize,
    pub h: usize,
    pub seg: SegX,
    pub filt: FiltX,
    pub quant: QuantX,
    pub probs: Vec<u8>,
    pub skip: Option<u8>,
}

impl SegX {
    pub open spec fn view(&self) -> Seg {
        Seg { enabled: self.enabled, update_map: self.update_map, update_data: self.update_data, abs: self.abs,
              tree: self.tree@, lf: ints(self.lf@), quant: ints(self.quant@) }
    }
}

impl FiltX {
    pub open spec fn view(&self) -> Filt {
        Filt { simple: self.simple, level: self.level as int, sharpness: self.sharpness as int, delta: self.delta,
               ref_delta: ints(self.ref_delta@), mode_delta: ints(self.mode_delta@) }
    }
}

impl QuantX {
    pub open spec fn view(&self) -> Quant {
        Quant { q: self.q as int, y1_dc: self.y1_dc as int, y2_dc: self.y2_dc as int, y2_ac: self.y2_ac as int,
                uv_dc: self.uv_dc as int, uv_ac: self.uv_ac as int }
    }
}

impl HdrX {
    pub open spec fn view(&self) -> Hdr {
        Hdr { w: self.w as nat, h: self.h as nat, seg: self.seg.view(), filt: self.filt.view(), quant: self.quant.view(),
              probs: self.probs@, skip: self.skip }
    }

    /// The header's values are in the ranges the readers give.
    pub open spec fn wf(&self) -> bool {
        &&& 1 <= self.w < 16384 && 1 <= self.h < 16384
        &&& self.seg.tree@.len() == 3 && self.seg.lf@.len() == 4 && self.seg.quant@.len() == 4
        &&& forall|i: int| 0 <= i < 4 ==> -128 < #[trigger] self.seg.lf@[i] < 128
        &&& forall|i: int| 0 <= i < 4 ==> -128 < #[trigger] self.seg.quant@[i] < 128
        &&& 0 <= self.filt.level < 64 && 0 <= self.filt.sharpness < 8
        &&& self.filt.ref_delta@.len() == 4 && self.filt.mode_delta@.len() == 4
        &&& forall|i: int| 0 <= i < 4 ==> -64 < #[trigger] self.filt.ref_delta@[i] < 64
        &&& forall|i: int| 0 <= i < 4 ==> -64 < #[trigger] self.filt.mode_delta@[i] < 64
        &&& 0 <= self.quant.q < 128
        &&& -16 < self.quant.y1_dc < 16 && -16 < self.quant.y2_dc < 16 && -16 < self.quant.y2_ac < 16
        &&& -16 < self.quant.uv_dc < 16 && -16 < self.quant.uv_ac < 16
        &&& self.probs@.len() == 1056
    }
}

/// `k` values of `b_maybe(n)` (`b_maybes`), each of magnitude below 2^n.
fn maybes(bd: &mut Bd, n: u32, k: usize) -> (r: Vec<i32>)
    requires old(bd).wf(), n <= 7,
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, r@.len() == k,
        (ints(r@), final(bd).view()) == b_maybes(old(bd).buf@, old(bd).view(), n as nat, k as nat, Seq::empty()),
        forall|i: int| 0 <= i < k ==> -(p2(n as nat) as int) < #[trigger] r@[i] < (p2(n as nat) as int),
{
    let ghost buf = bd.buf@;
    let ghost s0 = bd.view();
    let mut r: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    proof { assert(ints(r@) =~= Seq::<int>::empty()); }
    while i < k
        invariant
            bd.wf(), bd.buf@ == buf, i <= k, r@.len() == i, n <= 7,
            b_maybes(buf, bd.view(), n as nat, (k - i) as nat, ints(r@)) == b_maybes(buf, s0, n as nat, k as nat, Seq::empty()),
            forall|j: int| 0 <= j < i ==> -(p2(n as nat) as int) < #[trigger] r@[j] < (p2(n as nat) as int),
        decreases k - i,
    {
        let ghost sb = bd.view();
        let ghost r0 = r@;
        let v = bd.maybe(n);
        proof {
            lemma_maybe_bound(buf, sb, n);
            assert(b_maybes(buf, sb, n as nat, (k - i) as nat, ints(r0))
                == b_maybes(buf, bd.view(), n as nat, (k - i - 1) as nat, ints(r0).push(v as int)));
        }
        r.push(v);
        proof { assert(ints(r@) =~= ints(r0).push(v as int)); }
        i = i + 1;
    }
    r
}

pub proof fn lemma_uint_bound(buf: Seq<u8>, s: BState, n: nat)
    ensures 0 <= b_uint(buf, s, n).0 < p2(n),
    decreases n,
{
    if n > 0 {
        lemma_uint_bound(buf, s, (n - 1) as nat);
    }
}

pub proof fn lemma_maybe_bound(buf: Seq<u8>, s: BState, n: u32)
    requires n <= 7,
    ensures -(p2(n as nat) as int) < b_maybe(buf, s, n as nat).0 < (p2(n as nat) as int),
{
    let (f, s1) = b_bit(buf, s);
    vbits::bitspec::lemma_p2_pos(n as nat);
    if f { lemma_uint_bound(buf, s1, n as nat); }
}

pub proof fn lemma_p2_7(n: nat)
    requires n <= 8,
    ensures p2(n) <= 256, p2(7) == 128, p2(6) == 64,
{
    reveal_with_fuel(p2, 9);
}

fn zero4() -> (r: Vec<i32>)
    ensures ints(r@) == zeros4(), r@.len() == 4, forall|i: int| 0 <= i < 4 ==> #[trigger] r@[i] == 0,
{
    let mut r = Vec::new();
    r.push(0); r.push(0); r.push(0); r.push(0);
    proof { assert(ints(r@) =~= zeros4()); }
    r
}

fn tree0() -> (r: Vec<u8>)
    ensures r@ == seq![0u8, 0, 0],
{
    let mut r = Vec::new();
    r.push(0); r.push(0); r.push(0);
    proof { assert(r@ =~= seq![0u8, 0, 0]); }
    r
}

/// The segment tree's probabilities (`tree_probs`).
fn tree3(bd: &mut Bd) -> (r: Vec<u8>)
    requires old(bd).wf(),
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, r@.len() == 3,
        (r@, final(bd).view()) == tree_probs(old(bd).buf@, old(bd).view(), 3, Seq::empty()),
{
    let ghost buf = bd.buf@;
    let ghost s0 = bd.view();
    let mut r: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < 3
        invariant
            bd.wf(), bd.buf@ == buf, i <= 3, r@.len() == i,
            tree_probs(buf, bd.view(), (3 - i) as nat, r@) == tree_probs(buf, s0, 3, Seq::empty()),
        decreases 3 - i,
    {
        let ghost sb = bd.view();
        let f = bd.bit();
        let v: u8 = if f {
            let ghost s1 = bd.view();
            let u = bd.uint(8);
            proof { lemma_uint_bound(buf, s1, 8); lemma_p2_7(8); }
            u as u8
        } else {
            255
        };
        r.push(v);
        i = i + 1;
    }
    r
}

/// decode_segmentation_header (`seg_hdr`).
fn seg_hdr_x(bd: &mut Bd) -> (r: SegX)
    requires old(bd).wf(),
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@,
        (r.view(), final(bd).view()) == seg_hdr(old(bd).buf@, old(bd).view()),
        r.tree@.len() == 3, r.lf@.len() == 4, r.quant@.len() == 4,
        forall|i: int| 0 <= i < 4 ==> -128 < #[trigger] r.lf@[i] < 128,
        forall|i: int| 0 <= i < 4 ==> -128 < #[trigger] r.quant@[i] < 128,
{
    let ghost buf = bd.buf@;
    let ghost s0 = bd.view();
    let en = bd.bit();
    if !en {
        return SegX { enabled: false, update_map: false, update_data: false, abs: false, tree: tree0(),
                      lf: zero4(), quant: zero4() };
    }
    let um = bd.bit();
    let ud = bd.bit();
    let abs = if ud { bd.bit() } else { false };
    let quant = if ud { maybes(bd, 7, 4) } else { zero4() };
    let lf = if ud { maybes(bd, 6, 4) } else { zero4() };
    let tree = if um { tree3(bd) } else { tree0() };
    proof {
        lemma_p2_7(7);
        lemma_p2_7(6);
    }
    SegX { enabled: true, update_map: um, update_data: ud, abs, tree, lf, quant }
}

/// decode_loopfilter_header (`filt_hdr`).
fn filt_hdr_x(bd: &mut Bd) -> (r: FiltX)
    requires old(bd).wf(),
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@,
        (r.view(), final(bd).view()) == filt_hdr(old(bd).buf@, old(bd).view()),
        0 <= r.level < 64, 0 <= r.sharpness < 8, r.ref_delta@.len() == 4, r.mode_delta@.len() == 4,
        forall|i: int| 0 <= i < 4 ==> -64 < #[trigger] r.ref_delta@[i] < 64,
        forall|i: int| 0 <= i < 4 ==> -64 < #[trigger] r.mode_delta@[i] < 64,
{
    let ghost buf = bd.buf@;
    let simple = bd.bit();
    let ghost s1 = bd.view();
    let level = bd.uint(6);
    let ghost s2 = bd.view();
    let sharpness = bd.uint(3);
    proof { lemma_uint_bound(buf, s1, 6); lemma_uint_bound(buf, s2, 3); reveal_with_fuel(p2, 7); }
    let delta = bd.bit();
    let upd = if delta { bd.bit() } else { false };
    let ref_delta = if upd { maybes(bd, 6, 4) } else { zero4() };
    let mode_delta = if upd { maybes(bd, 6, 4) } else { zero4() };
    proof { lemma_p2_7(6); }
    FiltX { simple, level: level as i32, sharpness: sharpness as i32, delta, ref_delta, mode_delta }
}

/// decode_quantizer_header (`quant_hdr`).
fn quant_hdr_x(bd: &mut Bd) -> (r: QuantX)
    requires old(bd).wf(),
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@,
        (r.view(), final(bd).view()) == quant_hdr(old(bd).buf@, old(bd).view()),
        0 <= r.q < 128, -16 < r.y1_dc < 16, -16 < r.y2_dc < 16, -16 < r.y2_ac < 16, -16 < r.uv_dc < 16, -16 < r.uv_ac < 16,
{
    let ghost buf = bd.buf@;
    let ghost s0 = bd.view();
    let q = bd.uint(7);
    proof { lemma_uint_bound(buf, s0, 7); reveal_with_fuel(p2, 8); }
    let ghost s1 = bd.view();
    let y1_dc = bd.maybe(4);
    let ghost s2 = bd.view();
    let y2_dc = bd.maybe(4);
    let ghost s3 = bd.view();
    let y2_ac = bd.maybe(4);
    let ghost s4 = bd.view();
    let uv_dc = bd.maybe(4);
    let ghost s5 = bd.view();
    let uv_ac = bd.maybe(4);
    proof {
        lemma_maybe_bound(buf, s1, 4); lemma_maybe_bound(buf, s2, 4); lemma_maybe_bound(buf, s3, 4);
        lemma_maybe_bound(buf, s4, 4); lemma_maybe_bound(buf, s5, 4);
    }
    QuantX { q: q as i32, y1_dc, y2_dc, y2_ac, uv_dc, uv_ac }
}

/// decode_entropy_header's coefficient probability updates (`coeff_probs`).
fn coeff_probs_x(bd: &mut Bd) -> (r: Vec<u8>)
    requires old(bd).wf(),
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, r@.len() == 1056,
        (r@, final(bd).view()) == coeff_probs(old(bd).buf@, old(bd).view(), Seq::empty()),
{
    let ghost buf = bd.buf@;
    let ghost s0 = bd.view();
    let mut r: Vec<u8> = Vec::with_capacity(1056);
    let mut i: usize = 0;
    while i < 1056
        invariant
            bd.wf(), bd.buf@ == buf, i <= 1056, r@.len() == i,
            coeff_probs(buf, bd.view(), r@) == coeff_probs(buf, s0, Seq::empty()),
        decreases 1056 - i,
    {
        let u = bd.get(COEFF_UPDATE_PROBS[i]);
        let v: u8 = if u {
            let ghost s1 = bd.view();
            let x = bd.uint(8);
            proof { lemma_uint_bound(buf, s1, 8); lemma_p2_7(8); }
            x as u8
        } else {
            DEFAULT_COEFF_PROBS[i]
        };
        r.push(v);
        i = i + 1;
    }
    r
}

/// Views of partitions.
pub open spec fn views(ps: Seq<&[u8]>) -> Seq<Seq<u8>> { ps.map_values(|p: &[u8]| p@) }

/// decode_and_init_token_partitions (`token_parts`).
fn token_parts_x<'a>(rest: &'a [u8], n: usize) -> (r: Option<Vec<&'a [u8]>>)
    requires 1 <= n <= 8,
    ensures match token_parts(rest@, n as nat) {
        None => r.is_none(),
        Some(ps) => r.is_some() && views(r.unwrap()@) == ps && r.unwrap()@.len() == n,
    },
{
    if rest.len() < 3 * (n - 1) {
        return None;
    }
    let mut sz = rest.len() - 3 * (n - 1);
    let mut at = 3 * (n - 1);
    let mut acc: Vec<&'a [u8]> = Vec::new();
    let mut i: usize = 0;
    proof { assert(views(acc@) =~= Seq::<Seq<u8>>::empty()); }
    while i < n
        invariant
            1 <= n <= 8, i <= n, acc@.len() == i, 3 * (n - 1) <= rest@.len(), at + sz == rest@.len(),
            token_parts(rest@, n as nat) == parts(rest@, n as nat, at as nat, sz as nat, views(acc@)),
        decreases n - i,
    {
        let psz: usize = if i < n - 1 {
            rest[3 * i] as usize + 256 * rest[3 * i + 1] as usize + 65536 * rest[3 * i + 2] as usize
        } else {
            sz
        };
        if sz < psz || at + psz > rest.len() {
            return None;
        }
        let p = vstd::slice::slice_subrange(rest, at, at + psz);
        let ghost a0 = acc@;
        proof {
            assert(views(a0).len() == i);
            assert(psz == if (i as int) < n - 1 { le24(rest@, 3 * i) } else { sz as nat });
        }
        acc.push(p);
        proof { assert(views(acc@) =~= views(a0).push(p@)); }
        at = at + psz;
        sz = sz - psz;
        i = i + 1;
    }
    Some(acc)
}

/// The frame header and the first partition's (`header`): the header, the
/// first partition's reader after it, and the token partitions.
pub fn header_x<'a>(b: &'a [u8]) -> (r: Option<(HdrX, Bd<'a>, Vec<&'a [u8]>)>)
    ensures match header(b@) {
        None => r.is_none(),
        Some((hd, p0, s, ps)) => r.is_some() && ({
            let (hx, bd, px) = r.unwrap();
            &&& hx.view() == hd && hx.wf()
            &&& bd.wf() && bd.buf@ == p0 && bd.view() == s
            &&& views(px@) == ps && 1 <= px@.len() <= 8
        }),
    },
{
    if b.len() < 10 {
        return None;
    }
    let t: usize = b[0] as usize + 256 * b[1] as usize + 65536 * b[2] as usize;
    let part0 = t / 32;
    if b.len() <= part0 + 10 || t % 2 != 0 || b[3] != 0x9d || b[4] != 0x01 || b[5] != 0x2a {
        return None;
    }
    let w = b[6] as usize + 256 * (b[7] as usize % 64);
    let h = b[8] as usize + 256 * (b[9] as usize % 64);
    if w == 0 || h == 0 || (t / 8) % 2 == 1 {
        return None;
    }
    let p0 = vstd::slice::slice_subrange(b, 10, 10 + part0);
    let rest = vstd::slice::slice_subrange(b, 10 + part0, b.len());
    let mut bd = Bd::new(p0);
    let cs = bd.uint(2);
    if cs != 0 {
        return None;
    }
    let seg = seg_hdr_x(&mut bd);
    let filt = filt_hdr_x(&mut bd);
    let ghost s3 = bd.view();
    let np = bd.uint(2);
    proof { lemma_uint_bound(p0@, s3, 2); reveal_with_fuel(p2, 3); }
    let n: usize = if np == 0 { 1 } else if np == 1 { 2 } else if np == 2 { 4 } else { 8 };
    let ps = match token_parts_x(rest, n) {
        None => return None,
        Some(ps) => ps,
    };
    let quant = quant_hdr_x(&mut bd);
    let _refresh = bd.bit();
    let probs = coeff_probs_x(&mut bd);
    let sk = bd.bit();
    let skip = if sk {
        let ghost s8 = bd.view();
        let v = bd.uint(8);
        proof { lemma_uint_bound(p0@, s8, 8); lemma_p2_7(8); }
        Some(v as u8)
    } else {
        None
    };
    let hx = HdrX { w, h, seg, filt, quant, probs, skip };
    proof {
        assert(tag(b@) == t);
        assert(p0@ == b@.subrange(10, (10 + part0) as int));
        assert(rest@ == b@.subrange((10 + part0) as int, b@.len() as int));
        assert(hx.wf());
        assert(header(b@) == Some((hx.view(), p0@, bd.view(), views(ps@))));
    }
    Some((hx, bd, ps))
}

} // verus!
