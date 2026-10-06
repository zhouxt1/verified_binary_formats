//! A macroblock's tokens, proved to follow `spec::mb_tokens`.
use vstd::prelude::*;
use super::spec::*;
use super::tab::*;
use super::bd::Bd;
use super::hdr::*;
use super::modes::MbX;
use vsimd::mem::{get, aget, aset};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;

verus! {

pub struct FacX {
    pub y1: (i32, i32),
    pub uv: (i32, i32),
    pub y2: (i32, i32),
}

impl FacX {
    pub open spec fn view(&self) -> Fac {
        Fac { y1: (self.y1.0 as int, self.y1.1 as int), uv: (self.uv.0 as int, self.uv.1 as int), y2: (self.y2.0 as int, self.y2.1 as int) }
    }

    pub open spec fn wf(&self) -> bool {
        &&& 0 <= self.y1.0 <= 512 && 0 <= self.y1.1 <= 512
        &&& 0 <= self.uv.0 <= 512 && 0 <= self.uv.1 <= 512
        &&& 0 <= self.y2.0 <= 512 && 0 <= self.y2.1 <= 512
    }
}

pub open spec fn qwf(q: QuantX) -> bool {
    &&& 0 <= q.q < 128
    &&& -16 < q.y1_dc < 16 && -16 < q.y2_dc < 16 && -16 < q.y2_ac < 16 && -16 < q.uv_dc < 16 && -16 < q.uv_ac < 16
}

fn clamp_q_x(q: i32) -> (r: usize)
    ensures r as int == clamp_q(q as int), r < 128,
{
    if q < 0 { 0 } else if q > 127 { 127 } else { q as usize }
}

proof fn lemma_tables(i: int)
    requires 0 <= i < 128,
    ensures 4 <= DC_Q@[i] <= 157, 4 <= AC_Q@[i] <= 284,
{
}

/// dequant_init for one segment (`factors`).
fn factors_x(q: i32, qh: &QuantX) -> (r: FacX)
    requires -300 < q < 300, qwf(*qh),
    ensures r.view() == factors(q as int, qh.view()), r.wf(),
{
    let delta_update = qh.q != 0 || qh.y1_dc != 0 || qh.y2_dc != 0 || qh.y2_ac != 0 || qh.uv_dc != 0 || qh.uv_ac != 0;
    if q == -1 && !delta_update {
        return FacX { y1: (0, 0), uv: (0, 0), y2: (0, 0) };
    }
    let i1 = clamp_q_x(q + qh.y1_dc);
    let i2 = clamp_q_x(q);
    let i3 = clamp_q_x(q + qh.uv_dc);
    let i4 = clamp_q_x(q + qh.uv_ac);
    let i5 = clamp_q_x(q + qh.y2_dc);
    let i6 = clamp_q_x(q + qh.y2_ac);
    proof {
        lemma_tables(i1 as int); lemma_tables(i2 as int); lemma_tables(i3 as int);
        lemma_tables(i4 as int); lemma_tables(i5 as int); lemma_tables(i6 as int);
    }
    let y2ac = AC_Q[i6] * 155 / 100;
    let uvdc = DC_Q[i3];
    FacX {
        y1: (DC_Q[i1], AC_Q[i2]),
        uv: (if uvdc > 132 { 132 } else { uvdc }, AC_Q[i4]),
        y2: (DC_Q[i5] * 2, if y2ac < 8 { 8 } else { y2ac }),
    }
}

/// Every segment's factors (`facs`).
pub fn facs_x(hd: &HdrX) -> (r: Vec<FacX>)
    requires hd.wf(),
    ensures r@.len() == 4, forall|i: int| 0 <= i < 4 ==> (#[trigger] r@[i]).view() == facs(hd.view())[i] && r@[i].wf(),
{
    let mut r: Vec<FacX> = Vec::new();
    let mut i: usize = 0;
    while i < 4
        invariant hd.wf(), i <= 4, r@.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] r@[j]).view() == facs(hd.view())[j] && r@[j].wf(),
        decreases 4 - i,
    {
        let q = if !hd.seg.enabled { hd.quant.q } else if hd.seg.abs { hd.seg.quant[i] } else { hd.quant.q + hd.seg.quant[i] };
        proof { assert(q as int == seg_q(hd.view(), i as int)); }
        r.push(factors_x(q, &hd.quant));
        i = i + 1;
    }
    r
}

/// A value in 16 bits (`wrap16`): a truncation to `i16`.
#[inline(always)]
pub fn wrap16_x(x: i32) -> (r: i32)
    ensures r as int == wrap16(x as int), -32768 <= r <= 32767,
{
    let t = x as i16;
    let r = t as i32;
    proof {
        let m = x & 0xffff;
        assert(m as int == (x as int) % 65536) by (bit_vector) requires m == x & 0xffff;
        assert(m >= 32768 ==> r == (m - 65536) as i32) by (bit_vector) requires m == x & 0xffff, t == x as i16, r == t as i32;
        assert(m < 32768 ==> r == m) by (bit_vector) requires m == x & 0xffff, t == x as i16, r == t as i32;
    }
    r
}

/// `extra`: `n` bits at the probabilities `CAT_PROBS[at..]`, added to 0.
#[inline(always)]
fn extra_x(bd: &mut Bd, at: usize, n: usize) -> (r: i32)
    requires old(bd).wf(), at + n <= 26, n <= 11,
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, 0 <= r < p2(n as nat),
        (r as int, final(bd).view()) == extra(old(bd).buf@, old(bd).view(), at as int, n as nat, 0),
{
    let ghost buf = bd.buf@;
    let ghost s0 = bd.view();
    let mut v: i32 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            bd.wf(), bd.buf@ == buf, i <= n, n <= 11, at + n <= 26, 0 <= v < p2(i as nat),
            extra(buf, bd.view(), (at + i) as int, (n - i) as nat, v as int) == extra(buf, s0, at as int, n as nat, 0),
        decreases n - i,
    {
        proof { lemma_p2_11(i as nat); }
        let b = bd.get(aget(&CAT_PROBS, at + i));
        v = 2 * v + if b { 1 } else { 0 };
        i = i + 1;
    }
    v
}

proof fn lemma_p2_11(n: nat)
    requires n <= 11,
    ensures p2(n) <= 2048,
{
    reveal_with_fuel(p2, 12);
}

/// `big_value`.
#[inline(always)]
fn big_value_x(bd: &mut Bd, probs: &Vec<u8>, pb: usize) -> (r: i32)
    requires old(bd).wf(), pb + 11 <= probs@.len(), probs@.len() == 1056,
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, 2 <= r <= 2114,
        (r as int, final(bd).view()) == big_value(old(bd).buf@, old(bd).view(), probs@, pb as int),
{
    if !bd.get(get(probs.as_slice(), pb + 3)) {
        if !bd.get(get(probs.as_slice(), pb + 4)) { 2 } else if bd.get(get(probs.as_slice(), pb + 5)) { 4 } else { 3 }
    } else {
        let cat: usize = if !bd.get(get(probs.as_slice(), pb + 6)) {
            if bd.get(get(probs.as_slice(), pb + 7)) { 1 } else { 0 }
        } else if !bd.get(get(probs.as_slice(), pb + 8)) {
            if bd.get(get(probs.as_slice(), pb + 9)) { 3 } else { 2 }
        } else {
            if bd.get(get(probs.as_slice(), pb + 10)) { 5 } else { 4 }
        };
        let e = extra_x(bd, aget(&CAT_AT, cat) as usize, aget(&CAT_LEN, cat) as usize);
        proof { lemma_p2_11(CAT_LEN@[cat as int] as nat); reveal_with_fuel(p2, 12); }
        aget(&CAT_BASE, cat) as i32 + e
    }
}

/// Block `i` of a macroblock's coefficients (16 of the 400).
pub open spec fn blk(c: Seq<i32>, i: int) -> Seq<int> { Seq::new(16, |j: int| c[16 * i + j] as int) }

/// All 25 blocks.
pub open spec fn blocks(c: Seq<i32>) -> Seq<Seq<int>> { Seq::new(25, |i: int| blk(c, i)) }

/// Coefficients in 16 bits.
pub open spec fn c16(c: Seq<i32>) -> bool { forall|k: int| 0 <= k < c.len() ==> -32768 <= #[trigger] c[k] <= 32767 }

/// BANDS[c] * 33: a band's first probability, from a type's.
pub const BANDS33: [u16; 16] = [0, 33, 66, 99, 198, 132, 165, 198, 198, 198, 198, 198, 198, 198, 198, 231];

proof fn lemma_bands33(c: int)
    requires 0 <= c < 16,
    ensures BANDS33@[c] as int == BANDS@[c] as int * 33,
{
    assert(BANDS33@ =~= seq![0u16, 33, 66, 99, 198, 132, 165, 198, 198, 198, 198, 198, 198, 198, 198, 231]);
    assert(BANDS@ =~= seq![0u8, 1, 2, 3, 6, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 7]);
}

/// One block's tokens (`tokens`, from `first` with an end of block
/// allowed), into block `i` of `co`, which starts as zeros.
fn block_x(bd: &mut Bd, probs: &Vec<u8>, ty: usize, first: usize, ctx: usize, dqf: (i32, i32), co: &mut [i32; 400], i: usize)
    -> (c_end: usize)
    requires
        old(bd).wf(), probs@.len() == 1056, ty <= 3, first <= 1, ctx <= 2, i < 25,
        0 <= dqf.0 <= 512, 0 <= dqf.1 <= 512, c16(old(co)@),
        blk(old(co)@, i as int) == zeros16(),
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, c16(final(co)@), c_end <= 15,
        forall|j: int| 0 <= j < 25 && j != i ==> blk(final(co)@, j) == blk(old(co)@, j),
        ({
            let (out, c, s) = tokens(old(bd).buf@, old(bd).view(), probs@, ty as int, first as int, ctx as int, true,
                                     (dqf.0 as int, dqf.1 as int), zeros16());
            &&& blk(final(co)@, i as int) == out && c_end as int == c && final(bd).view() == s
        }),
{
    block_body(bd, probs, ty, first, ctx, dqf, co, i)
}

/// `block_x`, compiled with BMI2 and LZCNT (single-uop variable shifts,
/// leading zeros), as libwebp picks its kernels at run time.
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "bmi2,lzcnt")]
fn block_x_bmi(bd: &mut Bd, probs: &Vec<u8>, ty: usize, first: usize, ctx: usize, dqf: (i32, i32), co: &mut [i32; 400], i: usize)
    -> (c_end: usize)
    requires
        old(bd).wf(), probs@.len() == 1056, ty <= 3, first <= 1, ctx <= 2, i < 25,
        0 <= dqf.0 <= 512, 0 <= dqf.1 <= 512, c16(old(co)@),
        blk(old(co)@, i as int) == zeros16(),
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, c16(final(co)@), c_end <= 15,
        forall|j: int| 0 <= j < 25 && j != i ==> blk(final(co)@, j) == blk(old(co)@, j),
        ({
            let (out, c, s) = tokens(old(bd).buf@, old(bd).view(), probs@, ty as int, first as int, ctx as int, true,
                                     (dqf.0 as int, dqf.1 as int), zeros16());
            &&& blk(final(co)@, i as int) == out && c_end as int == c && final(bd).view() == s
        }),
{
    block_body(bd, probs, ty, first, ctx, dqf, co, i)
}

/// Calls `block_x_bmi`. Trusted: it is reached only from
/// `mb_tokens_x::<true>`, which only `tokens_step` calls, and only on a
/// CPU with BMI2 and LZCNT.
#[cfg(target_arch = "x86_64")]
#[verifier::external_body]
#[inline(always)]
fn block_x_fast(bd: &mut Bd, probs: &Vec<u8>, ty: usize, first: usize, ctx: usize, dqf: (i32, i32), co: &mut [i32; 400], i: usize)
    -> (c_end: usize)
    requires
        old(bd).wf(), probs@.len() == 1056, ty <= 3, first <= 1, ctx <= 2, i < 25,
        0 <= dqf.0 <= 512, 0 <= dqf.1 <= 512, c16(old(co)@),
        blk(old(co)@, i as int) == zeros16(),
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, c16(final(co)@), c_end <= 15,
        forall|j: int| 0 <= j < 25 && j != i ==> blk(final(co)@, j) == blk(old(co)@, j),
        ({
            let (out, c, s) = tokens(old(bd).buf@, old(bd).view(), probs@, ty as int, first as int, ctx as int, true,
                                     (dqf.0 as int, dqf.1 as int), zeros16());
            &&& blk(final(co)@, i as int) == out && c_end as int == c && final(bd).view() == s
        }),
{
    // Sound: see above.
    unsafe { block_x_bmi(bd, probs, ty, first, ctx, dqf, co, i) }
}

#[inline(always)]
fn block_body(bd: &mut Bd, probs: &Vec<u8>, ty: usize, first: usize, ctx: usize, dqf: (i32, i32), co: &mut [i32; 400], i: usize)
    -> (c_end: usize)
    requires
        old(bd).wf(), probs@.len() == 1056, ty <= 3, first <= 1, ctx <= 2, i < 25,
        0 <= dqf.0 <= 512, 0 <= dqf.1 <= 512, c16(old(co)@),
        blk(old(co)@, i as int) == zeros16(),
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, c16(final(co)@), c_end <= 15,
        forall|j: int| 0 <= j < 25 && j != i ==> blk(final(co)@, j) == blk(old(co)@, j),
        ({
            let (out, c, s) = tokens(old(bd).buf@, old(bd).view(), probs@, ty as int, first as int, ctx as int, true,
                                     (dqf.0 as int, dqf.1 as int), zeros16());
            &&& blk(final(co)@, i as int) == out && c_end as int == c && final(bd).view() == s
        }),
{
    let ghost buf = bd.buf@;
    let ghost s0 = bd.view();
    let ghost co0 = co@;
    let ghost dq = (dqf.0 as int, dqf.1 as int);
    let mut c: usize = first;
    let mut cx: usize = ctx;
    let tyb = ty * 264;
    let ghost t0 = tokens(buf, s0, probs@, ty as int, first as int, ctx as int, true, dq, zeros16());
    proof { lemma_bands33(c as int); }
    let mut pb = tyb + aget(&BANDS33, c) as usize + cx * 11;
    // As libwebp's GetCoeffsFast: an end of block may come here; then a
    // run of zeros, each with no end of block after it; then a value.
    loop
        invariant
            tyb == ty * 264,
            bd.wf(), bd.buf@ == buf, buf == old(bd).buf@, s0 == old(bd).view(), co0 == old(co)@,
            probs@.len() == 1056, ty <= 3, c <= 15, cx <= 2, i < 25, pb as int == pbase(ty as int, c as int, cx as int),
            0 <= dqf.0 <= 512, 0 <= dqf.1 <= 512, dq == (dqf.0 as int, dqf.1 as int), c16(co@),
            forall|j: int| 0 <= j < 25 && j != i ==> blk(co@, j) == blk(co0, j),
            t0 == tokens(buf, s0, probs@, ty as int, first as int, ctx as int, true, dq, zeros16()),
            tokens(buf, bd.view(), probs@, ty as int, c as int, cx as int, true, dq, blk(co@, i as int)) == t0,
        decreases 16 - c,
    {
        if !bd.get(get(probs.as_slice(), pb)) {
            return c;
        }
        let ghost mut sz = bd.view();
        let ghost c_in = c;
        loop
            invariant_except_break
                sz == bd.view(),
            invariant
                tyb == ty * 264,
                bd.wf(), bd.buf@ == buf, buf == old(bd).buf@, s0 == old(bd).view(), co0 == old(co)@,
                probs@.len() == 1056, ty <= 3, c_in <= c <= 15, cx <= 2, i < 25,
                pb as int == pbase(ty as int, c as int, cx as int),
                0 <= dqf.0 <= 512, 0 <= dqf.1 <= 512, dq == (dqf.0 as int, dqf.1 as int), c16(co@),
                forall|j: int| 0 <= j < 25 && j != i ==> blk(co@, j) == blk(co0, j),
                t0 == tokens(buf, s0, probs@, ty as int, first as int, ctx as int, true, dq, zeros16()),
                tokens(buf, sz, probs@, ty as int, c as int, cx as int, false, dq, blk(co@, i as int)) == t0,
            ensures
                pb as int == pbase(ty as int, c as int, cx as int), c_in <= c <= 15, cx <= 2,
                b_get(buf, sz, probs@[pb as int + 1]) == (true, bd.view()),
            decreases 16 - c,
        {
            let ghost s1 = bd.view();
            if bd.get(get(probs.as_slice(), pb + 1)) {
                break;
            }
            if c == 15 {
                return 15;
            }
            c = c + 1;
            cx = 0;
            proof { lemma_bands33(c as int); sz = bd.view(); }
            pb = tyb + aget(&BANDS33, c) as usize;
        }
        let ghost sa = bd.view();
        let one = bd.get(get(probs.as_slice(), pb + 2));
        let v: i32 = if !one { 1 } else { big_value_x(bd, probs, pb) };
        let f = if c > 0 { dqf.1 } else { dqf.0 };
        proof {
            assert(v * f <= 2114 * 512 && v * f >= 0) by (nonlinear_arith) requires 1 <= v <= 2114, 0 <= f <= 512;
        }
        let p = v * f;
        let ghost sb0 = bd.view();
        let sp = bd.signed(p);
        let ghost neg = b_bit(buf, sb0).0;
        let val = wrap16_x(sp);
        let z = aget(&ZIGZAG, c) as usize;
        let ghost before = co@;
        aset(co, 16 * i + z, val);
        proof {
            assert(-(p as int) == (-(v as int)) * (f as int)) by (nonlinear_arith) requires p == v * f;
            assert(blk(co@, i as int) =~= blk(before, i as int).update(z as int, val as int));
            assert forall|j: int| 0 <= j < 25 && j != i implies blk(co@, j) == blk(co0, j) by {
                assert(blk(co@, j) =~= blk(before, j));
            }
        }
        if c == 15 {
            return 15;
        }
        c = c + 1;
        cx = if v == 1 { 1 } else { 2 };
        proof { lemma_bands33(c as int); }
        pb = tyb + aget(&BANDS33, c) as usize + cx * 11;
    }
}

/// A macroblock's token contexts and coefficients (`TokState`, without
/// the reader).
pub open spec fn tview(s: BState, left: Seq<i32>, above: Seq<i32>, co: Seq<i32>, nz: bool) -> TokState {
    TokState { s, left: ints(left), above: ints(above), coeffs: blocks(co), nonzero: nz }
}

pub open spec fn ctx01(c: Seq<i32>) -> bool { forall|k: int| 0 <= k < c.len() ==> 0 <= #[trigger] c[k] <= 1 }

/// `block_at`.
fn block_at_x(bpred: bool, k: usize) -> (r: (usize, usize))
    requires k < 25,
    ensures (r.0 as int, r.1 as int) == block_at(bpred, k as int), r.0 < 25, r.1 <= 3,
{
    if bpred {
        if k < 16 { (k, 3) } else { (k, 2) }
    } else {
        if k == 0 { (24, 1) } else if k <= 16 { (k - 1, 0) } else { (k - 1, 2) }
    }
}

/// Block `i`'s AC coefficients (1..16) are 0: a DC alone.
pub open spec fn acz(co: Seq<i32>, i: int) -> bool { forall|k: int| 1 <= k < 16 ==> #[trigger] co[16 * i + k] == 0 }

/// Bit `i` of `m`.
pub open spec fn bit(m: u32, i: int) -> bool { (m >> (i as u32)) & 1u32 == 1u32 }

/// ZIGZAG's inverse.
pub const ZZINV: [u8; 16] = [0, 1, 5, 6, 2, 4, 7, 12, 3, 8, 11, 13, 9, 10, 14, 15];

proof fn lemma_zz()
    ensures
        forall|i: int, j: int| 0 <= i < 16 && 0 <= j < 16 && i != j ==> #[trigger] ZIGZAG@[i] != #[trigger] ZIGZAG@[j],
        forall|p: int| 0 <= p < 16 ==> #[trigger] ZZINV@[p] < 16 && ZIGZAG@[ZZINV@[p] as int] as int == p && (p >= 1 ==> ZZINV@[p] >= 1),
        forall|i: int| 0 <= i < 16 ==> #[trigger] ZIGZAG@[i] < 16,
{
    assert(ZIGZAG@ =~= seq![0u8, 1, 4, 8, 5, 2, 3, 6, 9, 12, 13, 10, 7, 11, 14, 15]);
    assert(ZZINV@ =~= seq![0u8, 1, 5, 6, 2, 4, 7, 12, 3, 8, 11, 13, 9, 10, 14, 15]);
}

/// `tokens` writes nothing at the zigzag positions from where it ends
/// (below 15, where it ended at an end of block) on.
proof fn lemma_tokens_tail(buf: Seq<u8>, s: BState, probs: Seq<u8>, ty: int, c: int, ctx: int, eob: bool,
    dqf: (int, int), out: Seq<int>)
    requires 0 <= c <= 15, out.len() == 16,
    ensures ({
        let (o2, c2, s2) = tokens(buf, s, probs, ty, c, ctx, eob, dqf, out);
        &&& c <= c2 <= 15 && o2.len() == 16
        &&& c2 < 15 ==> forall|k: int| c2 <= k < 16 ==> #[trigger] o2[ZIGZAG@[k] as int] == out[ZIGZAG@[k] as int]
    }),
    decreases 16 - c, if eob { 1int } else { 0 },
{
    lemma_zz();
    let pb = pbase(ty, c, ctx);
    if eob {
        let (more, s1) = b_get(buf, s, probs[pb]);
        if more { lemma_tokens_tail(buf, s1, probs, ty, c, ctx, false, dqf, out); }
    } else {
        let (nz, s1) = b_get(buf, s, probs[pb + 1]);
        if !nz {
            if c < 15 { lemma_tokens_tail(buf, s1, probs, ty, c + 1, 0, false, dqf, out); }
        } else {
            let (one, s2) = b_get(buf, s1, probs[pb + 2]);
            let (v, s3) = if !one { (1int, s2) } else { big_value(buf, s2, probs, pb) };
            let (neg, s4) = b_bit(buf, s3);
            let f = if c > 0 { dqf.1 } else { dqf.0 };
            let out2 = out.update(ZIGZAG@[c] as int, wrap16((if neg { -v } else { v }) * f));
            if c < 15 {
                lemma_tokens_tail(buf, s4, probs, ty, c + 1, if v == 1 { 1 } else { 2 }, true, dqf, out2);
                let (o2, c2, _) = tokens(buf, s4, probs, ty, c + 1, if v == 1 { 1 } else { 2 }, true, dqf, out2);
                assert forall|k: int| c2 <= k < 16 && c2 < 15 implies #[trigger] o2[ZIGZAG@[k] as int] == out[ZIGZAG@[k] as int] by {
                    assert(ZIGZAG@[k] != ZIGZAG@[c]);
                }
            }
        }
    }
}

/// A macroblock's tokens (`mb_tokens`), into `co` (zeros on entry),
/// updating the contexts; returns dixie's eob_mask != 0.
#[inline(always)]
pub fn mb_tokens_x<const BMI: bool>(bd: &mut Bd, probs: &Vec<u8>, f: &FacX, mb: &MbX, left: &mut [i32; 9], above: &mut [i32; 9], co: &mut [i32; 400])
    -> (r: (bool, u32))
    requires
        old(bd).wf(), probs@.len() == 1056, f.wf(), mb.wf(), ctx01(old(left)@), ctx01(old(above)@),
        old(co)@ == Seq::new(400, |k: int| 0i32),
    ensures
        final(bd).wf(), final(bd).buf@ == old(bd).buf@, ctx01(final(left)@), ctx01(final(above)@), c16(final(co)@),
        tview(final(bd).view(), final(left)@, final(above)@, final(co)@, r.0)
            == mb_tokens(old(bd).buf@, probs@, f.view(), mb.view(), old(bd).view(), ints(old(left)@), ints(old(above)@)),
        // The blocks whose bit is set are a DC alone, as the tokens' ends show.
        forall|j: int| 0 <= j < 25 && #[trigger] bit(r.1, j) ==> acz(final(co)@, j),
{
    proof { reveal(mb_tokens); }
    let ghost buf = bd.buf@;
    let ghost s0 = bd.view();
    let ghost l0 = ints(left@);
    let ghost a0 = ints(above@);
    let bpred = mb.y_mode == 4;
    proof {
        assert(blocks(co@) =~= Seq::new(25, |i: int| zeros16())) by {
            assert forall|i: int| 0 <= i < 25 implies #[trigger] blocks(co@)[i] == zeros16() by {
                assert(blk(co@, i) =~= zeros16());
            }
        }
    }
    if mb.skip {
        left[0] = 0; left[1] = 0; left[2] = 0; left[3] = 0; left[4] = 0; left[5] = 0; left[6] = 0; left[7] = 0;
        above[0] = 0; above[1] = 0; above[2] = 0; above[3] = 0; above[4] = 0; above[5] = 0; above[6] = 0; above[7] = 0;
        if !bpred {
            left[8] = 0;
            above[8] = 0;
        }
        proof {
            assert(ints(left@) =~= Seq::new(9, |k: int| if k == 8 && bpred { l0[8] } else { 0int }));
            assert(ints(above@) =~= Seq::new(9, |k: int| if k == 8 && bpred { a0[8] } else { 0int }));
            assert forall|j: int| 0 <= j < 25 && #[trigger] bit(0x1ff_ffffu32, j) implies acz(co@, j) by {
                assert forall|kk: int| 1 <= kk < 16 implies #[trigger] co@[16 * j + kk] == 0 by {}
            }
        }
        return (false, 0x1ff_ffff);
    }
    let n: usize = if bpred { 24 } else { 25 };
    let mut nz = false;
    // Every block is 0 so far: a DC alone.
    let mut dcx: u32 = 0x1ff_ffff;
    let mut k: usize = 0;
    let ghost fv = f.view();
    proof {
        assert(tview(bd.view(), left@, above@, co@, nz) == TokState { s: s0, left: l0, above: a0, coeffs: Seq::new(25, |i: int| zeros16()), nonzero: false });
        assert forall|m: int| 0 <= m < n implies blk(co@, (#[trigger] block_at(bpred, m)).0) == zeros16() by {
            assert(blocks(co@)[block_at(bpred, m).0] == blk(co@, block_at(bpred, m).0));
        }
    }
    while k < n
        invariant
            bd.wf(), bd.buf@ == buf, probs@.len() == 1056, f.wf(), fv == f.view(), k <= n, n as int == nblocks(bpred),
            ctx01(left@), ctx01(above@), c16(co@),
            forall|j: int| 0 <= j < 25 && #[trigger] bit(dcx, j) ==> acz(co@, j),
            forall|m: int| k <= m < n ==> blk(co@, (#[trigger] block_at(bpred, m)).0) == zeros16(),
            mb_blocks(buf, probs@, fv, bpred, k as int, tview(bd.view(), left@, above@, co@, nz))
                == mb_blocks(buf, probs@, fv, bpred, 0, TokState { s: s0, left: l0, above: a0, coeffs: Seq::new(25, |i: int| zeros16()), nonzero: false }),
        decreases n - k,
    {
        let (i, ty) = block_at_x(bpred, k);
        let li = aget(&LEFT_CTX, i) as usize;
        let ai = aget(&ABOVE_CTX, i) as usize;
        let ctx = (aget(left, li) + aget(above, ai)) as usize;
        let first: usize = if ty == 0 { 1 } else { 0 };
        let dq = if ty == 1 { f.y2 } else if ty == 2 { f.uv } else { f.y1 };
        let ghost t0 = tview(bd.view(), left@, above@, co@, nz);
        let ghost sb = bd.view();
        let ghost cb = co@;
        proof { assert(block_at(bpred, k as int).0 == i); }
        #[cfg(target_arch = "x86_64")]
        let c = if BMI { block_x_fast(bd, probs, ty, first, ctx, dq, co, i) } else { block_x(bd, probs, ty, first, ctx, dq, co, i) };
        #[cfg(not(target_arch = "x86_64"))]
        let c = block_x(bd, probs, ty, first, ctx, dq, co, i);
        let dcx0 = dcx;
        proof { assert(forall|j: int| 0 <= j < 25 && #[trigger] bit(dcx0, j) ==> acz(cb, j)); }
        if c > 1 {
            dcx = dcx & !(1u32 << (i as u32));
        }
        proof {
            let i32_ = i as u32;
            assert forall|j: int| 0 <= j < 25 && #[trigger] bit(dcx, j) implies acz(co@, j) by {
                let j32 = j as u32;
                assert(c > 1 ==> (((dcx0 & !(1u32 << i32_)) >> j32) & 1u32 == 1u32) == ((dcx0 >> j32) & 1u32 == 1u32 && j32 != i32_))
                    by (bit_vector) requires i32_ < 25, j32 < 25;
                if j != i {
                    assert(bit(dcx0, j));
                    assert(acz(cb, j));
                    assert(blk(co@, j) == blk(cb, j));
                    assert forall|kk: int| 1 <= kk < 16 implies #[trigger] co@[16 * j + kk] == 0 by {
                        assert(blk(co@, j)[kk] == blk(cb, j)[kk]);
                        assert(cb[16 * j + kk] == 0);
                    }
                } else {
                    let dq_ = (dq.0 as int, dq.1 as int);
                    lemma_tokens_tail(buf, sb, probs@, ty as int, first as int, ctx as int, true, dq_, zeros16());
                    lemma_zz();
                    let (out, c2, _) = tokens(buf, sb, probs@, ty as int, first as int, ctx as int, true, dq_, zeros16());
                    assert(c2 == c && blk(co@, i as int) == out);
                    assert(c <= 1) by {
                        assert(c > 1 ==> (((dcx0 & !(1u32 << i32_)) >> i32_) & 1u32 == 1u32) == false) by (bit_vector) requires i32_ < 25;
                    }
                    assert forall|kk: int| 1 <= kk < 16 implies #[trigger] co@[16 * j + kk] == 0 by {
                        let q = ZZINV@[kk] as int;
                        assert(out[ZIGZAG@[q] as int] == zeros16()[ZIGZAG@[q] as int]);
                        assert(blk(co@, i as int)[kk] == co@[16 * i + kk] as int);
                    }
                }
            }
        }
        let t: i32 = if c != first { 1 } else { 0 };
        aset(left, li, t);
        aset(above, ai, t);
        nz = nz || c != first;
        proof {
            assert(blocks(co@) =~= t0.coeffs.update(i as int, blk(co@, i as int)));
            assert(ints(left@) =~= t0.left.update(LEFT_CTX@[i as int] as int, t as int));
            assert(ints(above@) =~= t0.above.update(ABOVE_CTX@[i as int] as int, t as int));
            assert forall|m: int| k + 1 <= m < n implies blk(co@, (#[trigger] block_at(bpred, m)).0) == zeros16() by {
                lemma_block_at_distinct(bpred, k as int, m);
            }
        }
        k = k + 1;
    }
    proof { assert(mb_blocks(buf, probs@, fv, bpred, n as int, tview(bd.view(), left@, above@, co@, nz)) == tview(bd.view(), left@, above@, co@, nz)); }
    (nz, dcx)
}

/// Different block indexes go to different blocks.
proof fn lemma_block_at_distinct(bpred: bool, m: int, k: int)
    requires 0 <= m < k < 25,
    ensures block_at(bpred, m).0 != block_at(bpred, k).0,
{
}

} // verus!
