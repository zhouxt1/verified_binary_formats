//! The meta-block header (RFC 7932 6, 7.3, 9.2): block counts, context
//! maps, categories and the header as a whole, each proved to compute its
//! spec function.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::{p2, lemma_p2_pos};
use vbits::lsb::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::getbits;
use crate::spec::*;
use crate::code::*;

verus! {

pub fn varlen8_x(buf: &[u8], p: usize) -> (r: Option<(u64, usize)>)
    requires buf_ok(buf@), p <= 8 * buf.len(),
    ensures
        match r {
            Some((v, q)) => varlen8(lbits(buf@), p as int) == Some((v as nat, q as int))
                && v <= 255 && q <= 8 * buf.len(),
            None => varlen8(lbits(buf@), p as int) is None,
        },
{
    let x = match getbits_x(buf, p, 1) { None => return None, Some(x) => x };
    if x == 0 {
        return Some((0, p + 1));
    }
    let n = match getbits_x(buf, p + 1, 3) { None => return None, Some(n) => n };
    if n == 0 {
        return Some((1, p + 4));
    }
    proof { reveal_with_fuel(p2, 8); }
    let e = match getbits_x(buf, p + 4, n) { None => return None, Some(e) => e };
    proof {
        vbits::prim_read::lemma_p2_eq_pow2(n as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(n as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, n);
        vbits::prim_read::lemma_p2_mono(n as nat, 7);
    }
    Some(((1u64 << n) + e, p + 4 + n as usize))
}

pub const BC_BASE: [u32; 26] = [1, 5, 9, 13, 17, 25, 33, 41, 49, 65, 81, 97, 113, 145, 177, 209, 241, 305, 369,
    497, 753, 1265, 2289, 4337, 8433, 16625];
pub const BC_EXTRA: [u8; 26] = [2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 7, 8, 9, 10, 11, 12, 13, 24];

pub proof fn lemma_bc()
    ensures forall|i: int| 0 <= i < 26 ==> (#[trigger] BC_BASE@[i]) as nat == bc_base()[i]
        && BC_EXTRA@[i] as nat == bc_extra()[i] && BC_BASE@[i] <= 16625 && BC_EXTRA@[i] <= 24,
{
    assert(forall|i: int| 0 <= i < 26 ==> (#[trigger] BC_BASE@[i]) as nat == bc_base()[i]
        && BC_EXTRA@[i] as nat == bc_extra()[i] && BC_BASE@[i] <= 16625 && BC_EXTRA@[i] <= 24) by (compute);
}

/// A block count: at least 1 and below 2^25.
#[inline(always)]
pub fn read_count_x(code: &Dec, buf: &[u8], p: usize) -> (r: Option<(u64, usize)>)
    requires dec_wf(code), buf_ok(buf@), p <= 8 * buf.len(),
    ensures
        match r {
            Some((v, q)) => read_count(code.lens@, lbits(buf@), p as int) == Some((v as nat, q as int))
                && 1 <= v < 0x200_0000 && p <= q <= 8 * buf.len(),
            None => read_count(code.lens@, lbits(buf@), p as int) is None,
        },
{
    let (s, q) = match dsym_x(code, buf, p) { None => return None, Some(x) => x };
    if s >= 26 {
        return None;
    }
    proof { lemma_bc(); }
    let nb = BC_EXTRA[s as usize] as u64;
    let e = match getbits_x(buf, q, nb) { None => return None, Some(e) => e };
    proof {
        vbits::prim_read::lemma_p2_mono(nb as nat, 24);
        assert(p2(24) == 0x100_0000) by { reveal_with_fuel(p2, 25); }
    }
    Some((BC_BASE[s as usize] as u64 + e, q + nb as usize))
}

/// A context map or mode list as the spec's `nat`s.
pub open spec fn unat(v: Seq<u8>) -> Seq<nat> { v.map_values(|x: u8| x as nat) }

proof fn lemma_unat_push(v: Seq<u8>, x: u8)
    ensures unat(v.push(x)) == unat(v).push(x as nat),
{
    assert(unat(v.push(x)) =~= unat(v).push(x as nat));
}

fn read_cmap_vals_x(code: &Dec, rlemax: u64, buf: &[u8], pos: usize, size: usize, ntrees: u64)
    -> (r: Option<(Vec<u8>, usize)>)
    requires
        dec_wf(code), code.lens@.len() == ntrees + rlemax, rlemax <= 16, 2 <= ntrees <= 256,
        buf_ok(buf@), pos <= 8 * buf.len(), size <= 16384,
    ensures
        match r {
            Some((v, q)) => read_cmap_vals(code.lens@, rlemax as nat, lbits(buf@), pos as int, size as nat,
                                           Seq::empty()) == Some((unat(v@), q as int))
                && q <= 8 * buf.len() && v@.len() == size
                && forall|i: int| 0 <= i < v@.len() ==> (#[trigger] v@[i]) < ntrees,
            None => read_cmap_vals(code.lens@, rlemax as nat, lbits(buf@), pos as int, size as nat,
                                   Seq::empty()) is None,
        },
{
    let ghost b = lbits(buf@);
    let ghost target = read_cmap_vals(code.lens@, rlemax as nat, b, pos as int, size as nat, Seq::empty());
    let mut acc: Vec<u8> = Vec::with_capacity(size);
    let mut p = pos;
    proof { assert(unat(acc@) =~= Seq::<nat>::empty()); }
    while acc.len() < size
        invariant
            dec_wf(code), code.lens@.len() == ntrees + rlemax, rlemax <= 16, 2 <= ntrees <= 256,
            buf_ok(buf@), p <= 8 * buf.len(), b == lbits(buf@), size <= 16384, acc@.len() <= size,
            forall|i: int| 0 <= i < acc@.len() ==> (#[trigger] acc@[i]) < ntrees,
            read_cmap_vals(code.lens@, rlemax as nat, b, p as int, size as nat, unat(acc@)) == target,
            target == read_cmap_vals(code.lens@, rlemax as nat, lbits(buf@), pos as int, size as nat, Seq::empty()),
        decreases size - acc@.len(),
    {
        let (s, q) = match dsym_x(code, buf, p) { None => return None, Some(x) => x };
        let s = s as u64;
        if s == 0 {
            proof { lemma_unat_push(acc@, 0); }
            acc.push(0);
            p = q;
        } else if s <= rlemax {
            let e = match getbits_x(buf, q, s) { None => return None, Some(e) => e };
            proof {
                vbits::prim_read::lemma_p2_eq_pow2(s as nat);
                vstd::bits::lemma_u64_pow2_no_overflow(s as nat);
                vstd::bits::lemma_u64_shl_is_mul(1u64, s);
                vbits::prim_read::lemma_p2_mono(s as nat, 16);
                assert(p2(16) == 0x1_0000) by { reveal_with_fuel(p2, 17); }
            }
            let run: u64 = (1u64 << s) + e;
            if acc.len() as u64 + run > size as u64 {
                return None;
            }
            let ghost a0 = acc@;
            let mut j: u64 = 0;
            while j < run
                invariant
                    j <= run, a0.len() + run <= size, acc@ =~= a0 + Seq::new(j as nat, |_i: int| 0u8),
                decreases run - j,
            {
                acc.push(0);
                j = j + 1;
            }
            proof {
                assert(unat(acc@) =~= unat(a0) + Seq::new(run as nat, |_i: int| 0nat));
                assert forall|i: int| 0 <= i < acc@.len() implies (#[trigger] acc@[i]) < ntrees by {
                    if i < a0.len() { assert(acc@[i] == a0[i]); }
                }
            }
            p = q + s as usize;
        } else {
            proof { lemma_unat_push(acc@, (s - rlemax) as u8); }
            acc.push((s - rlemax) as u8);
            p = q;
        }
    }
    Some((acc, p))
}

/// The inverse move-to-front transform of 7.3, in place.
fn imtf_x(v: &mut Vec<u8>)
    ensures
        unat(final(v)@) == imtf(unat(old(v)@), Seq::new(256, |i: int| i as nat)),
        final(v)@.len() == old(v)@.len(),
{
    let ghost v0 = unat(old(v)@);
    let mut mtf = [0u8; 256];
    let mut k: usize = 0;
    while k < 256
        invariant k <= 256, forall|i: int| 0 <= i < k ==> #[trigger] mtf@[i] as int == i,
        decreases 256 - k,
    {
        mtf[k] = k as u8;
        k = k + 1;
    }
    proof {
        assert(unat(mtf@) =~= Seq::new(256, |i: int| i as nat));
        assert(v0.skip(0) =~= v0);
        assert(unat(v@).take(0) =~= Seq::<nat>::empty());
        assert(unat(v@).take(0) + imtf(v0.skip(0), unat(mtf@)) =~= imtf(v0.skip(0), unat(mtf@)));
    }
    let n = v.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == v@.len(), i <= n, mtf@.len() == 256, v0.len() == n,
            forall|j: int| i <= j < n ==> (#[trigger] v@[j]) as nat == v0[j],
            unat(v@).take(i as int) + imtf(v0.skip(i as int), unat(mtf@)) == imtf(v0, Seq::new(256, |j: int| j as nat)),
        decreases n - i,
    {
        let idx = v[i] as usize;
        let val = mtf[idx];
        let ghost m0 = mtf@;
        let mut j = idx;
        while j > 0
            invariant
                j <= idx, idx < 256, mtf@.len() == 256, m0.len() == 256,
                forall|t: int| 0 <= t <= j ==> #[trigger] mtf@[t] == m0[t],
                forall|t: int| j < t <= idx ==> #[trigger] mtf@[t] == m0[t - 1],
                forall|t: int| idx < t < 256 ==> #[trigger] mtf@[t] == m0[t],
            decreases j,
        {
            mtf[j] = mtf[j - 1];
            j = j - 1;
        }
        mtf[0] = val;
        proof {
            assert(unat(mtf@) =~= mtf_step(unat(m0), idx as nat)) by {
                assert forall|t: int| 0 <= t < 256 implies #[trigger] unat(mtf@)[t] == mtf_step(unat(m0), idx as nat)[t] by {
                    if t == 0 {} else if t <= idx { assert(mtf@[t] == m0[t - 1]); } else { assert(mtf@[t] == m0[t]); }
                }
            }
            let s = v0.skip(i as int);
            assert(s[0] == idx as nat);
            assert(s.skip(1) =~= v0.skip(i + 1));
            assert(imtf(s, unat(m0)) == seq![unat(m0)[idx as int]] + imtf(s.skip(1), mtf_step(unat(m0), idx as nat)));
        }
        let ghost vb = unat(v@);
        v.set(i, val);
        proof {
            assert(unat(v@).take(i + 1) =~= vb.take(i as int).push(val as nat));
            assert(unat(v@).take(i + 1) + imtf(v0.skip(i + 1), unat(mtf@))
                =~= vb.take(i as int) + (seq![val as nat] + imtf(v0.skip(i + 1), unat(mtf@))));
        }
        i = i + 1;
    }
    proof {
        assert(v0.skip(n as int) =~= Seq::<nat>::empty());
        assert(unat(v@).take(n as int) =~= unat(v@));
        assert(unat(v@).take(n as int) + imtf(v0.skip(n as int), unat(mtf@)) =~= unat(v@).take(n as int));
    }
}

/// Every value is below `ntrees`.
fn below_x(v: &Vec<u8>, ntrees: u64) -> (r: bool)
    ensures r == cmap_below(unat(v@), ntrees as nat),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), forall|j: int| 0 <= j < i ==> (#[trigger] v@[j]) < ntrees,
        decreases v@.len() - i,
    {
        if v[i] as u64 >= ntrees {
            proof { assert(unat(v@)[i as int] >= ntrees); }
            return false;
        }
        i = i + 1;
    }
    true
}

/// NTREES and a context map of `size` entries.
pub fn read_cmap_x(buf: &[u8], p: usize, size: usize) -> (r: Option<(Vec<u8>, u64, usize)>)
    requires buf_ok(buf@), p <= 8 * buf.len(), 1 <= size <= 16384,
    ensures
        match r {
            Some((v, nt, q)) => read_cmap(lbits(buf@), p as int, size as nat) == Some((unat(v@), nt as nat, q as int))
                && q <= 8 * buf.len() && v@.len() == size && 1 <= nt <= 256
                && forall|i: int| 0 <= i < v@.len() ==> (#[trigger] v@[i]) < nt,
            None => read_cmap(lbits(buf@), p as int, size as nat) is None,
        },
{
    let (t, q) = match varlen8_x(buf, p) { None => return None, Some(x) => x };
    if t == 0 {
        let v = zeros(size);
        proof { assert(unat(v@) =~= Seq::new(size as nat, |_i: int| 0nat)); }
        return Some((v, 1, q));
    }
    let ntrees = t + 1;
    let x = match getbits_x(buf, q, 1) { None => return None, Some(x) => x };
    let (rlemax, q2) = if x == 0 {
        (0u64, q + 1)
    } else {
        match getbits_x(buf, q + 1, 4) {
            None => return None,
            Some(r) => {
                proof { reveal_with_fuel(p2, 5); }
                (r + 1, q + 5)
            }
        }
    };
    let (code, q3) = match read_dec(buf, q2, ntrees + rlemax) { None => return None, Some(x) => x };
    let (mut v, q4) = match read_cmap_vals_x(&code, rlemax, buf, q3, size, ntrees) {
        None => return None,
        Some(x) => x,
    };
    let x2 = match getbits_x(buf, q4, 1) { None => return None, Some(x) => x };
    if x2 == 1 {
        imtf_x(&mut v);
    }
    if !below_x(&v, ntrees) {
        return None;
    }
    proof {
        assert forall|i: int| 0 <= i < v@.len() implies (#[trigger] v@[i]) < ntrees by {
            assert(unat(v@)[i] < ntrees);
        }
    }
    Some((v, ntrees, q4 + 1))
}

// ------------------------------------------------------------ categories

/// A category's header, ready to decode with.
pub struct XCat {
    pub n: u64,
    /// The block type and count codes: none for one block type (never read).
    pub codes: Option<(Dec, Dec)>,
    pub first: u64,
}

/// With two or more block types, the codes (opaque: revealed where they
/// are built and read).
#[verifier::opaque]
pub open spec fn codes_ok(codes: Option<(Dec, Dec)>, c: Cat, n: u64) -> bool {
    n >= 2 ==> {
        &&& codes is Some
        &&& dec_wf(&codes.unwrap().0) && codes.unwrap().0.lens@ == c.tcode
        &&& dec_wf(&codes.unwrap().1) && codes.unwrap().1.lens@ == c.ccode
        &&& c.tcode.len() == n + 2 && c.ccode.len() == 26
    }
}

pub open spec fn xcat_wf(x: &XCat, c: Cat) -> bool {
    &&& x.n as nat == c.n && 1 <= x.n <= 256
    &&& x.first as nat == c.first && 1 <= x.first < 0x200_0000
    &&& codes_ok(x.codes, c, x.n)
}

pub fn read_cat_x(buf: &[u8], p: usize) -> (r: Option<(XCat, usize)>)
    requires buf_ok(buf@), p <= 8 * buf.len(),
    ensures
        match r {
            Some((x, q)) => read_cat(lbits(buf@), p as int) matches Some((c, q2))
                && q2 == q as int && xcat_wf(&x, c) && q <= 8 * buf.len(),
            None => read_cat(lbits(buf@), p as int) is None,
        },
{
    let (v, q) = match varlen8_x(buf, p) { None => return None, Some(x) => x };
    if v == 0 {
        proof { assert(p2(24) == 0x100_0000) by { reveal_with_fuel(p2, 25); } reveal(codes_ok); }
        return Some((XCat { n: 1, codes: None, first: 0x100_0000 }, q));
    }
    let (tcode, q2) = match read_dec(buf, q, v + 3) { None => return None, Some(x) => x };
    let (ccode, q3) = match read_dec(buf, q2, 26) { None => return None, Some(x) => x };
    let (first, q4) = match read_count_x(&ccode, buf, q3) { None => return None, Some(x) => x };
    proof { reveal(codes_ok); }
    Some((XCat { n: v + 1, codes: Some((tcode, ccode)), first }, q4))
}

// ----------------------------------------------------------- the header

fn read_modes_x(buf: &[u8], pos: usize, n: u64) -> (r: Option<(Vec<u8>, usize)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), n <= 256,
    ensures
        match r {
            Some((v, q)) => read_modes(lbits(buf@), pos as int, n as nat, Seq::empty()) == Some((unat(v@), q as int))
                && q <= 8 * buf.len() && v@.len() == n && forall|i: int| 0 <= i < v@.len() ==> (#[trigger] v@[i]) < 4,
            None => read_modes(lbits(buf@), pos as int, n as nat, Seq::empty()) is None,
        },
{
    let ghost b = lbits(buf@);
    let ghost target = read_modes(b, pos as int, n as nat, Seq::empty());
    let mut v: Vec<u8> = Vec::new();
    let mut p = pos;
    proof { assert(unat(v@) =~= Seq::<nat>::empty()); reveal_with_fuel(p2, 3); }
    while (v.len() as u64) < n
        invariant
            buf_ok(buf@), p <= 8 * buf.len(), b == lbits(buf@), v@.len() <= n, n <= 256, p2(2) == 4,
            forall|i: int| 0 <= i < v@.len() ==> (#[trigger] v@[i]) < 4,
            read_modes(b, p as int, n as nat, unat(v@)) == target,
            target == read_modes(lbits(buf@), pos as int, n as nat, Seq::empty()),
        decreases n - v@.len(),
    {
        let m = match getbits_x(buf, p, 2) { None => return None, Some(m) => m };
        proof { lemma_unat_push(v@, m as u8); }
        v.push(m as u8);
        p = p + 2;
    }
    Some((v, p))
}

/// The lengths of a list of codes.
pub open spec fn lens_of(v: Seq<Dec>) -> Seq<Seq<u8>> { v.map_values(|d: Dec| d.lens@) }

/// Codes ready to decode with, over an alphabet of `asize`, with lengths `lens`.
pub open spec fn decs_wf(v: Seq<Dec>, lens: Seq<Seq<u8>>, asize: nat) -> bool {
    &&& v.len() == lens.len()
    &&& forall|i: int| #![trigger v[i]] 0 <= i < v.len() ==> dec_wf(&v[i]) && v[i].lens@ == lens[i]
                                             && v[i].lens@.len() == asize
}

fn read_codes_x(buf: &[u8], pos: usize, asize: u64, n: u64) -> (r: Option<(Vec<Dec>, usize)>)
    requires buf_ok(buf@), pos <= 8 * buf.len(), 2 <= asize <= 1024, n <= 256,
    ensures
        match r {
            Some((v, q)) => read_codes(lbits(buf@), pos as int, asize as nat, n as nat, Seq::empty())
                    matches Some((l, q2)) && q2 == q as int && decs_wf(v@, l, asize as nat)
                && q <= 8 * buf.len() && v@.len() == n,
            None => read_codes(lbits(buf@), pos as int, asize as nat, n as nat, Seq::empty()) is None,
        },
{
    let ghost b = lbits(buf@);
    let ghost target = read_codes(b, pos as int, asize as nat, n as nat, Seq::empty());
    let mut v: Vec<Dec> = Vec::with_capacity(n as usize);
    let mut p = pos;
    proof { assert(lens_of(v@) =~= Seq::<Seq<u8>>::empty()); }
    while (v.len() as u64) < n
        invariant
            buf_ok(buf@), p <= 8 * buf.len(), b == lbits(buf@), v@.len() <= n, n <= 256, 2 <= asize <= 1024,
            decs_wf(v@, lens_of(v@), asize as nat),
            read_codes(b, p as int, asize as nat, n as nat, lens_of(v@)) == target,
            target == read_codes(lbits(buf@), pos as int, asize as nat, n as nat, Seq::empty()),
        decreases n - v@.len(),
    {
        let (d, q) = match read_dec(buf, p, asize) { None => return None, Some(x) => x };
        let ghost v0 = v@;
        proof { assert(decs_wf(v0, lens_of(v0), asize as nat)); }
        v.push(d);
        proof {
            assert(lens_of(v@) =~= lens_of(v0).push(d.lens@));
            assert(decs_wf(v@, lens_of(v@), asize as nat)) by {
                assert forall|i: int| #![trigger v@[i]] 0 <= i < v@.len() implies dec_wf(&v@[i]) && v@[i].lens@ == lens_of(v@)[i]
                    && v@[i].lens@.len() == asize by {
                    if i < v0.len() {
                        assert(v@[i] == v0[i]);
                        assert(dec_wf(&v0[i]));
                        assert(v0[i].lens@ == lens_of(v0)[i]);
                        assert(v0[i].lens@.len() == asize);
                    } else {
                        assert(v@[i] == d);
                    }
                }
            }
        }
        p = q;
    }
    Some((v, p))
}

/// A compressed meta-block's header, ready to decode with.
pub struct XHdr {
    pub cl: XCat,
    pub ci: XCat,
    pub cd: XCat,
    pub npostfix: u64,
    pub ndirect: u64,
    pub modes: Vec<u8>,
    pub cmapl: Vec<u8>,
    /// For each literal block type, the one code all its contexts map to,
    /// or 256 if they map to more than one.
    pub triv: Vec<u16>,
    pub cmapd: Vec<u8>,
    pub lit: Vec<Dec>,
    pub cmd: Vec<Dec>,
    pub dist: Vec<Dec>,
    /// For the distance codes past the direct ones: the distance with extra
    /// bits 0, and the extra bits.
    pub dtab: Vec<u64>,
}

/// `triv[t]`, when below 256, is the value of every context of block type `t`.
pub open spec fn triv_ok(triv: Seq<u16>, cmap: Seq<u8>, n: nat) -> bool {
    &&& triv.len() == n
    &&& forall|t: int, c: int| 0 <= t < n && 0 <= c < 64 && #[trigger] triv[t] < 256
            ==> #[trigger] cmap[64 * t + c] as u16 == triv[t]
}

/// Which literal block types map every context to one code.
fn trivial_x(cmap: &Vec<u8>, n: u64) -> (r: Vec<u16>)
    requires cmap@.len() == 64 * n, n <= 256,
    ensures triv_ok(r@, cmap@, n as nat),
{
    let mut r: Vec<u16> = Vec::new();
    let mut t: u64 = 0;
    while t < n
        invariant t <= n, n <= 256, cmap@.len() == 64 * n, r@.len() == t, triv_ok(r@, cmap@, t as nat),
        decreases n - t,
    {
        let row = (64 * t) as usize;
        let v = cmap[row];
        let mut same = true;
        let mut c: usize = 1;
        while c < 64
            invariant
                1 <= c <= 64, row == 64 * t, t < n, cmap@.len() == 64 * n, v == cmap@[row as int],
                same ==> forall|j: int| 0 <= j < c ==> #[trigger] cmap@[row + j] == v,
            decreases 64 - c,
        {
            if cmap[row + c] != v {
                same = false;
            }
            c = c + 1;
        }
        let ghost r0 = r@;
        r.push(if same { v as u16 } else { 256 });
        proof {
            assert forall|tt: int, cc: int| 0 <= tt < t + 1 && 0 <= cc < 64 && #[trigger] r@[tt] < 256
                implies #[trigger] cmap@[64 * tt + cc] as u16 == r@[tt] by {
                if tt < t { assert(r@[tt] == r0[tt]); } else { assert(cmap@[row + cc] == v); }
            }
        }
        t = t + 1;
    }
    r
}

pub open spec fn xhdr_wf(x: &XHdr, h: Hdr) -> bool {
    &&& xcat_wf(&x.cl, h.cl) && xcat_wf(&x.ci, h.ci) && xcat_wf(&x.cd, h.cd)
    &&& x.npostfix as nat == h.npostfix && x.npostfix <= 3
    &&& x.ndirect as nat == h.ndirect && x.ndirect <= 120
    &&& unat(x.modes@) == h.modes && x.modes@.len() == x.cl.n
    &&& forall|i: int| 0 <= i < x.modes@.len() ==> (#[trigger] x.modes@[i]) < 4
    &&& unat(x.cmapl@) == h.cmapl && x.cmapl@.len() == 64 * x.cl.n
    &&& forall|i: int| 0 <= i < x.cmapl@.len() ==> (#[trigger] x.cmapl@[i] as int) < x.lit@.len()
    &&& triv_ok(x.triv@, x.cmapl@, x.cl.n as nat)
    &&& unat(x.cmapd@) == h.cmapd && x.cmapd@.len() == 4 * x.cd.n
    &&& forall|i: int| 0 <= i < x.cmapd@.len() ==> (#[trigger] x.cmapd@[i] as int) < x.dist@.len()
    &&& decs_wf(x.lit@, h.lit, 256)
    &&& decs_wf(x.cmd@, h.cmd, 704) && x.cmd@.len() == x.ci.n
    &&& decs_wf(x.dist@, h.dist, dist_asize(h.npostfix, h.ndirect))
    &&& dtab_ok(x.dtab@, h.npostfix, h.ndirect)
}

// ------------------------------------------------------ distance codes

pub proof fn lemma_p2_small()
    ensures p2(0) == 1, p2(1) == 2, p2(2) == 4, p2(3) == 8, p2(4) == 16,
{
    reveal_with_fuel(p2, 5);
}

/// `x / 2^k` and `x % 2^k` for k <= 4, as a shift and a mask.
#[inline(always)]
pub fn divmod_p2(x: u64, k: u64) -> (r: (u64, u64))
    requires k <= 4,
    ensures r.0 as nat == x as nat / p2(k as nat), r.1 as nat == x as nat % p2(k as nat), r.1 < 16,
{
    proof {
        vbits::prim_read::lemma_p2_eq_pow2(k as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(k as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, k);
        vstd::bits::lemma_u64_shr_is_div(x, k);
        vstd::bits::lemma_u64_low_bits_mask_is_mod(x, k as nat);
        lemma_p2_small();
        vbits::prim_read::lemma_p2_mono(k as nat, 4);
    }
    assert(1u64 << k >= 1) by (bit_vector) requires k <= 4;
    let mask = (1u64 << k) - 1;
    proof { assert(mask == vstd::bits::low_bits_mask(k as nat) as u64); }
    (x >> k, x & mask)
}

/// `m * 2^k` for k <= 3 and m below 2^26, as a product with a constant.
#[inline(always)]
pub fn mul_p2(m: u64, k: u64) -> (r: u64)
    requires k <= 3, m < 0x400_0000,
    ensures r as nat == m as nat * p2(k as nat), r < 0x2000_0000,
{
    proof { lemma_p2_small(); }
    if k == 0 {
        proof { assert(m as nat * p2(0) == m as nat); }
        m
    } else if k == 1 {
        proof { assert(m as nat * p2(1) == 2 * m as nat); }
        2 * m
    } else if k == 2 {
        proof { assert(m as nat * p2(2) == 4 * m as nat); }
        4 * m
    } else {
        proof { assert(m as nat * p2(3) == 8 * m as nat); }
        8 * m
    }
}

/// Each distance code past the short ones: its distance with extra bits 0
/// (4) plus its extra bits times 2^32. (Opaque: revealed where it is built
/// and read.)
#[verifier::opaque]
pub open spec fn dtab_ok(t: Seq<u64>, np: nat, nd: nat) -> bool {
    &&& t.len() == dist_asize(np, nd)
    &&& forall|dc: int| 16 <= dc < dist_asize(np, nd) ==> dtab_at(#[trigger] t[dc], np, nd, dc as nat)
}

pub open spec fn dtab_at(v: u64, np: nat, nd: nat, dc: nat) -> bool {
    let (base, nb) = (v % 0x1_0000_0000, v / 0x1_0000_0000);
    &&& nb <= 24 && base >= 1 && base + (p2(nb as nat) - 1) * p2(np) < 0x4000_0000
    &&& dc < 16 + nd ==> nb == 0 && base == dc - 15
    &&& dc >= 16 + nd ==> nb as nat == dist_nbits(np, nd, dc) && base as nat == long_dist(np, nd, dc, 0)
}

/// The extra bits add to the distance with extra bits 0.
pub proof fn lemma_long_dist_e(np: nat, nd: nat, dc: nat, e: nat)
    ensures long_dist(np, nd, dc, e) == long_dist(np, nd, dc, 0) + e * p2(np),
{
    let x = (dc - nd - 16) as nat;
    let offset = ((2 + (x / p2(np)) % 2) * p2(dist_nbits(np, nd, dc)) - 4) as nat;
    assert((offset + e) * p2(np) == offset * p2(np) + e * p2(np)) by (nonlinear_arith);
}

/// A distance code's extra bits and its distance with extra bits 0.
fn dist_code_x(np: u64, nd: u64, dc: u64) -> (r: (u32, u8))
    requires np <= 3, nd <= 120, 16 + nd <= dc < dist_asize(np as nat, nd as nat),
    ensures
        r.1 as nat == dist_nbits(np as nat, nd as nat, dc as nat) && r.1 <= 24,
        r.0 as nat == long_dist(np as nat, nd as nat, dc as nat, 0) && r.0 >= 1,
        r.0 + (p2(r.1 as nat) - 1) * p2(np as nat) < 0x4000_0000,
{
    proof { reveal_with_fuel(p2, 5); }
    let xx = dc - nd - 16;
    let (hx, _) = divmod_p2(xx, np + 1);
    let nb: u64 = 1 + hx;
    proof {
        assert(p2(np as nat + 1) == 2 * p2(np as nat));
        assert(xx < 48 * p2(np as nat));
        assert(hx < 24) by {
            let (xi, pi) = (xx as int, p2(np as nat) as int);
            assert(xi / (2 * pi) < 24) by (nonlinear_arith) requires xi < 48 * pi, pi >= 1, xi >= 0;
        }
        assert(nb as nat == dist_nbits(np as nat, nd as nat, dc as nat));
    }
    let (hcode, lcode) = divmod_p2(xx, np);
    proof {
        vbits::prim_read::lemma_p2_eq_pow2(nb as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(nb as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, nb);
        vbits::prim_read::lemma_p2_mono(nb as nat, 24);
        assert(p2(24) == 0x100_0000) by { reveal_with_fuel(p2, 25); }
    }
    let big: u64 = 1u64 << nb;
    assert(2 <= big <= 0x100_0000);
    let offset: u64 = if hcode % 2 == 0 { 2 * big - 4 } else { 3 * big - 4 };
    let base: u64 = mul_p2(offset, np) + lcode + nd + 1;
    let top: u64 = mul_p2(offset + big - 1, np) + lcode + nd + 1;
    proof {
        assert(offset as nat == ((2 + (hcode as nat) % 2) * p2(nb as nat) - 4) as nat);
        assert(lcode < p2(np as nat));
        assert((offset + big - 1) * p2(np as nat) == offset * p2(np as nat) + (p2(nb as nat) - 1) * p2(np as nat))
            by (nonlinear_arith) requires big == p2(nb as nat), big >= 1;
    }
    (base as u32, nb as u8)
}

/// The distance codes' table.
fn dist_tab_x(np: u64, nd: u64) -> (r: Vec<u64>)
    requires np <= 3, nd <= 120,
    ensures dtab_ok(r@, np as nat, nd as nat),
{
    proof {
        reveal(dtab_ok);
        reveal_with_fuel(p2, 5);
        vbits::prim_read::lemma_p2_mono(np as nat, 3);
        vbits::prim_read::lemma_p2_eq_pow2(np as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(np as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, np);
    }
    let pw = 1u64 << np;
    assert(pw <= 8);
    let size = 16 + nd + 48 * pw;
    proof { assert(size as nat == dist_asize(np as nat, nd as nat)); }
    let mut t: Vec<u64> = Vec::with_capacity(size as usize);
    let mut dc: u64 = 0;
    while dc < size
        invariant
            np <= 3, nd <= 120, size as nat == dist_asize(np as nat, nd as nat), dc <= size,
            t@.len() == dc,
            forall|c: int| 16 <= c < dc ==> dtab_at(#[trigger] t@[c], np as nat, nd as nat, c as nat),
        decreases size - dc,
    {
        let ghost o = t@;
        let v: u64 = if dc < 16 {
            0
        } else if dc < 16 + nd {
            proof {
                reveal_with_fuel(p2, 2);
                assert(p2(0) == 1);
                assert((p2(0) - 1) * p2(np as nat) == 0) by (nonlinear_arith) requires p2(0) == 1;
            }
            let v = dc - 15;
            assert(v % 0x1_0000_0000 == v && v / 0x1_0000_0000 == 0);
            assert(dtab_at(v, np as nat, nd as nat, dc as nat));
            v
        } else {
            let (b, n) = dist_code_x(np, nd, dc);
            let v = b as u64 + n as u64 * 0x1_0000_0000;
            assert(v % 0x1_0000_0000 == b as u64 && v / 0x1_0000_0000 == n as u64);
            assert(dtab_at(v, np as nat, nd as nat, dc as nat));
            v
        };
        t.push(v);
        proof {
            assert forall|c: int| 16 <= c < dc + 1 implies dtab_at(#[trigger] t@[c], np as nat, nd as nat, c as nat) by {
                if c < dc { assert(t@[c] == o[c]); } else { assert(t@[c] == v); }
            }
        }
        dc = dc + 1;
    }
    t
}

#[verifier::spinoff_prover]
pub fn read_hdr_x(buf: &[u8], p: usize) -> (r: Option<(XHdr, usize)>)
    requires buf_ok(buf@), p <= 8 * buf.len(),
    ensures
        match r {
            Some((x, q)) => read_hdr(lbits(buf@), p as int) matches Some((h, q2))
                && q2 == q as int && xhdr_wf(&x, h) && q <= 8 * buf.len(),
            None => read_hdr(lbits(buf@), p as int) is None,
        },
{
    let (cl, p1) = match read_cat_x(buf, p) { None => return None, Some(x) => x };
    let (ci, p2_) = match read_cat_x(buf, p1) { None => return None, Some(x) => x };
    let (cd, p3) = match read_cat_x(buf, p2_) { None => return None, Some(x) => x };
    let npostfix = match getbits_x(buf, p3, 2) { None => return None, Some(x) => x };
    let nd4 = match getbits_x(buf, p3 + 2, 4) { None => return None, Some(x) => x };
    proof {
        reveal_with_fuel(p2, 5);
        vbits::prim_read::lemma_p2_eq_pow2(npostfix as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(npostfix as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, npostfix);
        vbits::prim_read::lemma_p2_mono(npostfix as nat, 3);
        assert(nd4 * (1u64 << npostfix) <= 15 * 8) by (nonlinear_arith)
            requires nd4 < 16, (1u64 << npostfix) <= 8;
    }
    let ndirect = nd4 * (1u64 << npostfix);
    let (modes, p4) = match read_modes_x(buf, p3 + 6, cl.n) { None => return None, Some(x) => x };
    let (cmapl, ntl, p5) = match read_cmap_x(buf, p4, (64 * cl.n) as usize) { None => return None, Some(x) => x };
    let (cmapd, ntd, p6) = match read_cmap_x(buf, p5, (4 * cd.n) as usize) { None => return None, Some(x) => x };
    let (lit, p7) = match read_codes_x(buf, p6, 256, ntl) { None => return None, Some(x) => x };
    let (cmd, p8) = match read_codes_x(buf, p7, 704, ci.n) { None => return None, Some(x) => x };
    let dsize = 16 + ndirect + 48 * (1u64 << npostfix);
    proof { assert(dsize as nat == dist_asize(npostfix as nat, ndirect as nat)); }
    let (dist, p9) = match read_codes_x(buf, p8, dsize, ntd) { None => return None, Some(x) => x };
    let triv = trivial_x(&cmapl, cl.n);
    let dtab = dist_tab_x(npostfix, ndirect);
    Some((XHdr { cl, ci, cd, npostfix, ndirect, modes, cmapl, triv, cmapd, lit, cmd, dist, dtab }, p9))
}

} // verus!
