//! Static dictionary words and their transforms (RFC 7932 8), proved to
//! compute the spec's `dict_word` and `transform`.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::spec::*;
use crate::tables::*;

verus! {

/// DOFFSET of 8, for lengths 0..25.
pub const DOFF: [u32; 26] = [0, 0, 0, 0, 0, 4096, 9216, 21504, 35840, 44032, 53248, 63488, 74752, 87040, 93696,
    100864, 104704, 106752, 108928, 113536, 115968, 118528, 119872, 121280, 122016, 122784];

proof fn lemma_doff_step()
    ensures
        DOFF@[0] == 0,
        forall|l: int| 0 <= l < 25 ==> (#[trigger] DOFF@[l + 1]) as nat
            == DOFF@[l] as nat + l * (if l >= 4 { p2(ndbits()[l] as nat) } else { 0nat }),
{
    assert(ndbits() =~= seq![0u8, 0u8, 0u8, 0u8, 10u8, 10u8, 11u8, 11u8, 10u8, 10u8, 10u8, 10u8, 10u8, 9u8, 9u8, 8u8, 7u8, 7u8, 8u8, 7u8, 7u8, 6u8, 6u8, 5u8, 5u8
    ]) by (compute);
    reveal_with_fuel(p2, 12);
    assert(DOFF@[1] as nat == DOFF@[0] as nat + 0 * 0nat);
    assert(DOFF@[2] as nat == DOFF@[1] as nat + 1 * 0nat);
    assert(DOFF@[3] as nat == DOFF@[2] as nat + 2 * 0nat);
    assert(DOFF@[4] as nat == DOFF@[3] as nat + 3 * 0nat);
    assert(DOFF@[5] as nat == DOFF@[4] as nat + 4 * p2(10));
    assert(DOFF@[6] as nat == DOFF@[5] as nat + 5 * p2(10));
    assert(DOFF@[7] as nat == DOFF@[6] as nat + 6 * p2(11));
    assert(DOFF@[8] as nat == DOFF@[7] as nat + 7 * p2(11));
    assert(DOFF@[9] as nat == DOFF@[8] as nat + 8 * p2(10));
    assert(DOFF@[10] as nat == DOFF@[9] as nat + 9 * p2(10));
    assert(DOFF@[11] as nat == DOFF@[10] as nat + 10 * p2(10));
    assert(DOFF@[12] as nat == DOFF@[11] as nat + 11 * p2(10));
    assert(DOFF@[13] as nat == DOFF@[12] as nat + 12 * p2(10));
    assert(DOFF@[14] as nat == DOFF@[13] as nat + 13 * p2(9));
    assert(DOFF@[15] as nat == DOFF@[14] as nat + 14 * p2(9));
    assert(DOFF@[16] as nat == DOFF@[15] as nat + 15 * p2(8));
    assert(DOFF@[17] as nat == DOFF@[16] as nat + 16 * p2(7));
    assert(DOFF@[18] as nat == DOFF@[17] as nat + 17 * p2(7));
    assert(DOFF@[19] as nat == DOFF@[18] as nat + 18 * p2(8));
    assert(DOFF@[20] as nat == DOFF@[19] as nat + 19 * p2(7));
    assert(DOFF@[21] as nat == DOFF@[20] as nat + 20 * p2(7));
    assert(DOFF@[22] as nat == DOFF@[21] as nat + 21 * p2(6));
    assert(DOFF@[23] as nat == DOFF@[22] as nat + 22 * p2(6));
    assert(DOFF@[24] as nat == DOFF@[23] as nat + 23 * p2(5));
    assert(DOFF@[25] as nat == DOFF@[24] as nat + 24 * p2(5));
    assert forall|l: int| 0 <= l < 25 implies (#[trigger] DOFF@[l + 1]) as nat
        == DOFF@[l] as nat + l * (if l >= 4 { p2(ndbits()[l] as nat) } else { 0nat }) by {
        assert(0 <= l < 25);
    }
}

proof fn lemma_doff_upto(l: nat)
    requires l <= 25,
    ensures DOFF@[l as int] as nat == doffset(l),
    decreases l,
{
    lemma_doff_step();
    if l > 0 {
        lemma_doff_upto((l - 1) as nat);
        assert(DOFF@[(l - 1) + 1] as nat == DOFF@[l - 1] as nat
            + (l - 1) * (if l - 1 >= 4 { p2(ndbits()[l - 1] as nat) } else { 0nat }));
    }
}

pub proof fn lemma_doff()
    ensures
        forall|l: int| 0 <= l <= 25 ==> (#[trigger] DOFF@[l]) as nat == doffset(l as nat),
        forall|l: int| 4 <= l <= 24 ==> (#[trigger] DOFF@[l + 1]) as nat
            == DOFF@[l] as nat + l * p2(ndbits()[l] as nat),
        forall|l: int| 4 <= l <= 24 ==> 5 <= (#[trigger] ndbits()[l]) <= 11,
        dict_size() == 122784,
{
    lemma_doff_step();
    assert forall|l: int| 0 <= l <= 25 implies (#[trigger] DOFF@[l]) as nat == doffset(l as nat) by {
        lemma_doff_upto(l as nat);
    }
    assert forall|l: int| 4 <= l <= 24 implies (#[trigger] DOFF@[l + 1]) as nat
        == DOFF@[l] as nat + l * p2(ndbits()[l] as nat) by {
        assert(DOFF@[l + 1] as nat == DOFF@[l] as nat + l * (if l >= 4 { p2(ndbits()[l] as nat) } else { 0nat }));
    }
    assert(forall|l: int| 4 <= l <= 24 ==> 5 <= (#[trigger] ndbits()[l]) <= 11) by (compute);
    lemma_doff_upto(25);
    assert(DOFF@[25] == 122784);
}

/// The word of length `len` and index `idx` lies in the dictionary.
pub proof fn lemma_word_in(len: nat, idx: nat)
    requires 4 <= len <= 24, idx < p2(ndbits()[len as int] as nat),
    ensures DOFF@[len as int] as nat + idx * len + len <= 122784,
        DOFF@[len as int] as nat + idx * len == doffset(len) + idx * len,
{
    lemma_doff();
    assert(DOFF@[len as int + 1] as nat == DOFF@[len as int] as nat + len * p2(ndbits()[len as int] as nat));
    let q = p2(ndbits()[len as int] as nat);
    assert(idx * len + len <= len * q) by (nonlinear_arith) requires idx < q, len >= 0;
    vbits::prim_read::lemma_p2_mono(ndbits()[len as int] as nat, 11);
    assert(p2(11) == 2048) by { reveal_with_fuel(p2, 12); }
    assert(DOFF@[len as int + 1] <= 122784);
}

/// Transform `id` from the tables.
pub proof fn lemma_transform(id: int, w: Seq<u8>)
    requires 0 <= id <= 120,
    ensures
        transform(id as nat, w) == TR_PRE@.subrange(TR_PRE_OFF@[id] as int, TR_PRE_OFF@[id + 1] as int)
            + elem(TR_TYPE@[id] as nat, w) + TR_SUF@.subrange(TR_SUF_OFF@[id] as int, TR_SUF_OFF@[id + 1] as int),
        TR_PRE_OFF@[id] <= TR_PRE_OFF@[id + 1] <= 55, TR_SUF_OFF@[id] <= TR_SUF_OFF@[id + 1] <= 230,
        TR_TYPE@[id] <= 20, TR_PRE@.len() == 55, TR_SUF@.len() == 230,
{
    lemma_tr();
    assert(TR_PRE_OFF@[id] <= TR_PRE_OFF@[id + 1] <= TR_PRE@.len());
}

/// `src[a..b]` written into `out` at `m`.
#[inline(always)]
pub fn put_x(out: &mut Vec<u8>, m: usize, src: &[u8], a: usize, b: usize)
    requires a <= b <= src@.len(), m + (b - a) <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        final(out)@.take(m as int) == old(out)@.take(m as int),
        final(out)@.subrange(m as int, m + (b - a)) == src@.subrange(a as int, b as int),
        final(out)@.take(m + (b - a)) == old(out)@.take(m as int) + src@.subrange(a as int, b as int),
{
    let ghost o = out@;
    let k = b - a;
    let _pl = out.len();
    out.as_mut_slice()[m..m + k].copy_from_slice(vstd::slice::slice_subrange(src, a, b));
    proof {
        assert(out@.subrange(m as int, m + k) =~= src@.subrange(a as int, b as int));
        assert(out@.take(m as int) =~= o.take(m as int));
        assert(out@.take(m + (b - a)) =~= o.take(m as int) + src@.subrange(a as int, b as int));
    }
}

/// `Ferment` at `pos` of the word `out[lo..hi]`, in place: how far it
/// moves on.
#[inline(always)]
pub fn ferment_o(out: &mut Vec<u8>, lo: usize, hi: usize, pos: usize) -> (step: usize)
    requires lo + pos < hi <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        final(out)@.take(lo as int) == old(out)@.take(lo as int),
        final(out)@.subrange(lo as int, hi as int) == ferment(old(out)@.subrange(lo as int, hi as int), pos as int),
        step as int == ferment_step(old(out)@.subrange(lo as int, hi as int), pos as int), 1 <= step <= 3,
{
    let ghost o = out@;
    let ghost w = o.subrange(lo as int, hi as int);
    let c = out[lo + pos];
    assert(w[pos as int] == c);
    if c < 192 {
        if 97 <= c && c <= 122 {
            out.set(lo + pos, c ^ 32);
            proof { assert(out@.subrange(lo as int, hi as int) =~= w.update(pos as int, c ^ 32u8)); }
        } else {
            proof { assert(out@.subrange(lo as int, hi as int) =~= w); }
        }
        proof { assert(out@.take(lo as int) =~= o.take(lo as int)); }
        1
    } else if c < 224 {
        if hi - lo - pos > 1 {
            let x = out[lo + pos + 1];
            out.set(lo + pos + 1, x ^ 32);
            proof { assert(out@.subrange(lo as int, hi as int) =~= w.update(pos + 1, x ^ 32u8)); }
        } else {
            proof { assert(out@.subrange(lo as int, hi as int) =~= w); }
        }
        proof { assert(out@.take(lo as int) =~= o.take(lo as int)); }
        2
    } else {
        if hi - lo - pos > 2 {
            let x = out[lo + pos + 2];
            out.set(lo + pos + 2, x ^ 5);
            proof { assert(out@.subrange(lo as int, hi as int) =~= w.update(pos + 2, x ^ 5u8)); }
        } else {
            proof { assert(out@.subrange(lo as int, hi as int) =~= w); }
        }
        proof { assert(out@.take(lo as int) =~= o.take(lo as int)); }
        3
    }
}

/// `FermentAll` of the word `out[lo..hi]`, in place.
pub fn ferment_all_o(out: &mut Vec<u8>, lo: usize, hi: usize)
    requires lo <= hi <= old(out)@.len(), hi - lo <= 24,
    ensures
        final(out)@.len() == old(out)@.len(),
        final(out)@.take(lo as int) == old(out)@.take(lo as int),
        final(out)@.subrange(lo as int, hi as int) == ferment_all(old(out)@.subrange(lo as int, hi as int), 0),
{
    let ghost w0 = out@.subrange(lo as int, hi as int);
    let n = hi - lo;
    let mut i: usize = 0;
    while i < n
        invariant
            lo + n == hi, hi <= out@.len(), out@.len() == old(out)@.len(), n <= 24, i <= n + 2,
            out@.take(lo as int) == old(out)@.take(lo as int),
            ferment_all(out@.subrange(lo as int, hi as int), i as int) == ferment_all(w0, 0),
            w0 == old(out)@.subrange(lo as int, hi as int),
        decreases n + 3 - i,
    {
        let ghost wb = out@.subrange(lo as int, hi as int);
        let step = ferment_o(out, lo, hi, i);
        proof { assert(ferment_all(wb, i as int) == ferment_all(out@.subrange(lo as int, hi as int), i + step)); }
        i = i + step;
    }
}

pub proof fn lemma_tr()
    ensures
        TR_PRE@ == tr_pre(), TR_SUF@ == tr_suf(), TR_TYPE@ == tr_type(),
        TR_PRE_OFF@ == tr_pre_off(), TR_SUF_OFF@ == tr_suf_off(),
        TR_PRE@.len() == 55, TR_SUF@.len() == 230,
        forall|i: int| 0 <= i < 121 ==> (#[trigger] TR_PRE_OFF@[i]) <= TR_PRE_OFF@[i + 1] <= TR_PRE@.len()
            && TR_SUF_OFF@[i] <= TR_SUF_OFF@[i + 1] <= TR_SUF@.len() && TR_TYPE@[i] <= 20,
{
    lemma_tr_pre();
    lemma_tr_suf();
    lemma_tr_type();
    lemma_tr_pre_off();
    lemma_tr_suf_off();
    assert(forall|i: int| 0 <= i < 121 ==> (#[trigger] TR_PRE_OFF@[i]) <= TR_PRE_OFF@[i + 1] <= TR_PRE@.len()
        && TR_SUF_OFF@[i] <= TR_SUF_OFF@[i + 1] <= TR_SUF@.len() && TR_TYPE@[i] <= 20) by (compute);
}

/// `FermentAll` keeps a word's length.
pub proof fn lemma_ferment_all_len(w: Seq<u8>, i: int)
    ensures ferment_all(w, i).len() == w.len(),
    decreases w.len() + 3 - i,
{
    if 0 <= i < w.len() {
        assert(ferment(w, i).len() == w.len());
        lemma_ferment_all_len(ferment(w, i), i + ferment_step(w, i));
    }
}

/// The length of elementary transform `t` of a word of length `len`.
#[inline(always)]
pub fn elem_len(t: u8, len: usize) -> (k: usize)
    requires t <= 20, 1 <= len <= 24,
    ensures forall|w: Seq<u8>| w.len() == len ==> (#[trigger] elem(t as nat, w)).len() == k, k <= len,
{
    let k = if t <= 2 {
        len
    } else if t <= 11 {
        if len < (t - 2) as usize { 0 } else { len - (t - 2) as usize }
    } else {
        if len < (t - 11) as usize { 0 } else { len - (t - 11) as usize }
    };
    proof {
        assert forall|w: Seq<u8>| w.len() == len implies (#[trigger] elem(t as nat, w)).len() == k by {
            if t == 2 { lemma_ferment_all_len(w, 0); }
        }
    }
    k
}

/// The elementary transform `t` of the word `dict[o..o + len]` written into
/// `out` at `m`: its length.
pub fn put_elem(out: &mut Vec<u8>, m: usize, dict: &[u8], o: usize, len: usize, t: u8) -> (k: usize)
    requires t <= 20, 1 <= len <= 24, o + len <= dict@.len(), o + len < 0x100_0000,
        m + elem(t as nat, dict@.subrange(o as int, o + len)).len() <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(), k <= len,
        k == elem(t as nat, dict@.subrange(o as int, o + len)).len(),
        final(out)@.take(m + k) == old(out)@.take(m as int) + elem(t as nat, dict@.subrange(o as int, o + len)),
{
    let ghost word = dict@.subrange(o as int, o + len);
    let pl = out.len();
    let (s, e): (usize, usize) = if t <= 2 {
        (0, len)
    } else if t <= 11 {
        if len < (t - 2) as usize { (0, 0) } else { ((t - 2) as usize, len) }
    } else {
        if len < (t - 11) as usize { (0, 0) } else { (0, len - (t - 11) as usize) }
    };
    proof {
        assert(dict@.subrange(o + s, o + e) =~= word.subrange(s as int, e as int));
        if 3 <= t <= 11 && len >= (t - 2) { assert(word.skip(t - 2) =~= word.subrange(s as int, e as int)); }
        if 12 <= t && len >= (t - 11) { assert(word.take(len - (t - 11)) =~= word.subrange(s as int, e as int)); }
        if t > 2 && s == e { assert(word.subrange(s as int, e as int) =~= Seq::<u8>::empty()); }
        if t <= 2 { assert(word.subrange(0, len as int) =~= word); }
        if t == 2 { lemma_ferment_all_len(word, 0); }
    }
    let ghost o0 = out@;
    put_x(out, m, dict, o + s, o + e);
    let k = e - s;
    if t == 1 || t == 2 {
        let ghost o1 = out@;
        if t == 1 {
            ferment_o(out, m, m + k, 0);
        } else {
            ferment_all_o(out, m, m + k);
        }
        proof {
            assert(out@.take(m + k) =~= out@.take(m as int) + out@.subrange(m as int, m + k));
            assert(o1.take(m + k) =~= o1.take(m as int) + o1.subrange(m as int, m + k));
            assert(o1.subrange(m as int, m + k) =~= word);
        }
    }
    k
}

} // verus!
