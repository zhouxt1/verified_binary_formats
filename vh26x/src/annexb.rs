//! Annex B byte streams (H.264 B.1, H.265 B.2): NAL units after start
//! codes 0x000001, with zero bytes around them (leading_zero_8bits,
//! zero_byte, trailing_zero_8bits).
//!
//! `split` is the decoding of B.2 / B.3: find each start code, and take the
//! NAL unit to be the bytes up to the next start code, less the zero bytes
//! before it (a NAL unit's last byte is not 0x00, §7.4.1).
//!
//! * `theorem_split_complete`: NAL units that do not contain 0x000001 and
//!   do not end in 0x00 (which every NAL unit §7.4.1 allows satisfies), with
//!   any zero bytes before, between and after them, split back into
//!   exactly those NAL units.
//! * `theorem_split_sound`: whatever `split` returns is such a padding of
//!   the stream: the stream is those NAL units with zero bytes around their
//!   start codes, and each has no 0x000001 and ends in a nonzero byte.
//!
//! So the stream's NAL units are unique, and the only freedom an encoder
//! has is the zero bytes.
use vstd::prelude::*;

verus! {

pub open spec fn z8(n: nat) -> Seq<u8> { Seq::new(n, |i: int| 0u8) }

pub open spec fn sc() -> Seq<u8> { seq![0u8, 0u8, 1u8] }

pub open spec fn is_sc(b: Seq<u8>, i: int) -> bool {
    0 <= i && i + 2 < b.len() && b[i] == 0 && b[i + 1] == 0 && b[i + 2] == 1
}

/// The first start code at or after `i`.
pub open spec fn next_sc(b: Seq<u8>, i: nat) -> Option<nat>
    decreases b.len() - i,
{
    if i + 2 >= b.len() { None } else if is_sc(b, i as int) { Some(i) } else { next_sc(b, i + 1) }
}

/// Bytes less their trailing zeros.
pub open spec fn strip(n: Seq<u8>) -> Seq<u8>
    decreases n.len(),
{
    if n.len() == 0 { n } else if n.last() == 0 { strip(n.drop_last()) } else { n }
}

/// The NAL units of `b` from byte `i`, where one starts.
pub open spec fn split_from(b: Seq<u8>, i: nat) -> Seq<Seq<u8>>
    decreases b.len() - i,
{
    if i > b.len() {
        Seq::empty()
    } else {
        match next_sc(b, i) {
            Some(j) => if j >= i && j + 3 <= b.len() { seq![strip(b.subrange(i as int, j as int))] + split_from(b, j + 3) } else { Seq::empty() },
            None => seq![strip(b.skip(i as int))],
        }
    }
}

/// How many zero bytes `b` starts with, from `i`.
pub open spec fn lead0(b: Seq<u8>, i: nat) -> nat
    decreases b.len() - i,
{
    if i >= b.len() || b[i as int] != 0 { i } else { lead0(b, i + 1) }
}

/// B.2: zero bytes, then a start code, then NAL units; or only zero bytes.
pub open spec fn split(b: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    let z = lead0(b, 0);
    if z == b.len() { Some(Seq::empty()) } else if z >= 2 && b[z as int] == 1 { Some(split_from(b, z + 1)) } else { None }
}

/// A NAL unit as the split sees it: no start code inside, and a last byte
/// that is not zero.
pub open spec fn nal_shape(n: Seq<u8>) -> bool {
    &&& n.len() >= 1
    &&& n.last() != 0
    &&& forall|j: int| !#[trigger] is_sc(n, j)
}

/// NAL units after start codes, each followed by `t[i]` zero bytes.
pub open spec fn body(nals: Seq<Seq<u8>>, t: Seq<nat>) -> Seq<u8>
    decreases nals.len(),
{
    if nals.len() == 0 || t.len() == 0 {
        Seq::empty()
    } else {
        sc() + nals[0] + z8(t[0]) + body(nals.skip(1), t.skip(1))
    }
}

/// A byte stream of `nals`: `z` leading zero bytes, then each after a start
/// code and followed by its zero bytes.
pub open spec fn stream(nals: Seq<Seq<u8>>, z: nat, t: Seq<nat>) -> Seq<u8> {
    z8(z) + body(nals, t)
}

/// Every NAL unit §7.4.1 allows has that shape.
pub proof fn lemma_nal_ok_shape(n: Seq<u8>)
    requires crate::esc::nal_ok(n),
    ensures nal_shape(n),
{
    assert forall|j: int| !#[trigger] is_sc(n, j) by {
        if is_sc(n, j) {
            assert(crate::esc::ok_at(n, j));
        }
    }
}

// ------------------------------------------------------------------ lemmas

proof fn lemma_strip_pad(n: Seq<u8>, t: nat)
    requires n.len() >= 1, n.last() != 0,
    ensures strip(n + z8(t)) == n,
    decreases t,
{
    if t == 0 {
        assert(n + z8(0) =~= n);
    } else {
        let m = n + z8(t);
        assert(m.last() == 0);
        assert(m.drop_last() =~= n + z8((t - 1) as nat));
        lemma_strip_pad(n, (t - 1) as nat);
    }
}

proof fn lemma_next_sc_at(b: Seq<u8>, i: nat, j: nat)
    requires i <= j, is_sc(b, j as int), forall|k: int| i <= k < j ==> !#[trigger] is_sc(b, k),
    ensures next_sc(b, i) == Some(j),
    decreases j - i,
{
    if i < j {
        lemma_next_sc_at(b, i + 1, j);
    }
}

proof fn lemma_next_sc_none(b: Seq<u8>, i: nat)
    requires forall|k: int| i <= k ==> !#[trigger] is_sc(b, k),
    ensures next_sc(b, i) is None,
    decreases b.len() - i,
{
    if i + 2 < b.len() {
        lemma_next_sc_none(b, i + 1);
    }
}

proof fn lemma_next_sc_props(b: Seq<u8>, i: nat)
    ensures match next_sc(b, i) {
        Some(j) => i <= j && is_sc(b, j as int) && forall|k: int| i <= k < j ==> !#[trigger] is_sc(b, k),
        None => forall|k: int| i <= k ==> !#[trigger] is_sc(b, k),
    },
    decreases b.len() - i,
{
    if i + 2 < b.len() && !is_sc(b, i as int) {
        lemma_next_sc_props(b, i + 1);
    }
}

proof fn lemma_lead0_at(b: Seq<u8>, i: nat, z: nat)
    requires i <= z <= b.len(), forall|k: int| i <= k < z ==> b[k] == 0, z == b.len() || b[z as int] != 0,
    ensures lead0(b, i) == z,
    decreases z - i,
{
    if i < z {
        lemma_lead0_at(b, i + 1, z);
    }
}

proof fn lemma_lead0_props(b: Seq<u8>, i: nat)
    requires i <= b.len(),
    ensures ({
        let z = lead0(b, i);
        &&& i <= z <= b.len()
        &&& forall|k: int| i <= k < z ==> b[k] == 0
        &&& z == b.len() || b[z as int] != 0
    }),
    decreases b.len() - i,
{
    if i < b.len() && b[i as int] == 0 {
        lemma_lead0_props(b, i + 1);
    }
}

/// Within `pre + n + z8(t) + sc() + rest`, the first start code from where
/// `n` begins is the one after it.
proof fn lemma_one(pre: Seq<u8>, n: Seq<u8>, t: nat, rest: Seq<u8>)
    requires nal_shape(n),
    ensures ({
        let b = pre + n + z8(t) + sc() + rest;
        let i = pre.len();
        &&& next_sc(b, i) == Some(i + n.len() + t)
        &&& b.subrange(i as int, (i + n.len() + t) as int) =~= n + z8(t)
    }),
{
    let b = pre + n + z8(t) + sc() + rest;
    let i = pre.len();
    let j = i + n.len() + t;
    assert(is_sc(b, j as int)) by {
        assert(b[j as int] == sc()[0]);
        assert(b[j + 1int] == sc()[1]);
        assert(b[j + 2int] == sc()[2]);
    }
    assert forall|k: int| i <= k < j implies !#[trigger] is_sc(b, k) by {
        if is_sc(b, k) {
            if k + 2 < i + n.len() {
                // inside n
                assert(is_sc(n, k - i)) by {
                    assert(n[k - i] == b[k]);
                    assert(n[k - i + 1] == b[k + 1]);
                    assert(n[k - i + 2] == b[k + 2]);
                }
            } else if k + 2 < j {
                // the 1 would be a zero byte
                assert(b[k + 2] == z8(t)[k + 2 - i - n.len()]);
            } else if k + 2 == j {
                assert(b[k + 2] == sc()[0]);
            } else {
                // k + 2 == j + 1: the second byte of the start code
                assert(k + 2 == j + 1);
                assert(b[k + 2] == sc()[1]);
            }
        }
    }
    lemma_next_sc_at(b, i, j);
}

/// The same, for the last NAL unit.
proof fn lemma_last(pre: Seq<u8>, n: Seq<u8>, t: nat)
    requires nal_shape(n),
    ensures ({
        let b = pre + n + z8(t);
        &&& next_sc(b, pre.len()) is None
        &&& b.skip(pre.len() as int) =~= n + z8(t)
    }),
{
    let b = pre + n + z8(t);
    let i = pre.len();
    assert forall|k: int| i <= k implies !#[trigger] is_sc(b, k) by {
        if is_sc(b, k) {
            if k + 2 < i + n.len() {
                assert(is_sc(n, k - i)) by {
                    assert(n[k - i] == b[k]);
                    assert(n[k - i + 1] == b[k + 1]);
                    assert(n[k - i + 2] == b[k + 2]);
                }
            } else {
                assert(b[k + 2] == z8(t)[k + 2 - i - n.len()]);
            }
        }
    }
    lemma_next_sc_none(b, i);
}

proof fn lemma_split_body(pre: Seq<u8>, nals: Seq<Seq<u8>>, t: Seq<nat>)
    requires
        nals.len() >= 1, t.len() == nals.len(),
        forall|k: int| 0 <= k < nals.len() ==> nal_shape(#[trigger] nals[k]),
    ensures split_from(pre + body(nals, t), pre.len() + 3) == nals,
    decreases nals.len(),
{
    let n = nals[0];
    let b = pre + body(nals, t);
    let p3 = pre + sc();
    assert(body(nals, t) == sc() + n + z8(t[0]) + body(nals.skip(1), t.skip(1)));
    if nals.len() == 1 {
        assert(body(nals.skip(1), t.skip(1)) =~= Seq::<u8>::empty());
        assert(b =~= p3 + n + z8(t[0]));
        lemma_last(p3, n, t[0]);
        lemma_strip_pad(n, t[0]);
        assert(split_from(b, p3.len()) =~= seq![n]);
        assert(nals =~= seq![n]);
    } else {
        let rest_nals = nals.skip(1);
        let rest_t = t.skip(1);
        let n1 = rest_nals[0];
        assert(body(rest_nals, rest_t) == sc() + n1 + z8(rest_t[0]) + body(rest_nals.skip(1), rest_t.skip(1)));
        let tail = n1 + z8(rest_t[0]) + body(rest_nals.skip(1), rest_t.skip(1));
        assert(b =~= p3 + n + z8(t[0]) + sc() + tail);
        lemma_one(p3, n, t[0], tail);
        lemma_strip_pad(n, t[0]);
        let j = p3.len() + n.len() + t[0];
        let pre2 = p3 + n + z8(t[0]);
        assert(b =~= pre2 + body(rest_nals, rest_t));
        assert(forall|k: int| 0 <= k < rest_nals.len() ==> nal_shape(#[trigger] rest_nals[k])) by {
            assert forall|k: int| 0 <= k < rest_nals.len() implies nal_shape(#[trigger] rest_nals[k]) by {
                assert(rest_nals[k] == nals[k + 1]);
            }
        }
        lemma_split_body(pre2, rest_nals, rest_t);
        assert(pre2.len() == j);
        assert(split_from(b, p3.len()) == seq![n] + split_from(b, j + 3));
        assert(nals =~= seq![n] + rest_nals);
    }
}

/// NAL units that do not contain a start code and do not end in zero,
/// padded with any zero bytes, split back into themselves.
pub proof fn theorem_split_complete(nals: Seq<Seq<u8>>, z: nat, t: Seq<nat>)
    requires
        t.len() == nals.len(),
        forall|k: int| 0 <= k < nals.len() ==> nal_shape(#[trigger] nals[k]),
    ensures split(stream(nals, z, t)) == Some(nals),
{
    let b = stream(nals, z, t);
    if nals.len() == 0 {
        assert(body(nals, t) =~= Seq::<u8>::empty());
        assert(b =~= z8(z));
        lemma_lead0_at(b, 0, z);
        assert(nals =~= Seq::<Seq<u8>>::empty());
    } else {
        assert(body(nals, t) == sc() + nals[0] + z8(t[0]) + body(nals.skip(1), t.skip(1)));
        assert(b[z as int] == 0 && b[z + 1int] == 0 && b[z + 2int] == 1);
        lemma_lead0_at(b, 0, z + 2);
        lemma_split_body(z8(z), nals, t);
    }
}

// ---------------------------------------------------------- soundness

/// What `split_from` returns is a padding of the bytes from `i`.
proof fn lemma_split_from_sound(b: Seq<u8>, i: nat)
    requires i <= b.len(),
    ensures ({
        let nals = split_from(b, i);
        &&& nals.len() >= 1
        &&& forall|k: int| 0 <= k < nals.len() ==> (#[trigger] nals[k]).len() == 0 || nal_shape(nals[k])
        &&& exists|t0: nat, t: Seq<nat>| #![auto] t.len() == nals.len() - 1 &&
                b.skip(i as int) =~= nals[0] + z8(t0) + body(nals.skip(1), t)
    }),
    decreases b.len() - i,
{
    lemma_next_sc_props(b, i);
    let seg = match next_sc(b, i) { Some(j) => b.subrange(i as int, j as int), None => b.skip(i as int) };
    lemma_strip_props(seg);
    let n = strip(seg);
    let t0 = (seg.len() - n.len()) as nat;
    assert(seg =~= n + z8(t0));
    // n has no start code: one in it would be one in b before the next
    assert forall|k: int| !#[trigger] is_sc(n, k) implies true by {}
    assert forall|k: int| is_sc(n, k) implies false by {
        assert(is_sc(b, i + k)) by {
            assert(b[i + k] == seg[k]);
            assert(b[i + k + 1] == seg[k + 1]);
            assert(b[i + k + 2] == seg[k + 2]);
        }
    }
    match next_sc(b, i) {
        Some(j) => {
            lemma_split_from_sound(b, j + 3);
            let rest = split_from(b, j + 3);
            let (t1, tr) = choose|t1: nat, tr: Seq<nat>| #![auto] tr.len() == rest.len() - 1 &&
                b.skip((j + 3) as int) =~= rest[0] + z8(t1) + body(rest.skip(1), tr);
            let nals = seq![n] + rest;
            assert(split_from(b, i) == nals);
            let t = seq![t1] + tr;
            assert(nals.skip(1) =~= rest);
            assert(body(rest, t) == sc() + rest[0] + z8(t[0]) + body(rest.skip(1), t.skip(1)));
            assert(t.skip(1) =~= tr);
            assert(b.skip(i as int) =~= seg + sc() + b.skip((j + 3) as int));
            assert(b.skip(i as int) =~= nals[0] + z8(t0) + body(nals.skip(1), t));
            assert forall|k: int| 0 <= k < nals.len() implies (#[trigger] nals[k]).len() == 0 || nal_shape(nals[k]) by {
                if k > 0 { assert(nals[k] == rest[k - 1]); }
            }
        }
        None => {
            let nals = seq![n];
            assert(split_from(b, i) == nals);
            assert(nals.skip(1) =~= Seq::<Seq<u8>>::empty());
            assert(body(nals.skip(1), Seq::<nat>::empty()) =~= Seq::<u8>::empty());
            assert(b.skip(i as int) =~= nals[0] + z8(t0) + body(nals.skip(1), Seq::<nat>::empty()));
        }
    }
}

proof fn lemma_strip_props(s: Seq<u8>)
    ensures ({
        let n = strip(s);
        &&& n.len() <= s.len()
        &&& n =~= s.take(n.len() as int)
        &&& n.len() == 0 || n.last() != 0
        &&& forall|k: int| n.len() <= k < s.len() ==> s[k] == 0
    }),
    decreases s.len(),
{
    if s.len() > 0 && s.last() == 0 {
        let d = s.drop_last();
        lemma_strip_props(d);
        let n = strip(d);
        assert(strip(s) == n);
        assert(n =~= s.take(n.len() as int));
        assert forall|k: int| n.len() <= k < s.len() implies s[k] == 0 by {
            if k < d.len() { assert(s[k] == d[k]); }
        }
    } else {
        assert(s.take(s.len() as int) =~= s);
    }
}

/// Whatever `split` returns is a zero-byte padding of the stream, and each
/// NAL unit it returns has no start code and is empty or ends in nonzero.
pub proof fn theorem_split_sound(b: Seq<u8>)
    requires split(b) is Some,
    ensures
        forall|k: int| 0 <= k < split(b).unwrap().len() ==> (#[trigger] split(b).unwrap()[k]).len() == 0 || nal_shape(split(b).unwrap()[k]),
        exists|z: nat, t: Seq<nat>| t.len() == split(b).unwrap().len() && b == #[trigger] stream(split(b).unwrap(), z, t),
{
    lemma_lead0_props(b, 0);
    let z = lead0(b, 0);
    if z == b.len() {
        assert(b =~= z8(z));
        let e = Seq::<Seq<u8>>::empty();
        assert(split(b) == Some(e));
        assert(body(e, Seq::<nat>::empty()) =~= Seq::<u8>::empty());
        assert(b =~= stream(e, z, Seq::<nat>::empty()));
        let t = Seq::<nat>::empty();
        assert(t.len() == e.len() && b =~= stream(e, z, t));
        assert(b == stream(split(b).unwrap(), z, t));
    } else {
        lemma_split_from_sound(b, z + 1);
        let nals = split_from(b, z + 1);
        let (t0, tr) = choose|t0: nat, tr: Seq<nat>| #![auto] tr.len() == nals.len() - 1 &&
            b.skip((z + 1) as int) =~= nals[0] + z8(t0) + body(nals.skip(1), tr);
        let t = seq![t0] + tr;
        assert(t.skip(1) =~= tr);
        assert(body(nals, t) == sc() + nals[0] + z8(t[0]) + body(nals.skip(1), t.skip(1)));
        let zz = (z - 2) as nat;
        assert(split(b) == Some(nals));
        assert(b =~= z8(zz) + sc() + b.skip((z + 1) as int));
        assert(t.len() == nals.len());
        assert(b =~= stream(nals, zz, t));
        assert(t.len() == nals.len() && b =~= stream(nals, zz, t));
        assert(b == stream(split(b).unwrap(), zz, t));
    }
}

// ------------------------------------------------------------------- exec

/// `split`, as byte ranges of `b`: each NAL unit is `b[s..e]`.
pub fn split_x(b: &[u8]) -> (res: Option<Vec<(usize, usize)>>)
    ensures
        match split(b@) {
            Some(nals) => res is Some && res.unwrap()@.len() == nals.len() && forall|k: int| 0 <= k < nals.len() ==> ({
                let (s, e) = #[trigger] res.unwrap()@[k];
                s <= e <= b@.len() && b@.subrange(s as int, e as int) == nals[k]
            }),
            None => res is None,
        },
{
    let mut z: usize = 0;
    while z < b.len() && b[z] == 0
        invariant z <= b@.len(), forall|k: int| 0 <= k < z ==> b@[k] == 0,
        decreases b@.len() - z,
    {
        z = z + 1;
    }
    proof { lemma_lead0_at(b@, 0, z as nat); }
    if z == b.len() {
        return Some(Vec::new());
    }
    if z < 2 || b[z] != 1 {
        return None;
    }
    let mut out: Vec<(usize, usize)> = Vec::new();
    let mut i: usize = z + 1;
    let ghost all = split_from(b@, (z + 1) as nat);
    proof { assert(out_view(b@, out@) =~= Seq::<Seq<u8>>::empty()); assert(all =~= out_view(b@, out@) + all); }
    loop
        invariant
            i <= b@.len(),
            all == split_from(b@, (z + 1) as nat),
            split(b@) == Some(all),
            all =~= out_view(b@, out@) + split_from(b@, i as nat),
            forall|k: int| 0 <= k < out@.len() ==> ({
                let (s, e) = #[trigger] out@[k];
                s <= e <= b@.len()
            }),
        decreases b@.len() - i,
    {
        // the next start code from i
        let mut j: usize = i;
        while j < b.len() && b.len() - j > 2 && !(b[j] == 0 && b[j + 1] == 0 && b[j + 2] == 1)
            invariant
                i <= j, j <= b@.len(),
                forall|k: int| i <= k < j ==> !#[trigger] is_sc(b@, k),
            decreases b@.len() - j,
        {
            j = j + 1;
        }
        let found = j < b.len() && b.len() - j > 2;
        let end = if found { j } else { b.len() };
        proof {
            if found {
                lemma_next_sc_at(b@, i as nat, j as nat);
            } else {
                assert forall|k: int| i <= k implies !#[trigger] is_sc(b@, k) by {
                    if k >= j { assert(k + 2 >= b@.len()); }
                }
                lemma_next_sc_none(b@, i as nat);
            }
        }
        // less its trailing zeros
        let mut e: usize = end;
        let ghost seg = b@.subrange(i as int, end as int);
        proof { assert(seg.take((e - i) as int) =~= seg); }
        while e > i && b[e - 1] == 0
            invariant
                i <= e <= end, end <= b@.len(),
                seg == b@.subrange(i as int, end as int),
                strip(seg) == strip(seg.take((e - i) as int)),
            decreases e,
        {
            proof {
                let s0 = seg.take((e - i) as int);
                assert(s0.last() == 0);
                assert(s0.drop_last() =~= seg.take((e - 1 - i) as int));
            }
            e = e - 1;
        }
        proof {
            let s0 = seg.take((e - i) as int);
            assert(s0 =~= b@.subrange(i as int, e as int));
            if e > i { assert(s0.last() == b@[e - 1]); }
            else { assert(s0 =~= Seq::<u8>::empty()); }
            if !found { assert(seg =~= b@.skip(i as int)); }
        }
        let ghost before = out@;
        out.push((i, e));
        proof {
            assert(out_view(b@, out@) =~= out_view(b@, before) + seq![b@.subrange(i as int, e as int)]) by {
                assert(out@.drop_last() =~= before);
            }
        }
        if !found {
            proof {
                assert(split_from(b@, i as nat) =~= seq![strip(b@.skip(i as int))]);
                assert(all =~= out_view(b@, out@));
                assert(split_from(b@, (z + 1) as nat) =~= out_view(b@, out@));
                lemma_out_view(b@, out@);
            }
            return Some(out);
        }
        proof {
            assert(split_from(b@, i as nat) == seq![strip(b@.subrange(i as int, j as int))] + split_from(b@, (j + 3) as nat));
        }
        i = j + 3;
    }
}

proof fn lemma_out_view(b: Seq<u8>, out: Seq<(usize, usize)>)
    ensures
        out_view(b, out).len() == out.len(),
        forall|k: int| 0 <= k < out.len() ==> out_view(b, out)[k] == b.subrange(out[k].0 as int, out[k].1 as int),
    decreases out.len(),
{
    if out.len() > 0 {
        lemma_out_view(b, out.drop_last());
        assert forall|k: int| 0 <= k < out.len() implies out_view(b, out)[k] == b.subrange(out[k].0 as int, out[k].1 as int) by {
            if k < out.len() - 1 { assert(out.drop_last()[k] == out[k]); }
        }
    }
}

pub open spec fn out_view(b: Seq<u8>, out: Seq<(usize, usize)>) -> Seq<Seq<u8>>
    decreases out.len(),
{
    if out.len() == 0 {
        Seq::empty()
    } else {
        out_view(b, out.drop_last()) + seq![b.subrange(out.last().0 as int, out.last().1 as int)]
    }
}

} // verus!
