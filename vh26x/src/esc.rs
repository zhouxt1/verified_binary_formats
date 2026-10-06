//! Emulation prevention: a NAL unit's payload is its RBSP with a 0x03
//! after every two zero bytes that would otherwise be followed by a byte
//! from 0x00 to 0x03 (H.264 §7.3.1, §7.4.1; H.265 §7.3.1.1, §7.4.2).
//!
//! * `unesc` is §7.3.1's loop, as the standard writes it: three bytes
//!   0x000003 become 0x0000.
//! * `esc` is §7.4.1.1's encoder, with the final 0x03 after an RBSP that
//!   ends in two zero bytes.
//! * `nal_ok` is §7.4.1's constraints on a NAL unit's bytes: no 0x000000,
//!   0x000001 or 0x000002; 0x000003 only before 0x00..0x03 or at the end;
//!   a last byte that is not 0x00.
//!
//! `theorem_esc_rt`: unescaping an escaped RBSP gives it back.
//! `theorem_esc_inv`: a payload that satisfies `nal_ok` is the escaping of
//! what it unescapes to. So escaping is a bijection between RBSPs and
//! conforming payloads, and a conforming NAL unit has one encoding.
use vstd::prelude::*;

verus! {

/// §7.3.1, the loop over `i`.
pub open spec fn unesc(e: Seq<u8>) -> Seq<u8>
    decreases e.len(),
{
    if e.len() == 0 {
        Seq::empty()
    } else if e.len() >= 3 && e[0] == 0 && e[1] == 0 && e[2] == 3 {
        seq![0u8, 0u8] + unesc(e.skip(3))
    } else {
        seq![e[0]] + unesc(e.skip(1))
    }
}

/// The count of zero bytes just before, capped at 2.
pub open spec fn znext(z: nat, x: u8) -> nat {
    if x == 0 { if z >= 2 { 2 } else { z + 1 } } else { 0 }
}

/// `unesc`, stated with the count of preceding zeros instead of lookahead.
pub open spec fn unz(e: Seq<u8>, z: nat) -> Seq<u8>
    decreases e.len(),
{
    if e.len() == 0 {
        Seq::empty()
    } else if z >= 2 && e[0] == 3 {
        unz(e.skip(1), 0)
    } else {
        seq![e[0]] + unz(e.skip(1), znext(z, e[0]))
    }
}

/// §7.4.1.1, with `z` the zeros just written.
pub open spec fn esc(r: Seq<u8>, z: nat) -> Seq<u8>
    decreases r.len(),
{
    if r.len() == 0 {
        if z >= 2 { seq![3u8] } else { Seq::empty() }
    } else if z >= 2 && r[0] <= 3 {
        seq![3u8, r[0]] + esc(r.skip(1), znext(0, r[0]))
    } else {
        seq![r[0]] + esc(r.skip(1), znext(z, r[0]))
    }
}

/// §7.4.1, at byte `i`: no 0x000000, 0x000001 or 0x000002 starts there,
/// and a 0x000003 that starts there is followed by 0x00..0x03 or nothing.
pub open spec fn ok_at(n: Seq<u8>, i: int) -> bool {
    &&& !(n[i] == 0 && n[i + 1] == 0 && n[i + 2] <= 2)
    &&& i + 3 < n.len() ==> (n[i] == 0 && n[i + 1] == 0 && n[i + 2] == 3 ==> n[i + 3] <= 3)
}

/// §7.4.1: what the bytes of a NAL unit may not contain, and that its
/// last byte is not 0x00.
pub open spec fn nal_ok(n: Seq<u8>) -> bool {
    &&& n.len() >= 1
    &&& n.last() != 0
    &&& forall|i: int| 0 <= i && i + 2 < n.len() ==> #[trigger] ok_at(n, i)
}

pub open spec fn zeros8(z: nat) -> Seq<u8> { Seq::new(z, |i: int| 0u8) }

/// `unesc` after `z` zero bytes is those bytes and `unz` from state `z`.
proof fn lemma_unesc_unz(e: Seq<u8>, z: nat)
    requires z <= 2,
    ensures unesc(zeros8(z) + e) == zeros8(z) + unz(e, z),
    decreases e.len(), z,
{
    let ze = zeros8(z) + e;
    if e.len() == 0 {
        assert(ze =~= zeros8(z));
        if z == 0 {
            assert(zeros8(0) =~= Seq::<u8>::empty());
        } else if z == 1 {
            assert(zeros8(1).skip(1) =~= Seq::<u8>::empty());
            assert(zeros8(1) =~= seq![0u8]);
        } else {
            assert(zeros8(2).skip(1) =~= seq![0u8]);
            assert(seq![0u8].skip(1) =~= Seq::<u8>::empty());
            assert(zeros8(2) =~= seq![0u8, 0u8]);
            assert(unesc(seq![0u8]) =~= seq![0u8] + unesc(Seq::<u8>::empty()));
        }
        assert(unz(e, z) =~= Seq::<u8>::empty());
        assert(zeros8(z) + Seq::<u8>::empty() =~= zeros8(z));
    } else if z == 0 {
        assert(ze =~= e);
        assert(zeros8(0) + unz(e, 0) =~= unz(e, 0));
        if e[0] != 0 {
            lemma_unesc_unz(e.skip(1), 0);
            assert(zeros8(0) + e.skip(1) =~= e.skip(1));
            assert(zeros8(0) + unz(e.skip(1), 0) =~= unz(e.skip(1), 0));
        } else {
            // e = 0 · e', and unesc(e) = 0 · unz(e', 1) by the z = 1 case
            lemma_unesc_unz(e.skip(1), 1);
            assert(zeros8(1) + e.skip(1) =~= e);
            assert(zeros8(1) + unz(e.skip(1), 1) =~= seq![e[0]] + unz(e.skip(1), znext(0, e[0])));
        }
    } else if z == 1 {
        if e[0] != 0 {
            // no pattern at the zero; unesc(0 · e) = 0 · unesc(e)
            assert(ze.skip(1) =~= e);
            assert(unesc(ze) =~= seq![0u8] + unesc(e));
            lemma_unesc_unz(e, 0);
            assert(zeros8(0) + e =~= e);
            assert(zeros8(0) + unz(e, 0) =~= unz(e, 0));
            assert(unz(e, 1) =~= seq![e[0]] + unz(e.skip(1), 0));
            assert(unz(e, 0) =~= seq![e[0]] + unz(e.skip(1), 0));
            assert(zeros8(1) =~= seq![0u8]);
        } else {
            lemma_unesc_unz(e.skip(1), 2);
            assert(zeros8(2) + e.skip(1) =~= ze);
            assert(zeros8(2) + unz(e.skip(1), 2) =~= zeros8(1) + (seq![e[0]] + unz(e.skip(1), znext(1, e[0]))));
        }
    } else {
        assert(zeros8(2) =~= seq![0u8, 0u8]);
        if e[0] == 3 {
            assert(ze.skip(3) =~= e.skip(1));
            lemma_unesc_unz(e.skip(1), 0);
            assert(zeros8(0) + e.skip(1) =~= e.skip(1));
            assert(zeros8(0) + unz(e.skip(1), 0) =~= unz(e.skip(1), 0));
        } else if e[0] == 0 {
            // 0 0 0 ...: no pattern at the first zero
            assert(ze.skip(1) =~= zeros8(2) + e.skip(1));
            assert(unesc(ze) =~= seq![0u8] + unesc(ze.skip(1)));
            lemma_unesc_unz(e.skip(1), 2);
            assert(zeros8(2) + unz(e, 2) =~= seq![0u8] + (zeros8(2) + unz(e.skip(1), 2)));
        } else {
            // 0 0 x ... with x ∉ {0, 3}
            let x = e[0];
            let e1 = e.skip(1);
            assert(ze.skip(1) =~= seq![0u8, x] + e1);
            assert(unesc(ze) =~= seq![0u8] + unesc(seq![0u8, x] + e1));
            assert((seq![0u8, x] + e1).skip(1) =~= seq![x] + e1);
            assert(unesc(seq![0u8, x] + e1) =~= seq![0u8] + unesc(seq![x] + e1));
            assert((seq![x] + e1).skip(1) =~= e1);
            assert(unesc(seq![x] + e1) =~= seq![x] + unesc(e1));
            lemma_unesc_unz(e1, 0);
            assert(zeros8(0) + e1 =~= e1);
            assert(zeros8(0) + unz(e1, 0) =~= unz(e1, 0));
        }
    }
}

pub proof fn lemma_unesc_is_unz(e: Seq<u8>)
    ensures unesc(e) == unz(e, 0),
{
    lemma_unesc_unz(e, 0);
    assert(zeros8(0) + e =~= e);
    assert(zeros8(0) + unz(e, 0) =~= unz(e, 0));
}

proof fn lemma_unz_esc(r: Seq<u8>, z: nat)
    requires z <= 2,
    ensures unz(esc(r, z), z) == r,
    decreases r.len(),
{
    if r.len() == 0 {
        if z >= 2 {
            assert(seq![3u8].skip(1) =~= Seq::<u8>::empty());
            assert(esc(r, z) == seq![3u8]);
            assert(unz(seq![3u8], z) == unz(Seq::<u8>::empty(), 0));
        } else {
            assert(esc(r, z) == Seq::<u8>::empty());
        }
        assert(r =~= Seq::<u8>::empty());
        assert(unz(esc(r, z), z) == r);
    } else if z >= 2 && r[0] <= 3 {
        let x = r[0];
        let tail = esc(r.skip(1), znext(0, x));
        lemma_unz_esc(r.skip(1), znext(0, x));
        let e = seq![3u8, x] + tail;
        assert(esc(r, z) == e);
        assert(e.skip(1) =~= seq![x] + tail);
        assert((seq![x] + tail).skip(1) =~= tail);
        assert(unz(e, z) == unz(e.skip(1), 0));
        assert(unz(seq![x] + tail, 0) == seq![x] + unz(tail, znext(0, x)));
        assert(r =~= seq![x] + r.skip(1));
        assert(unz(esc(r, z), z) == r);
    } else {
        let x = r[0];
        let tail = esc(r.skip(1), znext(z, x));
        lemma_unz_esc(r.skip(1), znext(z, x));
        let e = seq![x] + tail;
        assert(esc(r, z) == e);
        assert(e.skip(1) =~= tail);
        assert(e[0] == x);
        assert(unz(e, z) == seq![x] + unz(tail, znext(z, x)));
        assert(r =~= seq![x] + r.skip(1));
        assert(unz(esc(r, z), z) == r);
    }
}

/// Unescaping an escaped RBSP gives it back.
pub proof fn theorem_esc_rt(r: Seq<u8>)
    ensures unesc(esc(r, 0)) == r,
{
    lemma_unesc_is_unz(esc(r, 0));
    lemma_unz_esc(r, 0);
}

/// Payload bytes a decoder in state `z` can meet in a conforming NAL unit.
pub open spec fn ok_z(e: Seq<u8>, z: nat) -> bool
    decreases e.len(),
{
    if e.len() == 0 {
        z == 0
    } else if z >= 2 {
        if e[0] == 3 {
            (e.len() == 1 || e[1] <= 3) && ok_z(e.skip(1), 0)
        } else {
            e[0] > 3 && ok_z(e.skip(1), 0)
        }
    } else {
        ok_z(e.skip(1), znext(z, e[0]))
    }
}

proof fn lemma_esc_unz(e: Seq<u8>, z: nat)
    requires z <= 2, ok_z(e, z),
    ensures esc(unz(e, z), z) == e,
    decreases e.len(),
{
    if e.len() == 0 {
    } else if z >= 2 && e[0] == 3 {
        let e1 = e.skip(1);
        if e1.len() == 0 {
            assert(e =~= seq![3u8]);
        } else {
            let x = e1[0];
            assert(ok_z(e1, 0));
            assert(ok_z(e1.skip(1), znext(0, x)));
            lemma_esc_unz(e1.skip(1), znext(0, x));
            assert(unz(e1, 0) =~= seq![x] + unz(e1.skip(1), znext(0, x)));
            let u = unz(e1.skip(1), znext(0, x));
            assert((seq![x] + u).skip(1) =~= u);
            assert(e =~= seq![3u8, x] + e1.skip(1));
        }
    } else {
        let x = e[0];
        lemma_esc_unz(e.skip(1), znext(z, x));
        let u = unz(e.skip(1), znext(z, x));
        assert((seq![x] + u).skip(1) =~= u);
        assert(e =~= seq![x] + e.skip(1));
    }
}

/// The payload of a conforming NAL unit meets `ok_z` from state 0.
proof fn lemma_nal_ok_z(n: Seq<u8>, i: nat, z: nat)
    requires
        nal_ok(n), i <= n.len(), z <= 2,
        z >= 1 ==> i >= 1 && n[i - 1] == 0,
        z >= 2 ==> i >= 2 && n[i - 2] == 0,
    ensures ok_z(n.skip(i as int), z),
    decreases n.len() - i,
{
    let e = n.skip(i as int);
    if i == n.len() {
        if z >= 1 {
            assert(n.last() == n[i - 1]);
        }
    } else if z >= 2 {
        assert(ok_at(n, i - 2));
        assert(!(n[i - 2] == 0 && n[i - 1] == 0 && n[i as int] <= 2));
        if n[i as int] == 3 {
            if i + 1 < n.len() {
                assert(n[(i - 2) + 3] <= 3);
                assert(e[1] == n[i + 1int]);
            }
            lemma_nal_ok_z(n, i + 1, 0);
            assert(e.skip(1) =~= n.skip(i + 1int));
        } else {
            lemma_nal_ok_z(n, i + 1, 0);
            assert(e.skip(1) =~= n.skip(i + 1int));
        }
    } else {
        lemma_nal_ok_z(n, i + 1, znext(z, n[i as int]));
        assert(e.skip(1) =~= n.skip(i + 1int));
    }
}

/// A conforming NAL unit's payload is the escaping of what it unescapes to.
pub proof fn theorem_esc_inv(n: Seq<u8>, hl: nat)
    requires nal_ok(n), hl <= n.len(),
    ensures esc(unesc(n.skip(hl as int)), 0) == n.skip(hl as int),
{
    lemma_nal_ok_z(n, hl, 0);
    lemma_unesc_is_unz(n.skip(hl as int));
    lemma_esc_unz(n.skip(hl as int), 0);
}

// ------------------------------------------------------------------- exec

/// `unesc` of `n` from byte `from`.
pub fn unescape_x(n: &[u8], from: usize) -> (r: Vec<u8>)
    requires from <= n@.len(),
    ensures r@ == unesc(n@.skip(from as int)),
{
    let ghost e0 = n@.skip(from as int);
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = from;
    let mut z: usize = 0;
    proof { lemma_unesc_is_unz(e0); assert(n@.skip(i as int) =~= e0); }
    while i < n.len()
        invariant
            from <= i <= n@.len(), z <= 2,
            e0 == n@.skip(from as int),
            unesc(e0) == out@ + unz(n@.skip(i as int), z as nat),
        decreases n@.len() - i,
    {
        let x = n[i];
        let ghost e = n@.skip(i as int);
        proof { assert(e.skip(1) =~= n@.skip(i as int + 1)); }
        if z >= 2 && x == 3 {
            z = 0;
        } else {
            proof { assert(out@ + (seq![x] + unz(e.skip(1), znext(z as nat, x))) =~= out@.push(x) + unz(e.skip(1), znext(z as nat, x))); }
            out.push(x);
            z = if x == 0 { if z >= 2 { 2 } else { z + 1 } } else { 0 };
        }
        i = i + 1;
    }
    proof { assert(out@ + Seq::<u8>::empty() =~= out@); }
    out
}

/// Append `esc(r, 0)` to `out`.
pub fn escape_x(r: &[u8], out: &mut Vec<u8>)
    ensures final(out)@ == old(out)@ + esc(r@, 0),
{
    let mut i: usize = 0;
    let mut z: usize = 0;
    proof { assert(r@.skip(0) =~= r@); assert(old(out)@ + esc(r@, 0) =~= out@ + esc(r@.skip(0), 0)); }
    while i < r.len()
        invariant
            i <= r@.len(), z <= 2,
            old(out)@ + esc(r@, 0) == out@ + esc(r@.skip(i as int), z as nat),
        decreases r@.len() - i,
    {
        let x = r[i];
        let ghost t = r@.skip(i as int);
        proof { assert(t.skip(1) =~= r@.skip(i as int + 1)); }
        if z >= 2 && x <= 3 {
            proof { assert(out@ + (seq![3u8, x] + esc(t.skip(1), znext(0, x))) =~= out@.push(3u8).push(x) + esc(t.skip(1), znext(0, x))); }
            out.push(3);
            out.push(x);
            z = if x == 0 { 1 } else { 0 };
        } else {
            proof { assert(out@ + (seq![x] + esc(t.skip(1), znext(z as nat, x))) =~= out@.push(x) + esc(t.skip(1), znext(z as nat, x))); }
            out.push(x);
            z = if x == 0 { if z >= 2 { 2 } else { z + 1 } } else { 0 };
        }
        i = i + 1;
    }
    if z >= 2 {
        proof { assert(out@ + seq![3u8] =~= out@.push(3u8)); }
        out.push(3);
    } else {
        proof { assert(out@ + Seq::<u8>::empty() =~= out@); }
    }
}

pub fn nal_ok_x(n: &[u8]) -> (ok: bool)
    ensures ok == nal_ok(n@),
{
    if n.len() == 0 || n[n.len() - 1] == 0 {
        return false;
    }
    if n.len() < 3 {
        return true;
    }
    let mut i: usize = 0;
    while i < n.len() - 2
        invariant
            n@.len() >= 3, i <= n@.len() - 2,
            forall|j: int| 0 <= j < i ==> #[trigger] ok_at(n@, j),
        decreases n@.len() - i,
    {
        if n[i] == 0 && n[i + 1] == 0 {
            if n[i + 2] <= 2 {
                proof { assert(!ok_at(n@, i as int)); }
                return false;
            }
            if n[i + 2] == 3 && i + 3 < n.len() && n[i + 3] > 3 {
                proof { assert(!ok_at(n@, i as int)); }
                return false;
            }
        }
        proof { assert(ok_at(n@, i as int)); }
        i = i + 1;
    }
    true
}

} // verus!
