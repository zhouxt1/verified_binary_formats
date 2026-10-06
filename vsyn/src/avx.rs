//! Executable reading and writing of AV1's descriptors (`avd`), proved
//! equal to their spec codes.
use vstd::prelude::*;
use vbits::bitspec::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::prim_write::{bits_seq, lemma_bits_seq_val};
use crate::eg::*;
use crate::avd::*;
use crate::bits::*;

verus! {

/// `leb_parse` from byte `i`, after `t` has been read from bytes before it.
pub open spec fn lcat7(r: Option<(nat, nat)>, t: nat, i: nat) -> Option<(nat, nat)> {
    match r {
        Some((v, k)) => Some((t + p2(7 * i) * v, k + i)),
        None => None,
    }
}

/// `le_parse` of the bytes left, after `t` has been read from `i` before.
pub open spec fn lcat8(r: Option<(nat, nat)>, t: nat, i: nat) -> Option<(nat, nat)> {
    match r {
        Some((v, k)) => Some((t + p2(8 * i) * v, k + 8 * i)),
        None => None,
    }
}

proof fn lemma_p2_step(a: nat, b: nat)
    ensures p2(a + b) == p2(a) * p2(b),
{
    lemma_p2_adds(a, b);
}

proof fn lemma_p2_consts()
    ensures p2(1) == 2, p2(7) == 128, p2(8) == 256,
{
    reveal_with_fuel(p2, 9);
}

pub fn pow2_u64(n: usize) -> (r: u64)
    requires n <= 63,
    ensures r as nat == p2(n as nat),
{
    proof {
        vbits::prim_read::lemma_p2_eq_pow2(n as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(n as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, n as u64);
    }
    1u64 << (n as u64)
}

/// The fewest bytes a `leb128()` of `v` takes.
pub fn leb_min_x(v: u64) -> (r: usize)
    ensures r as nat == leb_min(v as nat), 1 <= r <= 10,
{
    let mut x = v;
    let mut r: usize = 1;
    proof { lemma_leb_min_bound(v as nat); }
    while x >= 128
        invariant r >= 1, r + leb_min(x as nat) == leb_min(v as nat) + 1, leb_min(v as nat) <= 10,
        decreases x,
    {
        x = x / 128;
        r = r + 1;
    }
    r
}

proof fn lemma_leb_min_bound(v: nat)
    requires v <= u64::MAX,
    ensures leb_min(v) <= 10,
{
    vbits::prim_read::lemma_p2_64();
    vbits::prim_read::lemma_p2_mono(64, 70);
    lemma_leb_min(v, 10);
}

impl<'a> Reader<'a> {
    pub fn read_su(&mut self, n: usize) -> (res: Option<i64>)
        requires old(self).wf(), 1 <= n <= 48,
        ensures
            final(self).wf(), final(self).same(*old(self)),
            match su_parse(old(self).rem(), n as nat) {
                Some((v, k)) => res == Some(v as i64) && final(self).pos == old(self).pos + k,
                None => res is None,
            },
    {
        let x = match self.read_nbit(n) {
            Some(x) => x,
            None => { return None; }
        };
        proof {
            vbits::prim_read::lemma_p2_mono(n as nat, 48);
            crate::xir::lemma_p2_48();
            lemma_bits_val_bound(old(self).rem().take(n as int));
        }
        let half = pow2_u64(n - 1);
        let full = pow2_u64(n);
        if x >= half { Some(x as i64 - full as i64) } else { Some(x as i64) }
    }

    pub fn read_ns(&mut self, n: u64) -> (res: Option<u64>)
        requires old(self).wf(), 1 <= n <= 1099511627776u64,
        ensures
            final(self).wf(), final(self).same(*old(self)),
            match ns_parse(old(self).rem(), n as nat) {
                Some((v, k)) => res == Some(v as u64) && final(self).pos == old(self).pos + k,
                None => res is None,
            },
    {
        let ghost s = old(self).rem();
        let l = ilog2_x(n);
        proof { lemma_ilog2_40(n as nat); }
        let w = l + 1;
        let pw = pow2_u64(w);
        proof { lemma_ilog2(n as nat); }
        let m = pw - n;
        let v = match self.read_nbit(w - 1) {
            Some(v) => v,
            None => { return None; }
        };
        if v < m {
            return Some(v);
        }
        let ghost s1 = self.rem();
        let e = match self.read_nbit(1) {
            Some(e) => e,
            None => {
                proof { assert(s.len() < w); }
                return None;
            }
        };
        proof {
            let t = s.take(w as int);
            assert(t.take((w - 1) as int) =~= s.take((w - 1) as int));
            assert(t.skip((w - 1) as int) =~= s1.take(1));
            lemma_split_last_pub(t);
            lemma_p2_consts();
            vbits::prim_read::lemma_p2_mono(w as nat, 48);
            crate::xir::lemma_p2_48();
            lemma_bits_val_bound(s1.take(1));
            lemma_bits_val_bound(s.take((w - 1) as int));
            vbits::prim_read::lemma_p2_mono((w - 1) as nat, 48);
        }
        let y = 2 * v + e;
        Some(y - m)
    }

    pub fn read_le(&mut self, n: usize) -> (res: Option<u64>)
        requires old(self).wf(), n <= 6,
        ensures
            final(self).wf(), final(self).same(*old(self)),
            match le_parse(old(self).rem(), n as nat) {
                Some((v, k)) => res == Some(v as u64) && final(self).pos == old(self).pos + k,
                None => res is None,
            },
    {
        let ghost s = old(self).rem();
        let p0 = self.pos;
        let mut t: u64 = 0;
        let mut i: usize = 0;
        proof {
            assert(s.skip(0) =~= s);
            assert(p2(0) == 1);
        }
        while i < n
            invariant
                self.wf(), self.same(*old(self)), s == old(self).rem(), p0 == old(self).pos,
                i <= n, n <= 6,
                self.pos == p0 + 8 * i,
                self.rem() =~= s.skip(8 * i as int),
                (t as nat) < p2(8 * i as nat),
                le_parse(s, n as nat) == lcat8(le_parse(s.skip(8 * i as int), (n - i) as nat), t as nat, i as nat),
            decreases n - i,
        {
            let ghost cur = self.rem();
            let b = match self.read_nbit(8) {
                Some(b) => b,
                None => { return None; }
            };
            proof {
                lemma_p2_consts();
                lemma_bits_val_bound(cur.take(8));
                assert(cur.skip(8) =~= s.skip(8 * (i + 1) as int));
                lemma_p2_step(8 * i as nat, 8);
                assert(8 * i as nat + 8 == 8 * (i + 1) as nat);
                vbits::prim_read::lemma_p2_mono(8 * (i + 1) as nat, 48);
                crate::xir::lemma_p2_48();
                let bb = b as nat;
                let tt = t as nat;
                let q = p2(8 * i as nat);
                match le_parse(cur.skip(8), (n - i - 1) as nat) {
                    Some((r, k)) => {
                        assert(tt + q * (bb + 256 * r) == (tt + q * bb) + (q * 256) * r) by (nonlinear_arith);
                    }
                    None => {}
                }
                assert(tt + q * bb < q * 256) by (nonlinear_arith) requires tt < q, bb < 256;
            }
            let sh = pow2_u64(8 * i);
            t = t + sh * b;
            i = i + 1;
        }
        proof {
            assert(((n - i) as nat) == 0nat);
            vbits::prim_read::lemma_p2_mono(8 * i as nat, 48);
            crate::xir::lemma_p2_48();
            assert(le_parse(s.skip(8 * i as int), 0) == Some((0nat, 0nat)));
            assert(p2(8 * i as nat) * 0 == 0);
            assert(le_parse(s, n as nat) == Some((t as nat, 8 * n as nat)));
        }
        Some(t)
    }

    /// `uvlc()`: the value and the choice (the leading zeros past 32).
    pub fn read_uvlc(&mut self) -> (res: Option<(u64, u64)>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).same(*old(self)),
            match uvlc_parse(old(self).rem()) {
                Some((v, w, k)) => res == Some((v as u64, w as u64)) && final(self).pos == old(self).pos + k,
                None => res is None,
            },
    {
        let ghost s = old(self).rem();
        let p0 = self.pos;
        let mut l: usize = 0;
        loop
            invariant_except_break
                self.pos == p0 + l,
                self.rem() =~= s.skip(l as int),
            invariant
                self.wf(), self.same(*old(self)),
                p0 == old(self).pos,
                s == old(self).rem(),
                l <= s.len(),
                forall|j: int| 0 <= j < l ==> !s[j],
            ensures
                l < s.len(), s[l as int],
                self.pos == p0 + l + 1,
                self.rem() =~= s.skip(l as int + 1),
            decreases s.len() - l,
        {
            let ghost r = self.rem();
            match self.read_nbit(1) {
                None => {
                    proof {
                        lemma_first_one_none(s, 0, 32);
                        lemma_first_one_none(s, 32, s.len());
                    }
                    return None;
                }
                Some(bit) => {
                    proof {
                        assert(r.take(1) =~= seq![r[0]]);
                        lemma_bits_val_one(r[0]);
                        assert(r[0] == s[l as int]);
                        assert(self.rem() =~= s.skip(l as int + 1));
                    }
                    if bit == 1 {
                        break;
                    }
                    l = l + 1;
                }
            }
        }
        if l >= 32 {
            proof {
                lemma_first_one_none(s, 0, 32);
                lemma_first_one_at(s, 32, s.len(), l as nat);
            }
            return Some((4294967295u64, (l - 32) as u64));
        }
        proof { lemma_first_one_at(s, 0, 32, l as nat); }
        if l > self.end - self.pos {
            return None;
        }
        let ghost r = self.rem();
        let x = match self.read_nbit(l) {
            Some(x) => x,
            None => { return None; }
        };
        proof {
            let t = s.subrange(l as int, (2 * l + 1) as int);
            lemma_bits_val_split(t, 1);
            assert(t.take(1) =~= seq![true]);
            lemma_bits_val_one(true);
            assert(t.skip(1) =~= r.take(l as int));
            assert(((t.len() - 1) as nat) == l);
            lemma_p2_32();
            vbits::prim_read::lemma_p2_mono(l as nat, 31);
            lemma_bits_val_bound(r.take(l as int));
        }
        let pw: u64 = pow2_u64(l);
        Some((pw - 1 + x, 0))
    }

    /// `leb128()`: the value and the choice (the bytes past the fewest).
    pub fn read_leb128(&mut self) -> (res: Option<(u64, u64)>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).same(*old(self)),
            match leb_parse(old(self).rem(), 0) {
                Some((v, k)) => if v <= uvlc_max() {
                    res == Some((v as u64, (k - leb_min(v)) as u64)) && final(self).pos == old(self).pos + 8 * k
                } else {
                    res is None
                },
                None => res is None,
            },
    {
        let ghost s = old(self).rem();
        let p0 = self.pos;
        let mut t: u64 = 0;
        let mut i: usize = 0;
        proof {
            assert(s.skip(0) =~= s);
            assert(p2(0) == 1);
        }
        loop
            invariant
                self.wf(), self.same(*old(self)), s == old(self).rem(), p0 == old(self).pos,
                i <= 8,
                self.pos == p0 + 8 * i,
                self.rem() =~= s.skip(8 * i as int),
                (t as nat) < p2(7 * i as nat),
                leb_parse(s, 0) == lcat7(leb_parse(s.skip(8 * i as int), i as nat), t as nat, i as nat),
            decreases 8 - i,
        {
            if i == 8 {
                return None;
            }
            let ghost cur = self.rem();
            let b = match self.read_nbit(8) {
                Some(b) => b,
                None => { return None; }
            };
            proof {
                lemma_p2_consts();
                lemma_bits_val_bound(cur.take(8));
                assert(cur.skip(8) =~= s.skip(8 * (i + 1) as int));
                lemma_p2_step(7 * i as nat, 7);
                assert(7 * i as nat + 7 == 7 * (i + 1) as nat);
                vbits::prim_read::lemma_p2_mono(7 * (i + 1) as nat, 56);
                vbits::prim_read::lemma_p2_56();
            }
            let sh = pow2_u64(7 * i);
            if b < 128 {
                proof {
                    let q = p2(7 * i as nat);
                    assert((t as nat) + q * (b as nat) < q * 128) by (nonlinear_arith)
                        requires (t as nat) < q, (b as nat) < 128;
                }
                let v = t + sh * b;
                let k = i + 1;
                if v > 4294967295u64 {
                    return None;
                }
                let lm = leb_min_x(v);
                proof {
                    lemma_leb_min(v as nat, k as nat);
                    assert(v as nat == (t as nat) + p2(7 * i as nat) * (b as nat));
                }
                return Some((v, (k - lm) as u64));
            }
            proof {
                let q = p2(7 * i as nat);
                let bb = (b - 128) as nat;
                let tt = t as nat;
                match leb_parse(cur.skip(8), (i + 1) as nat) {
                    Some((r, k)) => {
                        assert(tt + q * (bb + 128 * r) == (tt + q * bb) + (q * 128) * r) by (nonlinear_arith);
                    }
                    None => {}
                }
                assert(tt + q * bb < q * 128) by (nonlinear_arith) requires tt < q, bb < 128;
            }
            t = t + sh * (b - 128);
            i = i + 1;
        }
    }
}

/// `lemma_split_last`, for the reader.
pub proof fn lemma_split_last_pub(t: Seq<bool>)
    requires t.len() >= 1,
    ensures
        bits_val(t) == 2 * bits_val(t.take(t.len() - 1)) + bits_val(t.skip(t.len() - 1)),
        bits_val(t.skip(t.len() - 1)) < 2,
{
    lemma_bits_val_split(t, t.len() - 1);
    assert(((t.len() - (t.len() - 1)) as nat) == 1nat);
    lemma_p2_consts();
    lemma_bits_val_bound(t.skip(t.len() - 1));
}

pub proof fn lemma_ilog2_40(n: nat)
    requires 1 <= n <= 1099511627776nat,
    ensures ilog2(n) <= 40, ns_w(n) <= 41, p2(40) == 1099511627776nat,
{
    lemma_ilog2(n);
    crate::xir::lemma_p2_48();
    lemma_p2_32();
    assert(p2(40) == 1099511627776nat) by {
        reveal_with_fuel(p2, 9);
        assert(p2(8) == 256);
        lemma_p2_adds(32, 8);
    }
    if ilog2(n) > 40 {
        lemma_p2_mono_strict(40, ilog2(n));
    }
}

impl Writer {
    pub fn write_su(&mut self, n: usize, v: i64) -> (ok: bool)
        requires old(self).wf(), 1 <= n <= 48, su_in(v as int, n as nat),
        ensures
            ok ==> final(self).wf(),
            ok ==> final(self).written() =~= old(self).written() + su_code(v as int, n as nat)
                   && final(self).pos == old(self).pos + n,
    {
        let full = pow2_u64(n);
        proof {
            assert(p2(n as nat) == 2 * p2((n - 1) as nat)) by { reveal_with_fuel(p2, 2); }
            vbits::prim_read::lemma_p2_mono(n as nat, 48);
            crate::xir::lemma_p2_48();
        }
        let u: u64 = if v < 0 { (v + full as i64) as u64 } else { v as u64 };
        self.write_nbit(n, u)
    }

    pub fn write_ns(&mut self, n: u64, x: u64) -> (ok: bool)
        requires old(self).wf(), 1 <= n <= 1099511627776u64, x < n,
        ensures
            ok ==> final(self).wf(),
            ok ==> final(self).written() =~= old(self).written() + ns_code(x as nat, n as nat)
                   && final(self).pos == old(self).pos + ns_code(x as nat, n as nat).len(),
    {
        let l = ilog2_x(n);
        proof { lemma_ilog2_40(n as nat); lemma_ilog2(n as nat); }
        let w = l + 1;
        let pw = pow2_u64(w);
        let m = pw - n;
        proof {
            assert(p2(w as nat) == 2 * p2((w - 1) as nat)) by { reveal_with_fuel(p2, 2); }
        }
        if x < m {
            self.write_nbit(w - 1, x)
        } else {
            self.write_nbit(w, x + m)
        }
    }

    pub fn write_le(&mut self, n: usize, v: u64) -> (ok: bool)
        requires old(self).wf(), n <= 6, (v as nat) < p2(8 * n as nat),
        ensures
            ok ==> final(self).wf(),
            ok ==> final(self).written() =~= old(self).written() + le_code(v as nat, n as nat)
                   && final(self).pos == old(self).pos + 8 * n,
    {
        let mut cur = v;
        let mut i: usize = 0;
        proof { lemma_le_len(v as nat, n as nat); }
        while i < n
            invariant
                self.wf(), i <= n, n <= 6,
                old(self).written() + le_code(v as nat, n as nat) =~= self.written() + le_code(cur as nat, (n - i) as nat),
                self.pos == old(self).pos + 8 * i,
            decreases n - i,
        {
            proof {
                lemma_p2_consts();
                assert(le_code(cur as nat, (n - i) as nat)
                       =~= u_code((cur as nat) % 256, 8) + le_code((cur as nat) / 256, (n - i - 1) as nat));
            }
            if !self.write_nbit(8, cur % 256) {
                return false;
            }
            cur = cur / 256;
            i = i + 1;
        }
        proof { assert(le_code(cur as nat, 0) =~= Seq::<bool>::empty()); }
        true
    }

    /// `uvlc()` of `v`, with `w` leading zeros past 32 when it is 2^32 − 1.
    pub fn write_uvlc(&mut self, v: u64, w: u64) -> (ok: bool)
        requires old(self).wf(), uvlc_code(v as nat, w as nat) is Some,
        ensures
            ok ==> final(self).wf(),
            ok ==> final(self).written() =~= old(self).written() + uvlc_code(v as nat, w as nat).unwrap()
                   && final(self).pos == old(self).pos + uvlc_code(v as nat, w as nat).unwrap().len(),
    {
        if v <= 4294967294 && w == 0 {
            return self.write_ue(v);
        }
        if w > 1000000000 {
            return false;
        }
        let total: u64 = 32 + w;
        let mut done: u64 = 0;
        proof { assert(zeros(0) =~= Seq::<bool>::empty()); }
        while done < total
            invariant
                self.wf(), done <= total, total == 32 + w,
                self.written() =~= old(self).written() + zeros(done as nat),
                self.pos == old(self).pos + done,
            decreases total - done,
        {
            let k: u64 = if total - done > 32 { 32 } else { total - done };
            proof {
                lemma_zeros_bits_seq(k as nat);
                lemma_p2_pos(k as nat);
                assert(zeros(done as nat) + zeros(k as nat) =~= zeros((done + k) as nat));
            }
            if !self.write_nbit(k as usize, 0) {
                return false;
            }
            done = done + k;
        }
        proof {
            lemma_p2_consts();
            assert(p2(0) == 1);
            assert(((1 - 1 - 0) as nat) == 0nat);
            assert((1u64 as nat) / p2(0) % 2 == 1);
            assert(bits_seq(1u64, 1)[0]);
            assert(bits_seq(1u64, 1) =~= seq![true]);
        }
        self.write_nbit(1, 1)
    }

    /// `leb128()` of `v` in the fewest bytes plus `w`.
    pub fn write_leb128(&mut self, v: u64, w: u64) -> (ok: bool)
        requires old(self).wf(), v <= uvlc_max(), leb_min(v as nat) + w <= 8,
        ensures
            ok ==> final(self).wf(),
            ok ==> final(self).written() =~= old(self).written() + leb_code(v as nat, leb_min(v as nat) + w as nat)
                   && final(self).pos == old(self).pos + 8 * (leb_min(v as nat) + w as nat),
    {
        let lm = leb_min_x(v);
        let k: usize = lm + w as usize;
        proof {
            lemma_leb_min(v as nat, k as nat);
            lemma_leb_len(v as nat, k as nat);
        }
        let mut cur = v;
        let mut i: usize = 0;
        while i < k
            invariant
                self.wf(), i <= k, 1 <= k <= 8,
                i < k ==> (cur as nat) < p2(7 * (k - i) as nat),
                old(self).written() + leb_code(v as nat, k as nat) =~= self.written() + (if i < k { leb_code(cur as nat, (k - i) as nat) } else { Seq::<bool>::empty() }),
                self.pos == old(self).pos + 8 * i,
            decreases k - i,
        {
            proof {
                lemma_p2_consts();
                lemma_p2_step(7 * (k - i - 1) as nat, 7);
                assert(7 * (k - i - 1) as nat + 7 == 7 * (k - i) as nat);
                lemma_p2_pos(7 * (k - i - 1) as nat);
            }
            if i + 1 < k {
                proof {
                    assert(leb_code(cur as nat, (k - i) as nat)
                           =~= u_code(128 + (cur as nat) % 128, 8) + leb_code((cur as nat) / 128, (k - i - 1) as nat));
                    assert((cur as nat) / 128 < p2(7 * (k - i - 1) as nat)) by (nonlinear_arith)
                        requires (cur as nat) < p2(7 * (k - i - 1) as nat) * 128;
                }
                if !self.write_nbit(8, 128 + cur % 128) {
                    return false;
                }
                cur = cur / 128;
            } else {
                proof {
                    assert(leb_code(cur as nat, 1) =~= u_code(cur as nat, 8));
                    assert(7 * 1 == 7);
                }
                if !self.write_nbit(8, cur) {
                    return false;
                }
            }
            i = i + 1;
        }
        true
    }
}

proof fn lemma_le_len(v: nat, n: nat)
    ensures le_code(v, n).len() == 8 * n,
    decreases n,
{
    if n > 0 { lemma_le_len(v / 256, (n - 1) as nat); }
}

proof fn lemma_leb_len(v: nat, k: nat)
    ensures leb_code(v, k).len() == 8 * (if k == 0 { 1 } else { k }),
    decreases k,
{
    if k > 1 { lemma_leb_len(v / 128, (k - 1) as nat); }
}

} // verus!
