//! Executable reading and writing of the descriptors, against `eg`'s codes.
//! A `Reader` reads from a window of a byte buffer that ends at any bit
//! (a parameter set's data ends where its trailing bits begin); a `Writer`
//! appends to a growing buffer.
use vstd::prelude::*;
use vbits::bitspec::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::prim_write::{bits_seq, lemma_bits_seq_val, lemma_bits_seq_of_val};
use crate::eg::*;
use crate::ir::*;

verus! {

pub proof fn lemma_bview_in_range(s: Seq<u8>, i: int, j: int)
    requires 0 <= i <= j <= 8 * s.len(),
    ensures bview(s).subrange(i, j) =~= bits_of(s).subrange(i, j),
{
}

pub proof fn lemma_bits_val_one(x: bool)
    ensures bits_val(seq![x]) == (if x { 1nat } else { 0nat }),
{
    reveal_with_fuel(bits_val, 2);
    assert(seq![x].drop_last() =~= Seq::<bool>::empty());
}

pub proof fn lemma_zeros_bits_seq(n: nat)
    requires n <= 64,
    ensures zeros(n) =~= bits_seq(0u64, n),
{
    assert forall|i: int| 0 <= i < n implies zeros(n)[i] == bits_seq(0u64, n)[i] by {
        lemma_p2_pos((n - 1 - i) as nat);
    }
}

pub proof fn lemma_first_one_none(s: Seq<bool>, i: nat, lim: nat)
    requires forall|j: int| i <= j < lim && j < s.len() ==> !s[j],
    ensures first_one(s, i, lim) is None,
    decreases lim - i,
{
    if i < lim && i < s.len() {
        lemma_first_one_none(s, i + 1, lim);
    }
}

// ------------------------------------------------------------------ reader

pub struct Reader<'a> {
    pub buf: &'a [u8],
    pub pos: usize,
    /// The bit the window ends at.
    pub end: usize,
}

impl<'a> Reader<'a> {
    pub open spec fn wf(self) -> bool {
        &&& self.pos <= self.end
        &&& self.end <= 8 * self.buf@.len()
        &&& 8 * self.buf@.len() <= usize::MAX
    }

    /// The window: the bits the syntax structure is read from.
    pub open spec fn win(self) -> Seq<bool> {
        bits_of(self.buf@).take(self.end as int)
    }

    /// The bits still to be read.
    pub open spec fn rem(self) -> Seq<bool> {
        self.win().skip(self.pos as int)
    }

    pub open spec fn same(self, o: Self) -> bool {
        self.buf == o.buf && self.end == o.end
    }

    pub fn new(buf: &'a [u8], end: usize) -> (r: Reader<'a>)
        requires end <= 8 * buf@.len(), 8 * buf@.len() <= usize::MAX,
        ensures r.wf(), r.buf == buf, r.pos == 0, r.end == end,
    {
        Reader { buf, pos: 0, end }
    }

    /// An `n`-bit unsigned field, `n` from 0 to 56.
    pub fn read_nbit(&mut self, n: usize) -> (res: Option<u64>)
        requires old(self).wf(), n <= 56,
        ensures
            final(self).wf(), final(self).same(*old(self)),
            match res {
                Some(v) => {
                    &&& n <= old(self).rem().len()
                    &&& v as nat == bits_val(old(self).rem().take(n as int))
                    &&& final(self).pos == old(self).pos + n
                },
                None => n > old(self).rem().len() && final(self).pos == old(self).pos,
            },
    {
        if n > self.end - self.pos {
            return None;
        }
        if n == 0 {
            assert(old(self).rem().take(0) =~= Seq::<bool>::empty());
            return Some(0);
        }
        let v = vbits::fastload::read_bits_fast(self.buf, self.pos, n);
        proof {
            lemma_bview_in_range(self.buf@, self.pos as int, self.pos as int + n as int);
            assert(old(self).rem().take(n as int)
                   =~= bits_of(self.buf@).subrange(self.pos as int, self.pos as int + n as int));
        }
        self.pos = self.pos + n;
        Some(v)
    }

    pub fn read_ue(&mut self) -> (res: Option<u64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).same(*old(self)),
            match ue_parse(old(self).rem()) {
                Some((v, k)) => res == Some(v as u64) && final(self).pos == old(self).pos + k && v <= ue_max(),
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
                l <= 32, l <= s.len(),
                forall|j: int| 0 <= j < l ==> !s[j],
            ensures
                l < 32, l < s.len(), s[l as int],
                self.pos == p0 + l + 1,
                self.rem() =~= s.skip(l as int + 1),
            decreases 32 - l,
        {
            if l == 32 {
                proof { lemma_first_one_none(s, 0, 32); }
                return None;
            }
            let ghost r = self.rem();
            match self.read_nbit(1) {
                None => {
                    proof { lemma_first_one_none(s, 0, 32); }
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
        proof {
            lemma_first_one_at(s, 0, 32, l as nat);
        }
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
        let pw: u64 = 1u64 << (l as u64);
        proof {
            vbits::prim_read::lemma_p2_eq_pow2(l as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, l as u64);
            vstd::bits::lemma_u64_pow2_no_overflow(l as nat);
        }
        Some(pw - 1 + x)
    }

    pub fn read_se(&mut self) -> (res: Option<i64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).same(*old(self)),
            match se_parse(old(self).rem()) {
                Some((v, k)) => res == Some(v as i64) && final(self).pos == old(self).pos + k,
                None => res is None,
            },
    {
        let k = match self.read_ue() {
            Some(k) => k,
            None => { return None; }
        };
        proof { lemma_se_map_inv(k as nat); }
        if k % 2 == 1 { Some(((k + 1) / 2) as i64) } else { Some(-((k / 2) as i64)) }
    }

    /// A 0xFF-byte-coded value, as `dparse(DV::FF, ...)` reads it.
    pub fn read_ff(&mut self) -> (res: Option<u64>)
        requires old(self).wf(),
        ensures
            final(self).wf(), final(self).same(*old(self)),
            match dparse(DV::FF, old(self).rem()) {
                Some((v, _, k)) => res == Some(v as u64) && final(self).pos == old(self).pos + k,
                None => res is None,
            },
    {
        let ghost s = old(self).rem();
        let p0 = self.pos;
        let mut acc: u64 = 0;
        proof { assert(p2(8) == 256) by { reveal_with_fuel(p2, 9); } }
        loop
            invariant
                self.wf(), self.same(*old(self)),
                p0 == old(self).pos, s == old(self).rem(),
                p0 <= self.pos,
                acc <= vb(),
                p2(8) == 256,
                ff_parse(s) == match ff_parse(self.rem()) {
                    Some((v, k)) => Some(((v + acc) as nat, (k + (self.pos - p0)) as nat)),
                    None => None,
                },
            decreases self.end - self.pos,
        {
            let ghost r = self.rem();
            let b = match self.read_nbit(8) {
                Some(b) => b,
                None => { return None; }
            };
            proof {
                lemma_bits_val_bound(r.take(8));
                assert(self.rem() =~= r.skip(8));
            }
            proof {
                assert(r.len() >= 8);
                assert(ff_parse(r) == if b == 255 {
                    match ff_parse(r.skip(8)) {
                        Some((v, k)) => Some(((v + 255) as nat, (k + 8) as nat)),
                        None => None,
                    }
                } else {
                    Some((b as nat, 8nat))
                });
            }
            if b != 255 {
                if acc + b > 281474976710656u64 {
                    return None;
                }
                return Some(acc + b);
            }
            if acc > 281474976710656u64 - 255 {
                return None;
            }
            acc = acc + 255;
        }
    }
}

// ------------------------------------------------------------------ writer

pub struct Writer {
    pub buf: Vec<u8>,
    pub pos: usize,
}

impl Writer {
    /// The buffer holds the bits written and, after them, fewer than eight
    /// zero bits.
    pub open spec fn wf(self) -> bool {
        &&& self.pos <= 8 * self.buf@.len()
        &&& 8 * self.buf@.len() <= usize::MAX
        &&& 8 * self.buf@.len() < self.pos + 8
        &&& forall|i: int| self.pos <= i < 8 * self.buf@.len() ==> !(#[trigger] bits_of(self.buf@)[i])
    }

    /// The bits written so far.
    pub open spec fn written(self) -> Seq<bool> {
        bits_of(self.buf@).take(self.pos as int)
    }

    pub fn new() -> (w: Writer)
        ensures w.wf(), w.written() =~= Seq::<bool>::empty(), w.pos == 0,
    {
        Writer { buf: Vec::new(), pos: 0 }
    }

    /// An `n`-bit unsigned field, `n` from 0 to 56.
    pub fn write_nbit(&mut self, n: usize, v: u64) -> (ok: bool)
        requires old(self).wf(), n <= 56, (v as nat) < p2(n as nat),
        ensures
            ok ==> final(self).wf(),
            ok ==> final(self).written() =~= old(self).written() + bits_seq(v, n as nat)
                   && final(self).pos == old(self).pos + n,
    {
        if n == 0 {
            assert(bits_seq(v, 0) =~= Seq::<bool>::empty());
            return true;
        }
        if self.pos > usize::MAX - 64 {
            return false;
        }
        while self.buf.len() * 8 < self.pos + n
            invariant
                self.pos == old(self).pos,
                self.pos <= usize::MAX - 64,
                self.pos <= 8 * self.buf@.len(),
                8 * self.buf@.len() <= usize::MAX,
                8 * self.buf@.len() < self.pos + n + 8,
                1 <= n <= 56,
                self.written() == old(self).written(),
                forall|i: int| self.pos <= i < 8 * self.buf@.len() ==> !(#[trigger] bits_of(self.buf@)[i]),
            decreases usize::MAX / 8 - self.buf@.len(),
        {
            if self.buf.len() >= usize::MAX / 8 - 16 {
                return false;
            }
            let ghost b0 = self.buf@;
            self.buf.push(0u8);
            proof {
                vbits::bytebits::lemma_bits_of_add(b0, seq![0u8]);
                assert(self.buf@ =~= b0 + seq![0u8]);
                assert(bits_of(self.buf@).take(self.pos as int) =~= bits_of(b0).take(self.pos as int));
                assert forall|i: int| self.pos <= i < 8 * self.buf@.len() implies !(#[trigger] bits_of(self.buf@)[i]) by {
                    if i >= 8 * b0.len() {
                        assert(bits_of(self.buf@)[i] == bits_of(seq![0u8])[i - 8 * b0.len()]);
                        vbits::prim_read::lemma_zero_bits(i - 8 * b0.len());
                    } else {
                        assert(bits_of(self.buf@)[i] == bits_of(b0)[i]);
                    }
                }
            }
        }
        let ghost before = bits_of(self.buf@);
        vbits::prim_write::write_bits(&mut self.buf, self.pos, n, v);
        proof {
            let after = bits_of(self.buf@);
            assert(after =~= before.take(self.pos as int) + bits_seq(v, n as nat)
                             + before.skip(self.pos as int + n as int));
            assert(after.take(self.pos as int + n as int)
                   =~= before.take(self.pos as int) + bits_seq(v, n as nat));
            assert forall|i: int| self.pos + n <= i < 8 * self.buf@.len() implies !(#[trigger] bits_of(self.buf@)[i]) by {
                assert(after[i] == before[i]);
            }
        }
        self.pos = self.pos + n;
        true
    }

    pub fn write_ue(&mut self, v: u64) -> (ok: bool)
        requires old(self).wf(), v <= ue_max(),
        ensures
            ok ==> final(self).wf(),
            ok ==> final(self).written() =~= old(self).written() + ue_code(v as nat)
                   && final(self).pos == old(self).pos + ue_code(v as nat).len(),
    {
        let m: u64 = v + 1;
        let l = ilog2_x(m);
        proof {
            lemma_ue_rt(v as nat, Seq::empty());
            lemma_ilog2(m as nat);
            lemma_zeros_bits_seq(l as nat);
            lemma_p2_pos(l as nat);
        }
        let ghost w0 = self.written();
        if !self.write_nbit(l, 0) {
            return false;
        }
        if !self.write_nbit(l + 1, m) {
            return false;
        }
        proof {
            assert(self.written() =~= w0 + (zeros(l as nat) + bits_seq(m, (l + 1) as nat)));
            assert(((v as nat + 1) as u64) == m);
        }
        true
    }

    pub fn write_se(&mut self, v: i64) -> (ok: bool)
        requires old(self).wf(), -se_max() <= v <= se_max(),
        ensures
            ok ==> final(self).wf(),
            ok ==> final(self).written() =~= old(self).written() + se_code(v as int)
                   && final(self).pos == old(self).pos + se_code(v as int).len(),
    {
        proof { lemma_se_map(v as int); }
        let k: u64 = if v > 0 { (2 * v - 1) as u64 } else { (-2 * v) as u64 };
        self.write_ue(k)
    }

    pub fn write_ff(&mut self, v: u64) -> (ok: bool)
        requires old(self).wf(),
        ensures
            ok ==> final(self).wf(),
            ok ==> final(self).written() =~= old(self).written() + ff_code(v as nat)
                   && final(self).pos == old(self).pos + ff_code(v as nat).len(),
    {
        let mut x = v;
        proof { assert(p2(8) == 256) by { reveal_with_fuel(p2, 9); } }
        loop
            invariant
                self.wf(),
                old(self).written() + ff_code(v as nat) =~= self.written() + ff_code(x as nat),
                self.pos + ff_code(x as nat).len() == old(self).pos + ff_code(v as nat).len(),
                p2(8) == 256,
            decreases x,
        {
            if x < 255 {
                return self.write_nbit(8, x);
            }
            if !self.write_nbit(8, 255) {
                return false;
            }
            x = x - 255;
        }
    }

    /// `byte_alignment( )`, at the current position.
    pub fn write_align(&mut self) -> (ok: bool)
        requires old(self).wf(),
        ensures
            ok ==> final(self).wf(),
            ok ==> final(self).written() =~= old(self).written() + align_code(old(self).pos as nat)
                   && final(self).pos == old(self).pos + align_code(old(self).pos as nat).len(),
    {
        let z: usize = (8 - (self.pos + 1) % 8) % 8;
        proof {
            assert(p2(1) == 2) by { reveal_with_fuel(p2, 2); }
            assert(p2(0) == 1);
            lemma_zeros_bits_seq(z as nat);
            assert(((1 - 1 - 0) as nat) == 0nat);
            assert((1u64 as nat) / p2(0) % 2 == 1);
            assert(bits_seq(1u64, 1)[0]);
            assert(bits_seq(1u64, 1) =~= seq![true]);
            lemma_p2_pos(z as nat);
        }
        let ghost w0 = self.written();
        if !self.write_nbit(1, 1) {
            return false;
        }
        if !self.write_nbit(z, 0) {
            return false;
        }
        proof {
            lemma_p2_pos(z as nat);
            assert(self.written() =~= w0 + (seq![true] + zeros(z as nat)));
        }
        true
    }
}

impl Writer {
    /// AV1's `byte_alignment( )`, at the current position.
    pub fn write_zalign(&mut self) -> (ok: bool)
        requires old(self).wf(),
        ensures
            ok ==> final(self).wf(),
            ok ==> final(self).written() =~= old(self).written() + zalign_code(old(self).pos as nat)
                   && final(self).pos == old(self).pos + zalign_code(old(self).pos as nat).len(),
    {
        let z: usize = (8 - self.pos % 8) % 8;
        proof {
            lemma_zeros_bits_seq(z as nat);
            lemma_p2_pos(z as nat);
        }
        self.write_nbit(z, 0)
    }
}

/// ⌊log2 m⌋.
pub fn ilog2_x(m: u64) -> (l: usize)
    requires m >= 1,
    ensures l as nat == ilog2(m as nat), l < 64,
{
    let mut x = m;
    let mut l: usize = 0;
    proof { lemma_ilog2_small(m as nat); }
    while x > 1
        invariant x >= 1, l + ilog2(x as nat) == ilog2(m as nat), ilog2(m as nat) < 64,
        decreases x,
    {
        x = x / 2;
        l = l + 1;
    }
    l
}

/// Each halving takes one off the logarithm, and a u64 has at most 63.
pub proof fn lemma_ilog2_small(x: nat)
    requires 1 <= x <= u64::MAX,
    ensures ilog2(x) < 64,
{
    lemma_ilog2(x);
    vbits::prim_read::lemma_p2_64();
    if ilog2(x) >= 64 {
        vbits::prim_read::lemma_p2_mono(64, ilog2(x));
    }
}

} // verus!
