//! Compression: a DEFLATE encoder, proved to round-trip through the spec:
//! for every input, `inflate(lbits(deflate_fixed(data)))` is `data`.
//!
//! One block with the fixed codes (RFC 1951 3.2.6), its matches found by a
//! greedy hash lookup of the last position with the same three bytes. The
//! proof needs nothing about how matches are found: each is checked byte by
//! byte before it is written.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::{bits_val, p2};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::prim_write::bits_seq;
use vbits::lsb::*;
use crate::spec::*;
use crate::huff::*;
use crate::step::*;
use crate::inflate::*;

verus! {

// --------------------------------------------------------- the bit writer

/// Bits written LSB-first: whole bytes in `buf`, then the low `nacc` bits of
/// `acc`.
pub struct BitW {
    pub buf: Vec<u8>,
    pub acc: u64,
    pub nacc: u64,
    /// the bytes already taken out (`flush`)
    pub pre: Ghost<Seq<u8>>,
}

impl BitW {
    pub open spec fn wf(&self) -> bool {
        self.nacc < 8 && self.acc < p2(self.nacc as nat) && self.buf@.len() < 0x1000_0000_0000_0000
    }

    pub open spec fn bits(&self) -> Seq<bool> {
        lbits(self.pre@ + self.buf@) + wbits(self.acc, self.nacc as nat)
    }
}

proof fn lemma_or_bits(acc: u64, na: u64, v: u64, n: u64, j: u64)
    requires na < 8, n <= 32, acc < (1u64 << na), v < (1u64 << n), j < na + n,
    ensures ((acc | (v << na)) >> j) & 1 == if j < na { (acc >> j) & 1 } else { (v >> ((j - na) as u64)) & 1 },
{
    assert(((acc | (v << na)) >> j) & 1 == if j < na { (acc >> j) & 1 } else { (v >> ((j - na) as u64)) & 1 })
        by (bit_vector)
        requires na < 8, n <= 32, acc < (1u64 << na), v < (1u64 << n), j < na + n;
}

pub fn bw_new() -> (w: BitW)
    ensures w.wf(), w.bits() == Seq::<bool>::empty(), w.buf@.len() == 0, w.pre@.len() == 0,
{
    let w = BitW { buf: Vec::new(), acc: 0, nacc: 0, pre: Ghost(Seq::empty()) };
    proof {
        assert(w.pre@ + w.buf@ =~= Seq::<u8>::empty());
        assert(lbits(w.buf@) =~= Seq::<bool>::empty());
        assert(wbits(0, 0) =~= Seq::<bool>::empty());
        assert(p2(0) == 1);
    }
    w
}

/// Append the low `n` bits of `v`, LSB first.
pub fn put(w: &mut BitW, v: u64, n: u64)
    requires old(w).wf(), n <= 32, v < p2(n as nat), old(w).buf@.len() + 8 < 0x1000_0000_0000_0000,
    ensures final(w).wf(), final(w).bits() == old(w).bits() + wbits(v, n as nat),
        final(w).buf@.len() <= old(w).buf@.len() + 5, final(w).pre == old(w).pre,
{
    let ghost b0 = w.bits();
    proof {
        vbits::prim_read::lemma_p2_eq_pow2(n as nat);
        vbits::prim_read::lemma_p2_eq_pow2(w.nacc as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(n as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, n);
        vstd::bits::lemma_u64_pow2_no_overflow(w.nacc as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, w.nacc);
    }
    let na = w.nacc;
    let acc = w.acc;
    assert(v < (1u64 << n));
    assert(acc < (1u64 << na));
    let acc2 = acc | (v << na);
    let n2 = na + n;
    proof {
        assert(wbits(acc2, n2 as nat) =~= wbits(acc, na as nat) + wbits(v, n as nat)) by {
            assert forall|j: int| 0 <= j < n2 implies
                #[trigger] wbits(acc2, n2 as nat)[j] == (wbits(acc, na as nat) + wbits(v, n as nat))[j] by {
                lemma_or_bits(acc, na, v, n, j as u64);
            }
        }
        assert(acc2 < (1u64 << n2)) by (bit_vector)
            requires acc2 == acc | (v << na), na < 8, n <= 32, acc < (1u64 << na), v < (1u64 << n), n2 == na + n;
    }
    w.acc = acc2;
    w.nacc = n2;
    proof { assert(w.bits() =~= b0 + wbits(v, n as nat)); }
    let ghost b1 = w.bits();
    while w.nacc >= 8
        invariant
            w.nacc <= 40, w.acc < (1u64 << w.nacc), w.bits() == b1, w.pre == old(w).pre,
            w.buf@.len() + (w.nacc as int) / 8 <= old(w).buf@.len() + 5,
            old(w).buf@.len() + 8 < 0x1000_0000_0000_0000,
        decreases w.nacc,
    {
        let x = (w.acc & 0xff) as u8;
        let ghost bb = w.buf@;
        let ghost a = w.acc;
        let ghost na = w.nacc;
        w.buf.push(x);
        w.acc = w.acc >> 8;
        w.nacc = w.nacc - 8;
        proof {
            let pr = w.pre@;
            lemma_lbits_add(pr + bb, seq![x]);
            assert(w.buf@ =~= bb + seq![x]);
            assert(pr + w.buf@ =~= (pr + bb) + seq![x]);
            assert(lbits(seq![x]) + wbits(w.acc, w.nacc as nat) =~= wbits(a, na as nat)) by {
                assert forall|j: int| 0 <= j < na implies
                    #[trigger] (lbits(seq![x]) + wbits(w.acc, w.nacc as nat))[j] == wbits(a, na as nat)[j] by {
                    let jj = j as u64;
                    if j < 8 {
                        assert(seq![x][j / 8] == x);
                        let j8 = jj as u8;
                        assert(j8 == j as u8);
                        assert(((x >> j8) & 1u8 == 1u8) == ((a >> jj) & 1u64 == 1u64)) by (bit_vector)
                            requires x == (a & 0xff) as u8, jj < 8, j8 == jj as u8;
                    } else {
                        assert(((a >> 8u64) >> ((jj - 8) as u64)) & 1u64 == (a >> jj) & 1u64) by (bit_vector)
                            requires 8 <= jj < 64;
                    }
                }
            }
            assert(w.bits() =~= lbits(pr + bb) + (lbits(seq![x]) + wbits(w.acc, w.nacc as nat)));
            let a2 = w.acc;
            let na2 = w.nacc;
            assert(a2 < (1u64 << na2)) by (bit_vector)
                requires a2 == a >> 8, a < (1u64 << na), 8 <= na <= 40, na2 == na - 8;
        }
    }
    proof {
        vbits::prim_read::lemma_p2_eq_pow2(w.nacc as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(w.nacc as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, w.nacc);
    }
}

/// Take out the whole bytes written so far; the bits stay the same.
pub fn flush(w: &mut BitW) -> (out: Vec<u8>)
    requires old(w).wf(),
    ensures final(w).wf(), final(w).bits() == old(w).bits(), final(w).pre@ == old(w).pre@ + out@,
        final(w).buf@.len() == 0,
{
    let mut out: Vec<u8> = Vec::new();
    std::mem::swap(&mut out, &mut w.buf);
    w.pre = Ghost(w.pre@ + out@);
    proof { assert(w.pre@ + w.buf@ =~= old(w).pre@ + old(w).buf@); }
    out
}

proof fn lemma_or2_bits(v1: u64, n1: u64, v2: u64, n2: u64, j: u64)
    requires n1 <= 32, n2 <= 32, n1 + n2 <= 32, v1 < (1u64 << n1), v2 < (1u64 << n2), j < n1 + n2,
    ensures ((v1 | (v2 << n1)) >> j) & 1 == if j < n1 { (v1 >> j) & 1 } else { (v2 >> ((j - n1) as u64)) & 1 },
{
    assert(((v1 | (v2 << n1)) >> j) & 1 == if j < n1 { (v1 >> j) & 1 } else { (v2 >> ((j - n1) as u64)) & 1 })
        by (bit_vector)
        requires n1 <= 32, n2 <= 32, n1 + n2 <= 32, v1 < (1u64 << n1), v2 < (1u64 << n2), j < n1 + n2;
}

/// Two fields at once: the low `n1` bits of `v1`, then the low `n2` of `v2`.
#[inline(always)]
pub fn put2(w: &mut BitW, v1: u64, n1: u64, v2: u64, n2: u64)
    requires old(w).wf(), n1 + n2 <= 32, v1 < p2(n1 as nat), v2 < p2(n2 as nat),
        old(w).buf@.len() + 8 < 0x1000_0000_0000_0000,
    ensures final(w).wf(), final(w).bits() == old(w).bits() + wbits(v1, n1 as nat) + wbits(v2, n2 as nat),
        final(w).buf@.len() <= old(w).buf@.len() + 5, final(w).pre == old(w).pre,
{
    proof {
        vbits::prim_read::lemma_p2_eq_pow2(n1 as nat);
        vbits::prim_read::lemma_p2_eq_pow2(n2 as nat);
        vbits::prim_read::lemma_p2_eq_pow2((n1 + n2) as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(n1 as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, n1);
        vstd::bits::lemma_u64_pow2_no_overflow(n2 as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, n2);
        vstd::bits::lemma_u64_pow2_no_overflow((n1 + n2) as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, (n1 + n2) as u64);
    }
    assert(v1 < (1u64 << n1));
    assert(v2 < (1u64 << n2));
    let v = v1 | (v2 << n1);
    let n = n1 + n2;
    proof {
        assert(v < (1u64 << n)) by (bit_vector)
            requires v == v1 | (v2 << n1), n == n1 + n2, n1 <= 32, n2 <= 32, n <= 32, v1 < (1u64 << n1), v2 < (1u64 << n2);
        assert(wbits(v, n as nat) =~= wbits(v1, n1 as nat) + wbits(v2, n2 as nat)) by {
            assert forall|j: int| 0 <= j < n implies
                #[trigger] wbits(v, n as nat)[j] == (wbits(v1, n1 as nat) + wbits(v2, n2 as nat))[j] by {
                lemma_or2_bits(v1, n1, v2, n2, j as u64);
            }
        }
    }
    let ghost b0 = w.bits();
    put(w, v, n);
    proof { assert(b0 + wbits(v, n as nat) =~= b0 + wbits(v1, n1 as nat) + wbits(v2, n2 as nat)); }
}

/// Write the last byte's remaining bits as zeros: the bytes are the bits
/// written, and some zeros.
pub fn finish(w: BitW) -> (out: Vec<u8>)
    requires w.wf(),
    ensures is_prefix(w.bits(), lbits(w.pre@ + out@)), w.pre@.len() + out@.len() == (w.bits().len() + 7) / 8,
{
    let mut w = w;
    let ghost b0 = w.bits();
    if w.nacc > 0 {
        let x = w.acc as u8;
        let ghost bb = w.pre@ + w.buf@;
        w.buf.push(x);
        proof {
            lemma_lbits_add(bb, seq![x]);
            assert(w.pre@ + w.buf@ =~= bb + seq![x]);
            vbits::prim_read::lemma_p2_eq_pow2(w.nacc as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(w.nacc as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, w.nacc);
            assert forall|i: int| 0 <= i < b0.len() implies #[trigger] b0[i] == lbits(w.pre@ + w.buf@)[i] by {
                if i >= lbits(bb).len() {
                    let j = i - lbits(bb).len();
                    let jj = j as u64;
                    assert(seq![x][j / 8] == x);
                    let j8 = jj as u8;
                    let wa = w.acc;
                    assert(j8 == j as u8);
                    assert(((x >> j8) & 1u8 == 1u8) == ((wa >> jj) & 1u64 == 1u64)) by (bit_vector)
                        requires x == wa as u8, jj < 8, j8 == jj as u8;
                }
            }
        }
    }
    w.buf
}

// ------------------------------------------------------ writing a code

/// A code's bits, most significant first, as a value to write LSB first.
fn rev_bits(c: u64, l: u64) -> (v: u64)
    requires l <= 15, c < p2(l as nat),
    ensures v < p2(l as nat), wbits(v, l as nat) == bits_seq(c, l as nat),
{
    let mut v: u64 = 0;
    let mut j: u64 = 0;
    assert(0u64 < (1u64 << 0u64)) by (bit_vector);
    while j < l
        invariant
            j <= l, l <= 15, v < (1u64 << j),
            forall|i: int| 0 <= i < j ==> ((v >> (i as u64)) & 1u64 == 1u64) == #[trigger] bits_seq(c, l as nat)[i],
        decreases l - j,
    {
        let sh = l - 1 - j;
        let b = (c >> sh) & 1;
        assert(b <= 1) by (bit_vector) requires b == (c >> sh) & 1;
        let v2 = v | (b << j);
        proof {
            vbits::prim_read::lemma_p2_eq_pow2(sh as nat);
            vstd::bits::lemma_u64_shr_is_div(c, sh);
            assert((b == 1) == ((c >> sh) % 2 == 1)) by (bit_vector) requires b == (c >> sh) & 1;
            assert(bits_seq(c, l as nat)[j as int] == ((c as nat / p2(sh as nat)) % 2 == 1));
            assert forall|i: int| 0 <= i < j + 1 implies
                ((v2 >> (i as u64)) & 1u64 == 1u64) == #[trigger] bits_seq(c, l as nat)[i] by {
                let ii = i as u64;
                assert(((v2 >> ii) & 1u64) == if ii < j { (v >> ii) & 1u64 } else { b }) by (bit_vector)
                    requires v2 == v | (b << j), v < (1u64 << j), b <= 1, ii <= j, j < 15;
            }
            assert(v2 < (1u64 << (j + 1) as u64)) by (bit_vector)
                requires v2 == v | (b << j), v < (1u64 << j), b <= 1, j < 15;
        }
        v = v2;
        j = j + 1;
    }
    proof {
        vbits::prim_read::lemma_p2_eq_pow2(l as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(l as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, l);
        assert(wbits(v, l as nat) =~= bits_seq(c, l as nat));
    }
    v
}

/// `next_code` shrinks, going to shorter lengths, past every code of those.
proof fn lemma_nc_div(lens: Seq<u8>, l: nat, big: nat)
    requires 1 <= l < big,
    ensures next_code(lens, big) / p2((big - l) as nat) >= next_code(lens, l) + bl_count(lens, l),
    decreases big - l,
{
    let k = (big - l) as nat;
    vbits::bitspec::lemma_p2_pos(k);
    if big == l + 1 {
        assert(p2(1) == 2) by { reveal_with_fuel(p2, 2); }
        assert(next_code(lens, big) == 2 * (next_code(lens, l) + bl_count(lens, l)));
    } else {
        lemma_nc_div(lens, l, (big - 1) as nat);
        let a = next_code(lens, big) as int;
        let h = next_code(lens, (big - 1) as nat) + bl_count(lens, (big - 1) as nat);
        assert(a == 2 * h);
        assert(p2(k) == 2 * p2((k - 1) as nat));
        vbits::bitspec::lemma_p2_pos((k - 1) as nat);
        vstd::arithmetic::div_mod::lemma_div_denominator(a, 2, p2((k - 1) as nat) as int);
        assert(a / 2 == h);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(next_code(lens, (big - 1) as nat) as int, h as int,
            p2((k - 1) as nat) as int);
    }
}

/// The first `l` bits of a code are its value shifted down.
proof fn lemma_code_prefix(c: u64, big: nat, l: nat)
    requires l <= big, big <= 64, c < p2(big),
    ensures bits_val(bits_seq(c, big).take(l as int)) == c as nat / p2((big - l) as nat),
{
    let s = bits_seq(c, big);
    vbits::prim_write::lemma_bits_seq_val(c, big);
    vbits::bitspec::lemma_bits_val_split(s, l as int);
    vbits::bitspec::lemma_bits_val_bound(s.skip(l as int));
    vbits::bitspec::lemma_p2_pos((big - l) as nat);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(c as int, p2((big - l) as nat) as int,
        bits_val(s.take(l as int)) as int, bits_val(s.skip(l as int)) as int);
}

/// Writing a symbol's code, most significant bit first, decodes to it: no
/// shorter code of a canonical code is a prefix of it.
pub proof fn lemma_code_decodes(lens: Seq<u8>, s: int, b: Seq<bool>, p: int)
    requires
        lens_ok(lens), 0 <= s < lens.len(), 1 <= lens[s] <= 15, code_of(lens, s) < p2(lens[s] as nat),
        0 <= p, p + lens[s] <= b.len(), b.subrange(p, p + lens[s]) == bits_seq(code_of(lens, s) as u64, lens[s] as nat),
    ensures decode_sym(lens, b, p) == Some((s as nat, p + lens[s])),
{
    let big = lens[s] as nat;
    let c = code_of(lens, s);
    vbits::prim_read::lemma_p2_mono(big, 64);
    vbits::prim_read::lemma_p2_64();
    assert(c < 0x1_0000_0000_0000_0000);
    let cs = bits_seq(c as u64, big);
    assert forall|l: nat| 1 <= l < big implies #[trigger] find_n(lens, b, p, l, 0) is None by {
        assert(b.subrange(p, p + l) =~= cs.take(l as int));
        lemma_code_prefix(c as u64, big, l);
        lemma_nc_div(lens, l, big);
        vbits::bitspec::lemma_p2_pos((big - l) as nat);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(next_code(lens, big) as int, c as int, p2((big - l) as nat) as int);
        lemma_find_n_range(lens, b, p, l);
    }
    assert(b.subrange(p, p + big) =~= cs);
    vbits::prim_write::lemma_bits_seq_val(c as u64, big);
    lemma_rank_lt(lens, s);
    lemma_find_n_range(lens, b, p, big);
    let n = find_n(lens, b, p, big, 0).unwrap() as int;
    assert(lens[n] == lens[s]);
    if n != s {
        if n < s { lemma_rank_inj(lens, n, s); } else { lemma_rank_inj(lens, s, n); }
    }
    lemma_find_sym_skip(lens, b, p, 1, big);
}

// ------------------------------------------------------- canonical codes

/// Every symbol's code (RFC 1951 3.2.2): `codes[s] == code_of(lens, s)`.
pub fn canon_codes(lens: &[u8]) -> (codes: Vec<u64>)
    requires lens.len() <= 320, lens_ok(lens@),
    ensures codes@.len() == lens.len(),
        forall|s: int| 0 <= s < lens.len() && 1 <= lens@[s] ==> #[trigger] codes@[s] as nat == code_of(lens@, s),
{
    let ghost gl = lens@;
    let n = lens.len();
    let mut count = [0u64; 16];
    let mut i: usize = 0;
    while i < n
        invariant
            n == lens.len(), gl == lens@, i <= n, n <= 320, lens_ok(gl),
            forall|l: int| 0 <= l < 16 ==> #[trigger] count[l] as nat == count_len(gl, l as nat, i as int),
        decreases n - i,
    {
        let l = lens[i] as usize;
        assert(lens[i as int] <= 15);
        proof { lemma_count_le(gl, l as nat, i as int); }
        count[l] = count[l] + 1;
        i = i + 1;
    }
    // next[l] = next_code(l), bounded as decode_bits bounds it
    let mut next = [0u64; 16];
    let mut l: usize = 1;
    proof { reveal_with_fuel(p2, 16); assert(next_code(gl, 1) == 0); }
    while l < 15
        invariant
            1 <= l <= 15, n <= 320, gl == lens@, n == gl.len(),
            forall|l: int| 0 <= l < 16 ==> #[trigger] count[l] as nat == count_len(gl, l as nat, n as int),
            forall|j: int| 1 <= j <= l ==> #[trigger] next[j] as nat == next_code(gl, j as nat),
            forall|j: int| 1 <= j <= l ==> #[trigger] next[j] + 640 <= 640 * p2(j as nat),
            p2(15) == 32768,
        decreases 15 - l,
    {
        proof {
            lemma_count_le(gl, l as nat, n as int);
            vbits::prim_read::lemma_p2_mono(l as nat, 15);
            assert(p2((l + 1) as nat) == 2 * p2(l as nat));
            assert(next[l as int] + 640 <= 640 * p2(l as nat));
            assert(count[l as int] <= 320);
            assert(next_code(gl, (l + 1) as nat) == 2 * (next_code(gl, l as nat) + bl_count(gl, l as nat)));
        }
        next[l + 1] = 2 * (next[l] + count[l]);
        l = l + 1;
    }
    let mut cur = next;
    let mut codes: Vec<u64> = Vec::with_capacity(n);
    let mut s: usize = 0;
    while s < n
        invariant
            n == lens.len(), gl == lens@, s <= n, n <= 320, lens_ok(gl), codes@.len() == s,
            forall|l: int| 0 <= l < 16 ==> #[trigger] count[l] as nat == count_len(gl, l as nat, n as int),
            forall|j: int| 1 <= j <= 15 ==> #[trigger] next[j] as nat == next_code(gl, j as nat),
            forall|j: int| 1 <= j <= 15 ==> #[trigger] next[j] + 640 <= 640 * p2(j as nat),
            forall|j: int| 1 <= j <= 15 ==> #[trigger] cur[j] as nat == next[j] + count_len(gl, j as nat, s as int),
            forall|t: int| 0 <= t < s && 1 <= gl[t] ==> #[trigger] codes@[t] as nat == code_of(gl, t),
            p2(15) == 32768,
        decreases n - s,
    {
        let l = lens[s] as usize;
        assert(lens[s as int] <= 15);
        proof { lemma_count_step(gl, s as int); }
        if l == 0 {
            codes.push(0);
        } else {
            proof {
                lemma_count_le(gl, l as nat, s as int);
                vbits::prim_read::lemma_p2_mono(l as nat, 15);
            }
            codes.push(cur[l]);
            cur[l] = cur[l] + 1;
        }
        s = s + 1;
    }
    codes
}

/// The extra bits written read back as their value.
pub proof fn lemma_lval_wbits(e: u64, n: nat)
    requires n <= 32, e < p2(n),
    ensures lval(wbits(e, n)) == e,
    decreases n,
{
    if n > 0 {
        let t = wbits(e, n);
        assert(t.subrange(1, t.len() as int) =~= wbits(e >> 1u64, (n - 1) as nat)) by {
            assert forall|j: int| 0 <= j < n - 1 implies
                #[trigger] t.subrange(1, t.len() as int)[j] == wbits(e >> 1u64, (n - 1) as nat)[j] by {
                let jj = j as u64;
                assert(((e >> (jj + 1) as u64) & 1u64) == (((e >> 1u64) >> jj) & 1u64)) by (bit_vector) requires jj < 32;
            }
        }
        assert(e >> 1u64 == e / 2) by (bit_vector);
        assert(p2(n) == 2 * p2((n - 1) as nat));
        lemma_lval_wbits(e >> 1u64, (n - 1) as nat);
        assert(((e >> 0u64) & 1u64 == 1u64) == (e % 2 == 1)) by (bit_vector);
    }
}

pub proof fn lemma_getbits_wbits(b: Seq<bool>, p: int, e: u64, n: nat)
    requires 0 <= p, p + n <= b.len(), b.subrange(p, p + n) == wbits(e, n), n <= 32, e < p2(n),
    ensures getbits(b, p, n) == Some(e as nat),
{
    lemma_lval_wbits(e, n);
}

/// A match checked byte by byte is the spec's copy.
pub proof fn lemma_lz_match(data: Seq<u8>, i: int, d: nat, len: nat)
    requires 1 <= d <= i, i + len <= data.len(),
        forall|j: int| 0 <= j < len ==> #[trigger] data[i + j] == data[i + j - d],
    ensures lz_copy(data.take(i), d, len) == data.take(i + len),
    decreases len,
{
    if len > 0 {
        let o = data.take(i);
        assert(o[o.len() - d] == data[i - d]);
        assert(data[i + 0] == data[i + 0 - d]);
        assert(o.push(o[o.len() - d]) =~= data.take(i + 1));
        assert forall|j: int| 0 <= j < len - 1 implies #[trigger] data[(i + 1) + j] == data[(i + 1) + j - d] by {
            assert(data[i + (j + 1)] == data[i + (j + 1) - d]);
        }
        lemma_lz_match(data, i + 1, d, (len - 1) as nat);
    } else {
        assert(data.take(i) =~= data.take(i + len));
    }
}

// -------------------------------------------------------- the fixed code

/// A code ready to write: each symbol's length and reversed code, for the
/// symbols whose code fits its length.
pub struct EncCode {
    pub lens: Vec<u8>,
    pub rc: Vec<u64>,
}

pub open spec fn enc_ok(c: &EncCode, lens: Seq<u8>) -> bool {
    &&& c.lens@ == lens && c.rc@.len() == lens.len() && lens_ok(lens) && lens.len() <= 320
    &&& forall|s: int| 0 <= s < lens.len() ==> rc_ok(lens, s, #[trigger] c.rc@[s])
}

/// The code for `lens`, if every code fits its length (true of any code
/// that is not over-subscribed).
/// What writing symbol `t` needs: its code fits its length, and `v` is the
/// code reversed.
pub open spec fn rc_ok(lens: Seq<u8>, t: int, v: u64) -> bool {
    1 <= lens[t] ==> (code_of(lens, t) < p2(lens[t] as nat) && v < p2(lens[t] as nat)
        && wbits(v, lens[t] as nat) == bits_seq(code_of(lens, t) as u64, lens[t] as nat))
}

/// The code for `lens`, if every code fits its length (true of any code
/// that is not over-subscribed).
pub fn enc_code(lens: Vec<u8>) -> (r: Option<EncCode>)
    requires lens@.len() <= 320, lens_ok(lens@),
    ensures r matches Some(c) ==> enc_ok(&c, lens@),
{
    let codes = canon_codes(&lens);
    let mut rc: Vec<u64> = Vec::with_capacity(lens.len());
    let mut s: usize = 0;
    while s < lens.len()
        invariant
            s <= lens@.len(), lens@.len() <= 320, lens_ok(lens@), codes@.len() == lens@.len(), rc@.len() == s,
            forall|t: int| 0 <= t < lens@.len() && 1 <= lens@[t] ==> #[trigger] codes@[t] as nat == code_of(lens@, t),
            forall|t: int| 0 <= t < s ==> rc_ok(lens@, t, #[trigger] rc@[t]),
        decreases lens@.len() - s,
    {
        let l = lens[s] as u64;
        assert(lens@[s as int] <= 15);
        let v: u64 = if l == 0 {
            0
        } else {
            proof {
                vbits::prim_read::lemma_p2_eq_pow2(l as nat);
                vstd::bits::lemma_u64_pow2_no_overflow(l as nat);
                vstd::bits::lemma_u64_shl_is_mul(1u64, l);
            }
            if codes[s] >= (1u64 << l) {
                return None;
            }
            proof {
                assert(codes@[s as int] as nat == code_of(lens@, s as int));
                assert(code_of(lens@, s as int) as u64 == codes@[s as int]);
            }
            rev_bits(codes[s], l)
        };
        proof { assert(rc_ok(lens@, s as int, v)); }
        let ghost rc0 = rc@;
        rc.push(v);
        proof {
            assert forall|t: int| 0 <= t < s + 1 implies rc_ok(lens@, t, #[trigger] rc@[t]) by {
                if t < s as int { assert(rc@[t] == rc0[t]); }
            }
        }
        s = s + 1;
    }
    Some(EncCode { lens, rc })
}

/// A lit/length symbol and its extra bits for a match length.
pub fn len_code(len: u64) -> (r: Option<(u64, u64, u64)>)
    requires 3 <= len <= 258,
    ensures r matches Some((s, e, x)) ==> 257 <= s <= 285 && x as nat == len_extra(s as nat) && x <= 5
        && e < p2(x as nat) && len_base(s as nat) + e == len,
{
    let mut s: u64 = 257;
    while s <= 285
        invariant 257 <= s <= 286, 3 <= len <= 258,
        decreases 286 - s,
    {
        let b = len_base_x(s);
        let x = len_extra_x(s);
        proof {
            vbits::prim_read::lemma_p2_eq_pow2(x as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(x as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, x);
        }
        if b <= len && len - b < (1u64 << x) {
            return Some((s, len - b, x));
        }
        s = s + 1;
    }
    None
}

/// A distance symbol and its extra bits for a distance.
pub fn dist_code(d: u64) -> (r: Option<(u64, u64, u64)>)
    requires 1 <= d <= 32768,
    ensures r matches Some((s, e, x)) ==> s <= 29 && x as nat == dist_extra(s as nat) && x <= 13
        && e < p2(x as nat) && dist_base(s as nat) + e == d,
{
    let mut s: u64 = 0;
    while s <= 29
        invariant s <= 30, 1 <= d <= 32768,
        decreases 30 - s,
    {
        let b = dist_base_x(s);
        let x = dist_extra_x(s);
        proof {
            vbits::prim_read::lemma_p2_eq_pow2(x as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(x as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, x);
        }
        if b <= d && d - b < (1u64 << x) {
            return Some((s, d - b, x));
        }
        s = s + 1;
    }
    None
}

/// The symbol tables: for each length (3 to 258) its length symbol, for
/// each distance d its distance symbol, from `d - 1` below 256 and from
/// `(d - 1) / 128` above. Each lookup is checked where it is used, so the
/// tables need no proof.
pub struct SymTabs {
    pub ls: Vec<u16>,
    pub dlo: Vec<u8>,
    pub dhi: Vec<u8>,
}

pub open spec fn tabs_wf(t: &SymTabs) -> bool {
    t.ls@.len() == 259 && t.dlo@.len() == 256 && t.dhi@.len() == 256
}

pub fn sym_tabs() -> (t: SymTabs)
    ensures tabs_wf(&t),
{
    let mut ls: Vec<u16> = vec![0u16; 259];
    let mut l: usize = 3;
    while l <= 258
        invariant 3 <= l <= 259, ls@.len() == 259,
        decreases 259 - l,
    {
        if let Some((s, _, _)) = len_code(l as u64) { ls.set(l, s as u16); }
        l = l + 1;
    }
    let mut dlo: Vec<u8> = vec![0u8; 256];
    let mut dhi: Vec<u8> = vec![0u8; 256];
    let mut k: usize = 0;
    while k < 256
        invariant k <= 256, dlo@.len() == 256, dhi@.len() == 256,
        decreases 256 - k,
    {
        if let Some((s, _, _)) = dist_code(k as u64 + 1) { dlo.set(k, s as u8); }
        if k >= 2 {
            if let Some((s, _, _)) = dist_code((k as u64) * 128 + 1) { dhi.set(k, s as u8); }
        }
        k = k + 1;
    }
    SymTabs { ls, dlo, dhi }
}

/// `len_code` by table, checked.
#[inline(always)]
pub fn len_code_t(t: &SymTabs, len: u64) -> (r: Option<(u64, u64, u64)>)
    requires 3 <= len <= 258, tabs_wf(t),
    ensures r matches Some((s, e, x)) ==> 257 <= s <= 285 && x as nat == len_extra(s as nat) && x <= 5
        && e < p2(x as nat) && len_base(s as nat) + e == len,
{
    let s = t.ls[len as usize] as u64;
    if 257 <= s && s <= 285 {
        let b = len_base_x(s);
        let x = len_extra_x(s);
        proof {
            vbits::prim_read::lemma_p2_eq_pow2(x as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(x as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, x);
        }
        if b <= len && len - b < (1u64 << x) {
            return Some((s, len - b, x));
        }
    }
    len_code(len)
}

/// `dist_code` by table, checked.
#[inline(always)]
pub fn dist_code_t(t: &SymTabs, d: u64) -> (r: Option<(u64, u64, u64)>)
    requires 1 <= d <= 32768, tabs_wf(t),
    ensures r matches Some((s, e, x)) ==> s <= 29 && x as nat == dist_extra(s as nat) && x <= 13
        && e < p2(x as nat) && dist_base(s as nat) + e == d,
{
    let v = d - 1;
    let s = if v < 256 { t.dlo[v as usize] as u64 } else { t.dhi[(v / 128) as usize] as u64 };
    if s <= 29 {
        let b = dist_base_x(s);
        let x = dist_extra_x(s);
        proof {
            vbits::prim_read::lemma_p2_eq_pow2(x as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(x as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, x);
        }
        if b <= d && d - b < (1u64 << x) {
            return Some((s, d - b, x));
        }
    }
    dist_code(d)
}

// ------------------------------------------------------------ the encoder

/// The written code of symbol `s`, then anything, decodes to `s`.
pub proof fn lemma_written_sym(lens: Seq<u8>, c: &EncCode, s: int, w: Seq<bool>, b: Seq<bool>)
    requires enc_ok(c, lens), 0 <= s < lens.len(), 1 <= lens[s],
        is_prefix(w + wbits(c.rc@[s], lens[s] as nat), b),
    ensures decode_sym(lens, b, w.len() as int) == Some((s as nat, w.len() + lens[s])),
{
    let l = lens[s] as nat;
    let x = wbits(c.rc@[s], l);
    assert(b.subrange(w.len() as int, (w.len() + l) as int) =~= x) by {
        assert forall|j: int| 0 <= j < l implies #[trigger] b.subrange(w.len() as int, (w.len() + l) as int)[j] == x[j] by {
            assert((w + x)[w.len() + j] == b[w.len() + j]);
        }
    }
    lemma_code_decodes(lens, s, b, w.len() as int);
}

pub proof fn lemma_written_bits(e: u64, n: nat, w: Seq<bool>, b: Seq<bool>)
    requires n <= 32, e < p2(n), is_prefix(w + wbits(e, n), b),
    ensures getbits(b, w.len() as int, n) == Some(e as nat),
{
    let x = wbits(e, n);
    assert(b.subrange(w.len() as int, (w.len() + n) as int) =~= x) by {
        assert forall|j: int| 0 <= j < n implies #[trigger] b.subrange(w.len() as int, (w.len() + n) as int)[j] == x[j] by {
            assert((w + x)[w.len() + j] == b[w.len() + j]);
        }
    }
    lemma_getbits_wbits(b, w.len() as int, e, n);
}

pub proof fn lemma_prefix_of_append(a: Seq<bool>, x: Seq<bool>, b: Seq<bool>)
    requires is_prefix(a + x, b),
    ensures is_prefix(a, b),
{
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i] == b[i] by {
        assert((a + x)[i] == b[i]);
    }
}

/// The state of the encoder: every stream that starts with the bits written
/// decodes the block from bit 3 to the input so far, from where the writing
/// is.
pub open spec fn enc_inv(w: Seq<bool>, data: Seq<u8>, i: int) -> bool {
    &&& w.len() >= 3
    &&& forall|b: Seq<bool>| #[trigger] is_prefix(w, b) ==>
        getbits(b, 0, 1) == Some(1nat) && getbits(b, 1, 2) == Some(1nat)
        && inflate_syms(fixed_lit(), fixed_dist(), b, 3, Seq::empty())
            == inflate_syms(fixed_lit(), fixed_dist(), b, w.len() as int, data.take(i))
}

/// Write a literal: the encoder's state moves past it.
fn emit_lit(w: &mut BitW, fl: &EncCode, fd: &EncCode, data: &[u8], i: usize)
    requires
        old(w).wf(), old(w).buf@.len() <= 6 * i + 1, i < data.len(), data.len() < 0x1000_0000,
        enc_ok(fl, fixed_lit()), enc_ok(fd, fixed_dist()), enc_inv(old(w).bits(), data@, i as int),
    ensures
        final(w).pre == old(w).pre,
        final(w).wf(), final(w).buf@.len() <= 6 * (i + 1) + 1, enc_inv(final(w).bits(), data@, i + 1),
{
    let ghost w0 = w.bits();
    let x = data[i] as usize;
    proof { assert(fixed_lit()[x as int] >= 7); }
    let ll = fl.lens[x] as u64;
    put(w, fl.rc[x], ll);
    proof {
        let wf = w.bits();
        let p = w0.len() as int;
        assert forall|b: Seq<bool>| #[trigger] is_prefix(wf, b) implies
            getbits(b, 0, 1) == Some(1nat) && getbits(b, 1, 2) == Some(1nat)
            && inflate_syms(fixed_lit(), fixed_dist(), b, 3, Seq::empty())
                == inflate_syms(fixed_lit(), fixed_dist(), b, wf.len() as int, data@.take(i + 1)) by {
            lemma_prefix_of_append(w0, wbits(fl.rc@[x as int], ll as nat), b);
            assert(is_prefix(w0, b));
            lemma_written_sym(fixed_lit(), fl, x as int, w0, b);
            assert(sym_step(fixed_lit(), fixed_dist(), b, p) == Some(Step::Lit(x as u8, wf.len() as int)));
            lemma_syms_unfold(fixed_lit(), fixed_dist(), b, p, data@.take(i as int));
            assert(data@.take(i as int).push(x as u8) =~= data@.take(i + 1));
        }
    }
}

/// Write a match of `mlen` bytes from `dist` back, checked byte by byte.
fn emit_match(w: &mut BitW, fl: &EncCode, fd: &EncCode, data: &[u8], i: usize, mlen: usize, dist: usize,
              ls: u64, le: u64, lx: u64, ds: u64, de: u64, dx: u64)
    requires
        old(w).wf(), old(w).buf@.len() <= 6 * i + 1, i + mlen <= data.len(), data.len() < 0x1000_0000,
        enc_ok(fl, fixed_lit()), enc_ok(fd, fixed_dist()), enc_inv(old(w).bits(), data@, i as int),
        3 <= mlen <= 258, 1 <= dist <= i,
        forall|j: int| 0 <= j < mlen ==> #[trigger] data@[i + j] == data@[i + j - dist],
        257 <= ls <= 285, lx as nat == len_extra(ls as nat), lx <= 5, le < p2(lx as nat), len_base(ls as nat) + le == mlen,
        ds <= 29, dx as nat == dist_extra(ds as nat), dx <= 13, de < p2(dx as nat), dist_base(ds as nat) + de == dist,
    ensures
        final(w).pre == old(w).pre,
        final(w).wf(), final(w).buf@.len() <= 6 * (i + mlen) + 1, enc_inv(final(w).bits(), data@, i + mlen),
{
    let ghost w0 = w.bits();
    let ls = ls as usize;
    let ds = ds as usize;
    proof {
        assert(1 <= fixed_lit()[ls as int] <= 15);
        assert(fixed_dist()[ds as int] == 5);
        reveal_with_fuel(p2, 6);
    }
    let ll = fl.lens[ls] as u64;
    put(w, fl.rc[ls], ll);
    let ghost w1 = w.bits();
    put(w, le, lx);
    let ghost w2 = w.bits();
    put(w, fd.rc[ds], 5);
    let ghost w3 = w.bits();
    put(w, de, dx);
    proof {
        let wf = w.bits();
        let p = w0.len() as int;
        let p1 = w1.len() as int;
        let p4 = wf.len() as int;
        assert(fd.lens@[ds as int] == 5);
        assert forall|b: Seq<bool>| #[trigger] is_prefix(wf, b) implies
            getbits(b, 0, 1) == Some(1nat) && getbits(b, 1, 2) == Some(1nat)
            && inflate_syms(fixed_lit(), fixed_dist(), b, 3, Seq::empty())
                == inflate_syms(fixed_lit(), fixed_dist(), b, p4, data@.take(i + mlen)) by {
            lemma_prefix_of_append(w3, wbits(de, dx as nat), b);
            lemma_prefix_of_append(w2, wbits(fd.rc@[ds as int], 5), b);
            lemma_prefix_of_append(w1, wbits(le, lx as nat), b);
            lemma_prefix_of_append(w0, wbits(fl.rc@[ls as int], ll as nat), b);
            lemma_written_sym(fixed_lit(), fl, ls as int, w0, b);
            lemma_written_bits(le, lx as nat, w1, b);
            lemma_written_sym(fixed_dist(), fd, ds as int, w2, b);
            lemma_written_bits(de, dx as nat, w3, b);
            assert(len_dist(fixed_dist(), b, p1, ls as nat) == Some((mlen as nat, dist as nat, p4)));
            assert(sym_step(fixed_lit(), fixed_dist(), b, p) == Some(Step::Copy(mlen as nat, dist as nat, p4)));
            lemma_syms_unfold(fixed_lit(), fixed_dist(), b, p, data@.take(i as int));
            lemma_lz_match(data@, i as int, dist as nat, mlen as nat);
        }
    }
}

/// Compress `data` into one block with the fixed codes. The result is what
/// the spec decodes to `data` (`None` only if the fixed codes did not fit
/// their lengths, which they do).
pub fn deflate_fixed(data: &[u8]) -> (r: Option<Vec<u8>>)
    requires data.len() < 0x1000_0000,
    ensures r matches Some(o) ==> (inflate(lbits(o@)) matches Some((d, _, st)) && d == data@ && st),
{
    let fl = match enc_code(fixed_lit_x()) { None => return None, Some(c) => c };
    let fd = match enc_code(fixed_dist_x()) { None => return None, Some(c) => c };
    proof {
        assert(lens_ok(fixed_lit())) by { assert forall|i: int| 0 <= i < fixed_lit().len() implies #[trigger] fixed_lit()[i] <= 15 by {} }
    }
    let n = data.len();
    let mut w = bw_new();
    proof { reveal_with_fuel(p2, 3); }
    put(&mut w, 1, 1);
    put(&mut w, 1, 2);
    proof {
        reveal_with_fuel(p2, 3);
        assert(w.bits() =~= wbits(1, 1) + wbits(1, 2));
        assert forall|b: Seq<bool>| #[trigger] is_prefix(w.bits(), b) implies
            getbits(b, 0, 1) == Some(1nat) && getbits(b, 1, 2) == Some(1nat)
            && inflate_syms(fixed_lit(), fixed_dist(), b, 3, Seq::empty())
                == inflate_syms(fixed_lit(), fixed_dist(), b, w.bits().len() as int, data@.take(0)) by {
            assert(Seq::<bool>::empty() + wbits(1, 1) =~= wbits(1, 1));
            assert(is_prefix(Seq::<bool>::empty() + wbits(1, 1), b)) by {
                assert forall|i: int| 0 <= i < 1 implies #[trigger] (Seq::<bool>::empty() + wbits(1, 1))[i] == b[i] by {
                    assert(w.bits()[i] == b[i]);
                }
            }
            lemma_written_bits(1, 1, Seq::empty(), b);
            lemma_written_bits(1, 2, wbits(1, 1), b);
            assert(data@.take(0) =~= Seq::<u8>::empty());
        }
    }
    let mut head: Vec<u32> = vec![0u32; 32768];
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n, n == data.len(), n < 0x1000_0000, head@.len() == 32768,
            w.wf(), w.buf@.len() <= 6 * i + 1, w.pre@.len() == 0,
            enc_ok(&fl, fixed_lit()), enc_ok(&fd, fixed_dist()),
            enc_inv(w.bits(), data@, i as int),
            forall|h: int| 0 <= h < 32768 ==> #[trigger] head@[h] as int <= i,
        decreases n - i,
    {
        let ghost w0 = w.bits();
        // a match with the last position whose three bytes hash the same
        let mut mlen: usize = 0;
        let mut dist: usize = 0;
        if n - i >= 3 {
            let hx = ((data[i] as usize) << 10) ^ ((data[i + 1] as usize) << 5) ^ (data[i + 2] as usize);
            let h = hx & 0x7fff;
            assert(h < 32768) by (bit_vector) requires h == hx & 0x7fff;
            let cand = head[h] as usize;
            head.set(h, (i + 1) as u32);
            if cand != 0 && i + 1 - cand <= 32768 {
                let d = i + 1 - cand;
                let mut m: usize = 0;
                while m < 258 && i + m < n && data[i + m] == data[i + m - d]
                    invariant
                        m <= 258, i + m <= n, 1 <= d <= i, n == data.len(),
                        forall|j: int| 0 <= j < m ==> #[trigger] data@[i + j] == data@[i + j - d],
                    decreases 258 - m,
                {
                    m = m + 1;
                }
                if m >= 3 {
                    mlen = m;
                    dist = d;
                }
            }
        }
        let mut done = false;
        if mlen >= 3 {
            match (len_code(mlen as u64), dist_code(dist as u64)) {
                (Some((ls, le, lx)), Some((ds, de, dx))) => {
                    emit_match(&mut w, &fl, &fd, data, i, mlen, dist, ls, le, lx, ds, de, dx);
                    i = i + mlen;
                    done = true;
                }
                _ => {}
            }
        }
        if !done {
            emit_lit(&mut w, &fl, &fd, data, i);
            i = i + 1;
        }
    }
    // end of block
    let ghost w0 = w.bits();
    proof { assert(1 <= fixed_lit()[256] <= 15); }
    let l256 = fl.lens[256] as u64;
    put(&mut w, fl.rc[256], l256);
    let ghost wf = w.bits();
    let out = finish(w);
    proof {
        let b = lbits(out@);
        lemma_prefix_of_append(w0, wbits(fl.rc@[256], l256 as nat), b);
        lemma_written_sym(fixed_lit(), &fl, 256, w0, b);
        assert(sym_step(fixed_lit(), fixed_dist(), b, w0.len() as int) == Some(Step::End(wf.len() as int)));
        lemma_syms_unfold(fixed_lit(), fixed_dist(), b, w0.len() as int, data@.take(n as int));
        assert(data@.take(n as int) =~= data@);
        assert(block(b, 3, 1, Seq::empty()) == Some((data@, wf.len() as int, true)));
    }
    Some(out)
}

} // verus!
