//! Canonical Huffman codes: the symbol table built from code lengths, and a
//! decoder proved equal to the spec's `decode_sym`.
//!
//! The table is `puff.c`'s: the number of codes of each length, and the
//! symbols sorted by (length, symbol). Codes of one length are consecutive
//! from `next_code` (3.2.2), so the bits at `p` are the code of a symbol of
//! length `l` exactly when their value `c` is in `next_code(l) ..
//! next_code(l) + bl_count(l)`, and that symbol is the `(c - next_code(l))`th
//! of that length. This needs no prefix-freeness: the spec tries lengths in
//! the same order, whatever the lengths are.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::{bits_val, p2};
use vbits::lsb::*;
use crate::spec::*;

verus! {

// ------------------------------------------------------ ranks of symbols

pub proof fn lemma_count_mono(lens: Seq<u8>, l: nat, a: int, b: int)
    requires 0 <= a <= b,
    ensures count_len(lens, l, a) <= count_len(lens, l, b),
    decreases b - a,
{
    if a < b { lemma_count_mono(lens, l, a, b - 1); }
}

pub proof fn lemma_count_le(lens: Seq<u8>, l: nat, a: int)
    requires 0 <= a,
    ensures count_len(lens, l, a) <= a,
    decreases a,
{
    if a > 0 { lemma_count_le(lens, l, a - 1); }
}

/// A symbol's rank among those of its length is below their number.
pub proof fn lemma_rank_lt(lens: Seq<u8>, n: int)
    requires 0 <= n < lens.len(),
    ensures count_len(lens, lens[n] as nat, n) < bl_count(lens, lens[n] as nat),
{
    lemma_count_mono(lens, lens[n] as nat, n + 1, lens.len() as int);
}

/// Ranks of one length increase with the symbol.
pub proof fn lemma_rank_inj(lens: Seq<u8>, n1: int, n2: int)
    requires 0 <= n1 < n2 < lens.len(), lens[n1] == lens[n2],
    ensures count_len(lens, lens[n1] as nat, n1) < count_len(lens, lens[n2] as nat, n2),
{
    lemma_count_mono(lens, lens[n1] as nat, n1 + 1, n2);
}

/// Every rank below the count is some symbol's.
pub proof fn lemma_rank_exists(lens: Seq<u8>, l: nat, upto: int, r: nat)
    requires 0 <= upto <= lens.len(), r < count_len(lens, l, upto),
    ensures exists|n: int| 0 <= n < upto && lens[n] as nat == l && count_len(lens, l, n) == r,
    decreases upto,
{
    if count_len(lens, l, upto - 1) > r {
        lemma_rank_exists(lens, l, upto - 1, r);
        let n = choose|n: int| 0 <= n < upto - 1 && lens[n] as nat == l && count_len(lens, l, n) == r;
        assert(0 <= n < upto && lens[n] as nat == l && count_len(lens, l, n) == r);
    } else {
        assert(lens[upto - 1] as nat == l && count_len(lens, l, upto - 1) == r);
    }
}

// ------------------------------------------------------- the search

pub open spec fn matches(lens: Seq<u8>, b: Seq<bool>, p: int, l: nat, n: int) -> bool {
    lens[n] as nat == l && code_of(lens, n) == codebits(b, p, l)
}

/// `find_n` finds the first match from `m` on, or says there is none.
pub proof fn lemma_find_n(lens: Seq<u8>, b: Seq<bool>, p: int, l: nat, m: int)
    requires 0 <= m,
    ensures
        match find_n(lens, b, p, l, m) {
            Some(n) => m <= n < lens.len() && matches(lens, b, p, l, n as int),
            None => forall|k: int| m <= k < lens.len() ==> !#[trigger] matches(lens, b, p, l, k),
        },
    decreases lens.len() - m,
{
    if m < lens.len() && !matches(lens, b, p, l, m) {
        lemma_find_n(lens, b, p, l, m + 1);
    }
}

/// At one length, the match is decided by where the code's value falls.
pub proof fn lemma_find_n_range(lens: Seq<u8>, b: Seq<bool>, p: int, l: nat)
    ensures
        ({
            let c = codebits(b, p, l);
            let f = next_code(lens, l);
            match find_n(lens, b, p, l, 0) {
                Some(n) => f <= c < f + bl_count(lens, l) && n < lens.len()
                    && lens[n as int] as nat == l && count_len(lens, l, n as int) == c - f,
                None => !(f <= c < f + bl_count(lens, l)),
            }
        }),
{
    let c = codebits(b, p, l);
    let f = next_code(lens, l);
    lemma_find_n(lens, b, p, l, 0);
    match find_n(lens, b, p, l, 0) {
        Some(n) => {
            lemma_rank_lt(lens, n as int);
        }
        None => {
            if f <= c < f + bl_count(lens, l) {
                lemma_rank_exists(lens, l, lens.len() as int, (c - f) as nat);
                let n = choose|n: int| 0 <= n < lens.len() && lens[n] as nat == l
                    && count_len(lens, l, n) == (c - f) as nat;
                assert(matches(lens, b, p, l, n));
            }
        }
    }
}

// --------------------------------------------------------- the table

/// A decoding table for `lens`: codes of each length, and the symbols in
/// (length, symbol) order, `offs[l]` the first of length `l`.
pub struct Huff {
    pub count: [u16; 16],
    pub offs: [u16; 16],
    pub syms: Vec<u16>,
}

pub open spec fn huff_wf(h: &Huff, lens: Seq<u8>) -> bool {
    &&& lens.len() <= 1024
    &&& lens_ok(lens)
    &&& forall|l: int| 1 <= l <= 15 ==> #[trigger] h.count[l] as nat == bl_count(lens, l as nat)
    &&& h.offs[1] == 0
    &&& forall|l: int| 1 <= l < 15 ==> #[trigger] h.offs[l + 1] as nat == h.offs[l] + h.count[l]
    &&& h.offs[15] + h.count[15] == h.syms@.len()
    &&& h.syms@.len() <= 1024
    &&& forall|n: int| 0 <= n < lens.len() && 1 <= lens[n] ==>
            (h.offs[lens[n] as int] + count_len(lens, lens[n] as nat, n) < h.syms@.len()
             && h.syms@[h.offs[lens[n] as int] + count_len(lens, lens[n] as nat, n)] == n)
}

proof fn lemma_offs_order(h: &Huff, lens: Seq<u8>, a: int, b: int)
    requires huff_wf(h, lens), 1 <= a < b <= 15,
    ensures h.offs[a] + h.count[a] <= h.offs[b],
    decreases b - a,
{
    if b > a + 1 {
        lemma_offs_order(h, lens, a, b - 1);
        assert(h.offs[(b - 1) + 1] as nat == h.offs[b - 1] + h.count[b - 1]);
    } else {
        assert(h.offs[a + 1] as nat == h.offs[a] + h.count[a]);
    }
}

pub proof fn lemma_offs_end(h: &Huff, lens: Seq<u8>, a: int)
    requires huff_wf(h, lens), 1 <= a <= 15,
    ensures h.offs[a] + h.count[a] <= h.syms@.len(),
{
    if a < 15 { lemma_offs_order(h, lens, a, 15); }
}

/// The rank-`r` symbol of length `l` is at `offs[l] + r`.
proof fn lemma_syms_at(h: &Huff, lens: Seq<u8>, l: nat, r: nat)
    requires huff_wf(h, lens), 1 <= l <= 15, r < bl_count(lens, l),
    ensures
        exists|n: int| 0 <= n < lens.len() && lens[n] as nat == l && count_len(lens, l, n) == r
            && h.syms@[h.offs[l as int] + r] == n,
{
    lemma_rank_exists(lens, l, lens.len() as int, r);
    let n = choose|n: int| 0 <= n < lens.len() && lens[n] as nat == l && count_len(lens, l, n) == r;
    assert(1 <= lens[n]);
}

pub proof fn lemma_count_step(lens: Seq<u8>, n: int)
    requires 0 <= n < lens.len(),
    ensures
        forall|l: nat| #[trigger] count_len(lens, l, n + 1)
            == count_len(lens, l, n) + (if lens[n] as nat == l { 1nat } else { 0nat }),
{
}

/// The number of the first `upto` symbols with lengths 1 to `l`.
pub open spec fn tot(lens: Seq<u8>, l: nat, upto: int) -> nat
    decreases l,
{
    if l == 0 { 0 } else { tot(lens, (l - 1) as nat, upto) + count_len(lens, l, upto) }
}

proof fn lemma_tot_mono(lens: Seq<u8>, a: nat, b: nat, upto: int)
    requires a <= b,
    ensures tot(lens, a, upto) <= tot(lens, b, upto),
    decreases b - a,
{
    if a < b { lemma_tot_mono(lens, a, (b - 1) as nat, upto); }
}

proof fn lemma_tot_step(lens: Seq<u8>, l: nat, n: int)
    requires 0 <= n < lens.len(),
    ensures tot(lens, l, n + 1) == tot(lens, l, n) + (if 1 <= lens[n] <= l { 1nat } else { 0nat }),
    decreases l,
{
    if l > 0 { lemma_tot_step(lens, (l - 1) as nat, n); }
}

proof fn lemma_tot_zero(lens: Seq<u8>, l: nat)
    ensures tot(lens, l, 0) == 0,
    decreases l,
{
    if l > 0 { lemma_tot_zero(lens, (l - 1) as nat); }
}

/// Every symbol has one length, so the counts add up to the symbols.
proof fn lemma_tot_all(lens: Seq<u8>, upto: int)
    requires 0 <= upto <= lens.len(), lens_ok(lens),
    ensures count_len(lens, 0, upto) + tot(lens, 15, upto) == upto,
    decreases upto,
{
    if upto == 0 {
        lemma_tot_zero(lens, 15);
    } else {
        lemma_tot_all(lens, upto - 1);
        lemma_tot_step(lens, 15, upto - 1);
        assert(lens[upto - 1] <= 15);
        assert(count_len(lens, 0, upto) == count_len(lens, 0, upto - 1)
            + (if lens[upto - 1] as nat == 0 { 1nat } else { 0nat }));
    }
}

/// Build the table. Lengths above 15 are not DEFLATE's; the caller has
/// checked.
pub fn build(lens: &[u8]) -> (h: Huff)
    requires lens.len() <= 1024, lens_ok(lens@),
    ensures huff_wf(&h, lens@),
{
    let ghost gl = lens@;
    let n = lens.len();
    let mut count = [0u16; 16];
    let mut i: usize = 0;
    while i < n
        invariant
            n == lens.len(), gl == lens@, i <= n, n <= 1024, lens_ok(gl),
            forall|l: int| 0 <= l < 16 ==> #[trigger] count[l] as nat == count_len(gl, l as nat, i as int),
        decreases n - i,
    {
        let l = lens[i] as usize;
        assert(lens[i as int] <= 15);
        proof {
            lemma_count_step(gl, i as int);
            lemma_count_le(gl, l as nat, i as int);
        }
        count[l] = count[l] + 1;
        i = i + 1;
    }
    proof { lemma_tot_all(gl, n as int); }
    let mut offs = [0u16; 16];
    let mut l: usize = 1;
    while l < 15
        invariant
            1 <= l <= 15, n <= 1024, n == gl.len(), lens_ok(gl),
            count_len(gl, 0, n as int) + tot(gl, 15, n as int) == n,
            forall|l: int| 0 <= l < 16 ==> #[trigger] count[l] as nat == count_len(gl, l as nat, n as int),
            forall|j: int| 1 <= j <= l ==> #[trigger] offs[j] as nat == tot(gl, (j - 1) as nat, n as int),
        decreases 15 - l,
    {
        proof { lemma_tot_mono(gl, l as nat, 15, n as int); }
        offs[l + 1] = offs[l] + count[l];
        l = l + 1;
    }
    proof { lemma_tot_mono(gl, 15, 15, n as int); }
    let total: usize = (offs[15] + count[15]) as usize;
    let mut syms: Vec<u16> = vec![0u16; total];
    let mut cur = offs;
    let mut i: usize = 0;
    while i < n
        invariant
            n == lens.len(), gl == lens@, i <= n, n <= 1024, lens_ok(gl),
            forall|l: int| 0 <= l < 16 ==> #[trigger] count[l] as nat == count_len(gl, l as nat, n as int),
            forall|j: int| 1 <= j <= 15 ==> #[trigger] offs[j] as nat == tot(gl, (j - 1) as nat, n as int),
            total == tot(gl, 15, n as int), syms@.len() == total, total <= 1024,
            forall|l: int| 1 <= l <= 15 ==> #[trigger] cur[l] as nat == offs[l] + count_len(gl, l as nat, i as int),
            forall|m: int| 0 <= m < i && 1 <= gl[m] ==>
                (offs[gl[m] as int] + count_len(gl, gl[m] as nat, m) < syms@.len()
                 && syms@[offs[gl[m] as int] + count_len(gl, gl[m] as nat, m)] == m),
        decreases n - i,
    {
        let l = lens[i] as usize;
        proof { lemma_count_step(gl, i as int); }
        if l != 0 {
            assert(lens[i as int] <= 15);
            proof {
                // the slot is inside length l's range
                lemma_count_mono(gl, l as nat, i as int + 1, n as int);
                assert(tot(gl, l as nat, n as int) == tot(gl, (l - 1) as nat, n as int) + count[l as int]);
                lemma_tot_mono(gl, l as nat, 15, n as int);
                assert(offs[l as int] as nat == tot(gl, (l - 1) as nat, n as int));
                assert(count_len(gl, l as nat, i as int + 1) == count_len(gl, l as nat, i as int) + 1);
                assert(cur[l as int] + 1 <= total);
                // and no earlier symbol is in it
                assert forall|m: int| 0 <= m < i && 1 <= gl[m] implies
                    offs[gl[m] as int] + count_len(gl, gl[m] as nat, m) != cur[l as int] by {
                    let lm = gl[m] as int;
                    assert(gl[m] <= 15);
                    lemma_count_mono(gl, lm as nat, m + 1, n as int);
                    assert(tot(gl, lm as nat, n as int) == tot(gl, (lm - 1) as nat, n as int) + count[lm]);
                    if lm < l as int {
                        lemma_tot_mono(gl, lm as nat, (l - 1) as nat, n as int);
                    } else if lm > l as int {
                        lemma_tot_mono(gl, l as nat, (lm - 1) as nat, n as int);
                    } else {
                        lemma_count_mono(gl, l as nat, m + 1, i as int);
                    }
                }
            }
            syms.set(cur[l] as usize, i as u16);
            cur[l] = cur[l] + 1;
        }
        i = i + 1;
    }
    let h = Huff { count, offs, syms };
    proof {
        assert forall|l: int| 1 <= l < 15 implies #[trigger] h.offs[l + 1] as nat == h.offs[l] + h.count[l] by {
            assert(tot(gl, l as nat, n as int) == tot(gl, (l - 1) as nat, n as int) + count[l]);
        }
        assert(tot(gl, 15, n as int) == tot(gl, 14, n as int) + count[15]);
    }
    h
}

// ------------------------------------------------------- decoding

/// The largest input, in bytes, whose bit count fits a `usize` comfortably.
pub open spec fn max_input() -> nat { 0x1000_0000_0000_0000 }

/// The value of the first `l` code bits grows one bit at a time.
proof fn lemma_codebits_step(b: Seq<bool>, p: int, l: nat)
    requires 0 <= p, 1 <= l, p + l <= b.len(),
    ensures codebits(b, p, l) == 2 * codebits(b, p, (l - 1) as nat) + (if b[p + l - 1] { 1nat } else { 0nat }),
{
    let s = b.subrange(p, p + l);
    assert(s.drop_last() =~= b.subrange(p, p + l - 1));
}

/// Bit `j` of a peeked window is bit `pos + j` of the stream.
proof fn lemma_peek_bit(buf: Seq<u8>, pos: int, n: nat, w: u64, j: nat)
    requires
        0 <= pos, j < n, n <= 56, pos + j < 8 * buf.len(),
        w as nat == lval(lview(buf).subrange(pos, pos + n)),
    ensures
        lbits(buf)[pos + j] == ((w >> (j as u64)) & 1u64 == 1u64),
{
    let t = lview(buf).subrange(pos, pos + n);
    lemma_lval_bit(t, j as int);
    vbits::prim_read::lemma_p2_eq_pow2(j);
    vstd::bits::lemma_u64_shr_is_div(w, j as u64);
    let x = w >> (j as u64);
    assert((x & 1u64 == 1u64) == (x % 2 == 1)) by (bit_vector);
}

proof fn lemma_p2_15()
    ensures p2(14) == 16384, p2(15) == 32768,
{
    reveal_with_fuel(p2, 16);
}

/// Bits `j < 15` of `w` are the bits of `b` from `p`, as far as `b` goes.
pub open spec fn win_ok(b: Seq<bool>, p: int, w: u64) -> bool {
    forall|j: int| 0 <= j < 15 && p + j < b.len() ==>
        #[trigger] b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64)
}

/// The spec's `find_sym` from length 1 at `p`, computed as `puff.c` does,
/// one bit at a time, from a window `w` of the bits there: the symbol and
/// its code length.
#[inline(never)]
pub fn decode_from(h: &Huff, Ghost(lens): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>,
                   p: usize, avail: usize, w: u64, l0: u64, code0: u64, first0: u64, index0: u64)
    -> (r: Option<(u16, u64)>)
    requires
        huff_wf(h, lens), p + avail == b.len(), win_ok(b, p as int, w),
        1 <= l0 <= 16, l0 - 1 <= avail,
        first0 as nat == next_code(lens, l0 as nat), first0 as nat <= 2048 * (p2((l0 - 1) as nat) - 1),
        l0 <= 15 ==> index0 as nat == h.offs[l0 as int], index0 <= 1024,
        code0 as nat == codebits(b, p as int, (l0 - 1) as nat),
        find_sym(lens, b, p as int, 1) == find_sym(lens, b, p as int, l0 as nat),
    ensures
        match r {
            Some((s, l)) => find_sym(lens, b, p as int, 1) == Some((s as nat, p + l))
                && 1 <= l <= 15,
            None => find_sym(lens, b, p as int, 1) is None,
        },
{
    let mut code: u64 = code0;
    let mut first: u64 = first0;
    let mut index: u64 = index0;
    let mut l: u64 = l0;
    proof { lemma_p2_15(); }
    while l <= 15
        invariant
            huff_wf(h, lens), p + avail == b.len(), win_ok(b, p as int, w),
            1 <= l <= 16,
            p2(14) == 16384, p2(15) == 32768,
            first as nat == next_code(lens, l as nat),
            first as nat <= 2048 * (p2((l - 1) as nat) - 1),
            l <= 15 ==> index as nat == h.offs[l as int],
            index <= 1024,
            code as nat == codebits(b, p as int, (l - 1) as nat),
            l - 1 <= avail,
            find_sym(lens, b, p as int, 1) == find_sym(lens, b, p as int, l as nat),
        decreases 16 - l,
    {
        if l as usize > avail {
            // the code would run past the input, and so would a longer one
            return None;
        }
        let sh: u64 = l - 1;
        let bit = (w >> sh) & 1;
        proof {
            assert(b[p + sh as int] == ((w >> sh) & 1u64 == 1u64));
            lemma_codebits_step(b, p as int, l as nat);
            assert(bit == 0 || bit == 1) by (bit_vector) requires bit == (w >> sh) & 1;
            vbits::bitspec::lemma_bits_val_bound(b.subrange(p as int, p as int + (l - 1)));
            vbits::prim_read::lemma_p2_mono((l - 1) as nat, 14);
            lemma_find_n_range(lens, b, p as int, l as nat);
            assert(h.count[l as int] as nat == bl_count(lens, l as nat));
            lemma_count_le(lens, l as nat, lens.len() as int);
        }
        code = 2 * code + bit;
        let count = h.count[l as usize] as u64;
        if code >= first && code < first + count {
            let k = (index + (code - first)) as usize;
            proof {
                let n = find_n(lens, b, p as int, l as nat, 0).unwrap() as int;
                assert(1 <= lens[n]);
                assert(h.syms@[h.offs[lens[n] as int] + count_len(lens, lens[n] as nat, n)] == n);
            }
            return Some((h.syms[k], l));
        }
        proof {
            if l < 15 {
                assert(h.offs[l as int + 1] as nat == h.offs[l as int] + h.count[l as int]);
                lemma_offs_end(h, lens, l as int + 1);
            }
            vbits::prim_read::lemma_p2_mono(l as nat, 15);
            assert(p2(l as nat) == 2 * p2((l - 1) as nat));
            vbits::bitspec::lemma_p2_pos((l - 1) as nat);
        }
        index = index + count;
        first = 2 * (first + count);
        l = l + 1;
    }
    None
}

/// From length 1: `decode_from` with nothing read yet.
pub fn decode_bits(h: &Huff, Ghost(lens): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>,
                   p: usize, avail: usize, w: u64) -> (r: Option<(u16, u64)>)
    requires huff_wf(h, lens), p + avail == b.len(), win_ok(b, p as int, w),
    ensures
        match r {
            Some((s, l)) => find_sym(lens, b, p as int, 1) == Some((s as nat, p + l))
                && 1 <= l <= 15,
            None => find_sym(lens, b, p as int, 1) is None,
        },
{
    proof {
        assert(b.subrange(p as int, p as int) =~= Seq::<bool>::empty());
        assert(codebits(b, p as int, 0) == 0);
        assert(p2(0) == 1) by { reveal_with_fuel(p2, 1); }
    }
    decode_from(h, Ghost(lens), Ghost(b), p, avail, w, 1, 0, 0, 0)
}

/// A peeked window is a window of the stream.
proof fn lemma_peek_win(buf: Seq<u8>, pos: int, w: u64)
    requires 0 <= pos, w as nat == lval(lview(buf).subrange(pos, pos + 15)),
    ensures win_ok(lbits(buf), pos, w),
{
    assert forall|j: int| 0 <= j < 15 && pos + j < lbits(buf).len() implies
        #[trigger] lbits(buf)[pos + j] == ((w >> (j as u64)) & 1u64 == 1u64) by {
        lemma_peek_bit(buf, pos, 15, w, j as nat);
    }
}

/// The symbol whose code starts at `pos`, and the position after it, one
/// bit at a time: the spec's `decode_sym`.
pub fn decode_slow(h: &Huff, Ghost(lens): Ghost<Seq<u8>>, buf: &[u8], pos: usize) -> (r: Option<(u16, usize)>)
    requires huff_wf(h, lens), buf.len() < max_input(), pos <= 8 * buf.len(),
    ensures
        match r {
            Some((s, q)) => decode_sym(lens, lbits(buf@), pos as int) == Some((s as nat, q as int)),
            None => decode_sym(lens, lbits(buf@), pos as int) is None,
        },
{
    let w = peek_lsb(buf, pos, 15);
    proof { lemma_peek_win(buf@, pos as int, w); }
    match decode_bits(h, Ghost(lens), Ghost(lbits(buf@)), pos, 8 * buf.len() - pos, w) {
        Some((s, l)) => Some((s, pos + l as usize)),
        None => None,
    }
}

// ------------------------------------------------------- the fast table

/// The first `n` bits of `w`, LSB first: what a table index stands for.
pub open spec fn wbits(w: u64, n: nat) -> Seq<bool> {
    Seq::new(n, |j: int| (w >> (j as u64)) & 1u64 == 1u64)
}

/// A table entry for a window: 0, or the length of the code the window
/// starts with times 1024 plus its symbol. (A 0 says nothing: the decoder
/// then reads the code one bit at a time.)
pub open spec fn entry_ok(e: u16, lens: Seq<u8>, wb: Seq<bool>) -> bool {
    e != 0 ==> ({
        let s = (e % 1024) as nat;
        let l = (e / 1024) as nat;
        1 <= l <= 15 && find_sym(lens, wb, 0, 1) == Some((s, l as int))
    })
}

/// The table has an entry for every `tb`-bit window (opaque: revealed where
/// the table is built and read).
#[verifier::opaque]
pub open spec fn fast_wf(tbl: Seq<u16>, lens: Seq<u8>, tb: nat) -> bool {
    &&& tbl.len() == 1024
    &&& forall|w: int| 0 <= w < p2(tb) ==> entry_ok(#[trigger] tbl[w], lens, wbits(w as u64, tb))
}

/// A found symbol is one of the code's.
pub proof fn lemma_find_sym_sym(lens: Seq<u8>, b: Seq<bool>, p: int, l: nat)
    ensures find_sym(lens, b, p, l) matches Some((s, q)) ==> s < lens.len(),
    decreases 16 - l,
{
    if !(l == 0 || l > maxbits() || p < 0 || p + l > b.len()) {
        lemma_find_n(lens, b, p, l, 0);
        lemma_find_sym_sym(lens, b, p, l + 1);
    }
}

/// Windows that agree on their low `m` bits agree on an entry whose code is
/// at most `m` bits long.
proof fn lemma_entry_move(e: u16, lens: Seq<u8>, w1: u64, n1: nat, w2: u64, n2: nat, m: nat)
    requires
        entry_ok(e, lens, wbits(w1, n1)), e != 0 ==> e / 1024 <= m,
        m <= n1, m <= n2, n1 <= 64, n2 <= 64,
        forall|j: u64| j < m ==> #[trigger] ((w1 >> j) & 1u64) == ((w2 >> j) & 1u64),
    ensures entry_ok(e, lens, wbits(w2, n2)),
{
    if e != 0 {
        let s = (e % 1024) as nat;
        let l = (e / 1024) as nat;
        let b1 = wbits(w1, n1);
        let b2 = wbits(w2, n2);
        assert forall|j: int| 0 <= j < l implies #[trigger] b2[0 + j] == b1[0 + j] by {
            assert(((w1 >> (j as u64)) & 1u64) == ((w2 >> (j as u64)) & 1u64));
        }
        lemma_find_sym_agree(lens, b2, 0, b1, 0, 1, s, l);
    }
}

/// Two bit strings that agree on a found code's bits find the same code.
pub proof fn lemma_find_sym_agree(lens: Seq<u8>, b1: Seq<bool>, p1: int, b2: Seq<bool>, p2: int,
                                  l0: nat, s: nat, m: nat)
    requires
        find_sym(lens, b2, p2, l0) == Some((s, p2 + m)),
        1 <= l0, 0 <= p1, 0 <= p2, p1 + m <= b1.len(),
        forall|j: int| 0 <= j < m ==> #[trigger] b1[p1 + j] == b2[p2 + j],
    ensures find_sym(lens, b1, p1, l0) == Some((s, p1 + m)),
    decreases 16 - l0,
{
    lemma_find_sym_adv(lens, b2, p2, l0);
    assert(b1.subrange(p1, p1 + l0) =~= b2.subrange(p2, p2 + l0)) by {
        assert forall|j: int| 0 <= j < l0 implies #[trigger] b1.subrange(p1, p1 + l0)[j] == b2.subrange(p2, p2 + l0)[j] by {
            assert(b1[p1 + j] == b2[p2 + j]);
        }
    }
    lemma_find_n_same(lens, b1, p1, b2, p2, l0, 0);
    if find_n(lens, b2, p2, l0, 0) is None {
        lemma_find_sym_agree(lens, b1, p1, b2, p2, l0 + 1, s, m);
    }
}

/// With no code of at most `v.len()` bits in `v`, the bits at `p`, the
/// search at `p` can start past them.
pub proof fn lemma_find_sym_past(lens: Seq<u8>, v: Seq<bool>, b: Seq<bool>, p: int, l: nat)
    requires
        1 <= l <= v.len() + 1, v.len() <= 15, find_sym(lens, v, 0, l) is None,
        0 <= p, p + v.len() <= b.len(),
        forall|j: int| 0 <= j < v.len() ==> #[trigger] b[p + j] == v[j],
    ensures find_sym(lens, b, p, l) == find_sym(lens, b, p, (v.len() + 1) as nat),
    decreases v.len() + 1 - l,
{
    if l <= v.len() {
        assert(b.subrange(p, p + l) =~= v.subrange(0, l as int)) by {
            assert forall|j: int| 0 <= j < l implies #[trigger] b.subrange(p, p + l)[j] == v.subrange(0, l as int)[j] by {
                assert(b[p + j] == v[j]);
            }
        }
        lemma_find_n_same(lens, b, p, v, 0, l, 0);
        lemma_find_sym_past(lens, v, b, p, l + 1);
    }
}

proof fn lemma_find_n_same(lens: Seq<u8>, b1: Seq<bool>, p1: int, b2: Seq<bool>, p2: int, l: nat, n: int)
    requires codebits(b1, p1, l) == codebits(b2, p2, l),
    ensures find_n(lens, b1, p1, l, n) == find_n(lens, b2, p2, l, n),
    decreases lens.len() - n,
{
    if 0 <= n < lens.len() {
        lemma_find_n_same(lens, b1, p1, b2, p2, l, n + 1);
    }
}

/// How many bits a table decodes: at most 10, the table's index.
pub open spec fn tb_ok(tb: u64) -> bool { 1 <= tb <= 10 }

/// A code's tables: the canonical one, and the fast one for `tb`-bit
/// windows (a code's longest length, at most 10, is enough).
pub struct Code {
    pub h: Huff,
    pub tbl: [u16; 1024],
    pub tb: u64,
    pub mask: u64,
    /// For a window with no table entry, its `tb` bits read as a code, and
    /// the first code of `tb + 1` bits: where the search for a longer code
    /// resumes.
    pub code: [u16; 1024],
    pub first1: u64,
}

pub open spec fn code_wf(c: &Code, lens: Seq<u8>) -> bool {
    &&& huff_wf(&c.h, lens)
    &&& tb_ok(c.tb) && c.mask == (1u64 << c.tb) - 1
    &&& fast_wf(c.tbl@, lens, c.tb as nat)
    &&& res_wf(c.tbl@, c.code@, lens, c.tb as nat)
    &&& c.first1 as nat == next_code(lens, (c.tb + 1) as nat) && c.first1 as nat <= 2048 * (p2(c.tb as nat) - 1)
}

/// Where the table has no entry, no code of at most `tb` bits starts the
/// window, and `code` holds its `tb` bits read as a code.
#[verifier::opaque]
pub open spec fn res_wf(tbl: Seq<u16>, code: Seq<u16>, lens: Seq<u8>, tb: nat) -> bool {
    &&& code.len() == 1024
    &&& forall|w: int| 0 <= w < p2(tb) && #[trigger] tbl[w] == 0 ==>
            find_sym(lens, wbits(w as u64, tb), 0, 1) is None && code[w] as nat == codebits(wbits(w as u64, tb), 0, tb)
}

/// Nothing below `m` matches, so the search from `l0` is the search from `m`.
pub proof fn lemma_find_sym_skip(lens: Seq<u8>, b: Seq<bool>, p: int, l0: nat, m: nat)
    requires
        1 <= l0 <= m <= 16, 0 <= p, p + m - 1 <= b.len(),
        forall|l: nat| l0 <= l < m ==> #[trigger] find_n(lens, b, p, l, 0) is None,
    ensures find_sym(lens, b, p, l0) == find_sym(lens, b, p, m),
    decreases m - l0,
{
    if l0 < m {
        assert(find_n(lens, b, p, l0, 0) is None);
        lemma_find_sym_skip(lens, b, p, l0 + 1, m);
    }
}

/// On a window that has no code, no length up to the window's matches.
proof fn lemma_find_sym_none(lens: Seq<u8>, b: Seq<bool>, l0: nat, k: nat)
    requires find_sym(lens, b, 0, l0) is None, b.len() == k, 1 <= l0, k <= 15,
    ensures forall|l: nat| l0 <= l <= k ==> #[trigger] find_n(lens, b, 0, l, 0) is None,
    decreases k + 1 - l0,
{
    if l0 <= k {
        assert(find_n(lens, b, 0, l0, 0) is None);
        lemma_find_sym_none(lens, b, l0 + 1, k);
    }
}

/// Windows agreeing on their first `l` bits have the same first `l` code bits.
proof fn lemma_wbits_codebits(w1: u64, k1: nat, w2: u64, k2: nat, l: nat)
    requires l <= k1, l <= k2, k1 <= 64, k2 <= 64,
        forall|j: u64| j < l ==> #[trigger] ((w1 >> j) & 1u64) == ((w2 >> j) & 1u64),
    ensures codebits(wbits(w1, k1), 0, l) == codebits(wbits(w2, k2), 0, l),
{
    assert(wbits(w1, k1).subrange(0, l as int) =~= wbits(w2, k2).subrange(0, l as int)) by {
        assert forall|j: int| 0 <= j < l implies
            #[trigger] wbits(w1, k1).subrange(0, l as int)[j] == wbits(w2, k2).subrange(0, l as int)[j] by {
            assert(((w1 >> (j as u64)) & 1u64) == ((w2 >> (j as u64)) & 1u64));
        }
    }
}

/// A table entry, and for a window with no code the value of its bits read
/// as a code, for the windows of `k` bits.
pub open spec fn lvl_ok(e: u16, c: u16, lens: Seq<u8>, w: u64, k: nat) -> bool {
    &&& entry_ok(e, lens, wbits(w, k))
    &&& e != 0 ==> e / 1024 <= k
    &&& e == 0 ==> find_sym(lens, wbits(w, k), 0, 1) is None && c as nat == codebits(wbits(w, k), 0, k)
}

/// A window of `k + 1` bits whose first `k` have no code: the entry for a
/// code of exactly `k + 1` bits, or none.
proof fn lemma_level_miss(h: &Huff, lens: Seq<u8>, base: u64, w: u64, k: u64, c: u16, bit: u64,
                          first: u64, count: u64, index: u64, ee: u16)
    requires
        huff_wf(h, lens), k < 10, p2(15) == 32768,
        lvl_ok(0, c, lens, base, k as nat),
        forall|j: u64| j < k ==> #[trigger] ((w >> j) & 1u64) == ((base >> j) & 1u64),
        (w >> k) & 1u64 == bit, bit <= 1,
        first as nat == next_code(lens, (k + 1) as nat), count as nat == bl_count(lens, (k + 1) as nat),
        index == h.offs[(k + 1) as int], index + count <= h.syms@.len(),
        ee == (if 2 * (c as int) + bit >= first && 2 * (c as int) + bit < first + count {
            ((k + 1) * 1024 + h.syms@[index + (2 * (c as int) + bit - first)]) as u16
        } else { 0u16 }),
    ensures lvl_ok(ee, (2 * (c as int) + bit) as u16, lens, w, (k + 1) as nat),
{
    let l = (k + 1) as nat;
    let wb = wbits(w, l);
    let cc = 2 * (c as int) + bit;
    lemma_find_sym_none(lens, wbits(base, k as nat), 1, k as nat);
    lemma_wbits_codebits(w, l, base, k as nat, k as nat);
    lemma_codebits_step(wb, 0, l);
    assert(wb[0 + l - 1] == ((w >> k) & 1u64 == 1u64));
    assert(codebits(wb, 0, l) == cc);
    assert forall|ll: nat| 1 <= ll < l implies #[trigger] find_n(lens, wb, 0, ll, 0) is None by {
        assert forall|j: u64| j < ll implies #[trigger] ((w >> j) & 1u64) == ((base >> j) & 1u64) by {}
        lemma_wbits_codebits(w, l, base, k as nat, ll);
        lemma_find_n_same(lens, wb, 0, wbits(base, k as nat), 0, ll, 0);
    }
    lemma_find_sym_skip(lens, wb, 0, 1, l);
    lemma_find_n_range(lens, wb, 0, l);
    lemma_find_sym_sym(lens, wb, 0, 1);
    vbits::bitspec::lemma_bits_val_bound(wb.subrange(0, l as int));
    vbits::prim_read::lemma_p2_mono(l, 10);
    reveal_with_fuel(p2, 11);
    if cc >= first && cc < first + count {
        let n = find_n(lens, wb, 0, l, 0).unwrap() as int;
        assert(1 <= lens[n]);
        assert(h.syms@[h.offs[lens[n] as int] + count_len(lens, lens[n] as nat, n)] == n);
        assert(find_sym(lens, wb, 0, l) == Some((n as nat, l as int)));
    } else {
        assert(find_sym(lens, wb, 0, l + 1) is None);
    }
}

/// The table for 10-bit windows, one window length at a time: a window of
/// `k + 1` bits has the entry of its first `k` if that has a code, and
/// otherwise a code of exactly `k + 1` bits or none, decided by the value of
/// its bits (as `decode_bits` decides it at that length).
pub fn build_table(h: &Huff, Ghost(lens): Ghost<Seq<u8>>, tb: u64) -> (tbl: [u16; 1024])
    requires huff_wf(h, lens), tb_ok(tb),
    ensures fast_wf(tbl@, lens, tb as nat),
{
    let (tbl, _, _) = build_table_c(h, Ghost(lens), tb);
    proof {
        reveal(fast_wf);
        assert forall|w: int| 0 <= w < p2(tb as nat) implies
            entry_ok(#[trigger] tbl@[w], lens, wbits(w as u64, tb as nat)) by {}
    }
    tbl
}

/// The table, each window's code so far where the table has none, and the
/// first code of `tb + 1` bits.
#[inline(always)]
pub fn build_table_c(h: &Huff, Ghost(lens): Ghost<Seq<u8>>, tb: u64) -> (r: ([u16; 1024], [u16; 1024], u64))
    requires huff_wf(h, lens), tb_ok(tb),
    ensures
        r.0@.len() == 1024, r.1@.len() == 1024,
        forall|w: int| 0 <= w < p2(tb as nat) ==> lvl_ok(#[trigger] r.0@[w], r.1@[w], lens, w as u64, tb as nat),
        r.2 as nat == next_code(lens, (tb + 1) as nat), r.2 as nat <= 2048 * (p2(tb as nat) - 1),
{
    let mut tbl = [0u16; 1024];
    let mut code = [0u16; 1024];
    let mut first: u64 = 0;   // next_code(k + 1)
    let mut k: u64 = 0;
    proof {
        lemma_p2_15();
        let wb = wbits(0, 0);
        assert(find_sym(lens, wb, 0, 1) is None);
        assert(wb.subrange(0, 0) =~= Seq::<bool>::empty());
        assert(codebits(wb, 0, 0) == 0);
        reveal_with_fuel(p2, 11);
    }
    while k < tb
        invariant
            huff_wf(h, lens), k <= tb, tb_ok(tb), tbl@.len() == 1024, code@.len() == 1024,
            p2(14) == 16384, p2(15) == 32768, p2(10) == 1024,
            first as nat == next_code(lens, (k + 1) as nat),
            first as nat <= 2048 * (p2(k as nat) - 1), p2(k as nat) <= 1024, 1 <= p2(k as nat),
            forall|w: int| 0 <= w < p2(k as nat) ==>
                lvl_ok(#[trigger] tbl@[w], code@[w], lens, w as u64, k as nat),
        decreases 10 - k,
    {
        let half: u64 = 1u64 << k;
        let l: u64 = k + 1;
        let count = h.count[l as usize] as u64;
        let index = h.offs[l as usize] as u64;
        proof {
            vbits::prim_read::lemma_p2_eq_pow2(k as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(k as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, k);
            vbits::prim_read::lemma_p2_mono(k as nat, 9);
            reveal_with_fuel(p2, 11);
            assert(half as nat == p2(k as nat));
            assert(p2(l as nat) == 2 * p2(k as nat));
            lemma_count_le(lens, l as nat, lens.len() as int);
            lemma_offs_end(h, lens, l as int);
        }
        let mut base: u64 = 0;
        while base < half
            invariant
                huff_wf(h, lens), k < 10, l == k + 1, tbl@.len() == 1024, code@.len() == 1024,
                half as nat == p2(k as nat), half <= 512, half == (1u64 << k), p2(15) == 32768,
                p2(l as nat) == 2 * p2(k as nat),
                first as nat == next_code(lens, l as nat), first as nat <= 2048 * 512,
                count as nat == bl_count(lens, l as nat), count <= 1024,
                index == h.offs[l as int], index + count <= h.syms@.len(),
                base <= half,
                forall|w: int| base <= w < half ==>
                    lvl_ok(#[trigger] tbl@[w], code@[w], lens, w as u64, k as nat),
                forall|w: int| (0 <= w < base || half <= w < half + base) ==>
                    lvl_ok(#[trigger] tbl@[w], code@[w], lens, w as u64, l as nat),
            decreases half - base,
        {
            let w1 = base + half;
            let e = tbl[base as usize];
            let c = code[base as usize];
            proof {
                assert(lvl_ok(tbl@[base as int], code@[base as int], lens, base, k as nat));
                assert(base < half && w1 < 2 * half);
                assert forall|j: u64| j < k implies #[trigger] ((w1 >> j) & 1u64) == ((base >> j) & 1u64) by {
                    assert(((w1 >> j) & 1u64) == ((base >> j) & 1u64)) by (bit_vector)
                        requires w1 == base + half, half == (1u64 << k), base < half, j < k, k < 10;
                }
                assert((w1 >> k) & 1u64 == 1u64 && (base >> k) & 1u64 == 0u64) by (bit_vector)
                    requires w1 == base + half, half == (1u64 << k), base < half, k < 10;
            }
            if e != 0 {
                proof {
                    assert forall|j: u64| j < (e / 1024) as nat implies
                        #[trigger] ((base >> j) & 1u64) == ((base >> j) & 1u64) by {}
                    lemma_entry_move(e, lens, base, k as nat, base, l as nat, (e / 1024) as nat);
                    assert forall|j: u64| j < (e / 1024) as nat implies
                        #[trigger] ((base >> j) & 1u64) == ((w1 >> j) & 1u64) by {}
                    lemma_entry_move(e, lens, base, k as nat, w1, l as nat, (e / 1024) as nat);
                }
                tbl[w1 as usize] = e;
            } else {
                // no code of at most k bits: one of exactly k + 1, or none
                proof {
                    lemma_find_sym_none(lens, wbits(base, k as nat), 1, k as nat);
                    vbits::bitspec::lemma_bits_val_bound(wbits(base, k as nat).subrange(0, k as int));
                    vbits::prim_read::lemma_p2_mono(k as nat, 9);
                }
                let c0: u64 = 2 * (c as u64);
                let c1: u64 = 2 * (c as u64) + 1;
                let e1 = if c1 >= first && c1 < first + count {
                    let k1 = (index + (c1 - first)) as usize;
                    (l * 1024 + h.syms[k1] as u64) as u16
                } else { 0u16 };
                let e0 = if c0 >= first && c0 < first + count {
                    let k0 = (index + (c0 - first)) as usize;
                    (l * 1024 + h.syms[k0] as u64) as u16
                } else { 0u16 };
                proof {
                    lemma_level_miss(h, lens, base, base, k, c, 0, first, count, index, e0);
                    lemma_level_miss(h, lens, base, w1, k, c, 1, first, count, index, e1);
                }
                tbl[w1 as usize] = e1;
                code[w1 as usize] = c1 as u16;
                tbl[base as usize] = e0;
                code[base as usize] = c0 as u16;
            }
            base = base + 1;
        }
        proof {
            assert(l <= 15);
            lemma_count_le(lens, l as nat, lens.len() as int);
            vbits::prim_read::lemma_p2_mono(l as nat, 10);
            vbits::bitspec::lemma_p2_pos(k as nat);
            assert(p2(l as nat) == 2 * p2(k as nat));
        }
        first = 2 * (first + count);
        k = k + 1;
    }
    (tbl, code, first)
}

/// A code's tables.
pub fn build_code(lens: &[u8], tb: u64) -> (c: Code)
    requires lens.len() <= 1024, lens_ok(lens@), tb_ok(tb),
    ensures code_wf(&c, lens@), c.tb == tb,
{
    let h = build(lens);
    let (tbl, code, first1) = build_table_c(&h, Ghost(lens@), tb);
    proof {
        reveal(fast_wf);
        reveal(res_wf);
        assert forall|w: int| 0 <= w < p2(tb as nat) implies
            entry_ok(#[trigger] tbl@[w], lens@, wbits(w as u64, tb as nat)) by {
            assert(lvl_ok(tbl@[w], code@[w], lens@, w as u64, tb as nat));
        }
        assert forall|w: int| 0 <= w < p2(tb as nat) && #[trigger] tbl@[w] == 0 implies
            find_sym(lens@, wbits(w as u64, tb as nat), 0, 1) is None
            && code@[w] as nat == codebits(wbits(w as u64, tb as nat), 0, tb as nat) by {
            assert(lvl_ok(tbl@[w], code@[w], lens@, w as u64, tb as nat));
        }
    }
    assert(1u64 << tb >= 2) by (bit_vector) requires 1 <= tb <= 10;
    Code { h, tbl, tb, mask: (1u64 << tb) - 1, code, first1 }
}

/// Bits `j < k` of `w` are the bits of `b` from `p`, as far as `b` goes.
pub open spec fn win_k(b: Seq<bool>, p: int, w: u64, k: nat) -> bool {
    forall|j: int| 0 <= j < k && p + j < b.len() ==>
        #[trigger] b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64)
}

/// Shifting a window moves it along the stream.
pub proof fn lemma_win_shift(b: Seq<bool>, p: int, w: u64, k: nat, m: u64)
    requires win_k(b, p, w, k), m <= k, k <= 64,
    ensures win_k(b, p + m, w >> m, (k - m) as nat),
{
    assert forall|j: int| 0 <= j < k - m && p + m + j < b.len() implies
        #[trigger] b[p + m + j] == (((w >> m) >> (j as u64)) & 1u64 == 1u64) by {
        let jj = j as u64;
        assert(((w >> m) >> jj) & 1u64 == (w >> ((m + jj) as u64)) & 1u64) by (bit_vector)
            requires m + jj < 64;
        assert(b[p + (m + j)] == ((w >> ((m + j) as u64)) & 1u64 == 1u64));
    }
}

/// A 15-bit window is what `decode_bits` wants.
pub proof fn lemma_win_15(b: Seq<bool>, p: int, w: u64, k: nat)
    requires win_k(b, p, w, k), 15 <= k,
    ensures win_ok(b, p, w),
{
    assert forall|j: int| 0 <= j < 15 && p + j < b.len() implies
        #[trigger] b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64) by {
        assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
    }
}

/// The symbol whose code starts at `p`, from a window of at least 15 bits
/// there: a table lookup for codes of at most `tb` bits, else one bit at a
/// time. The symbol and its code length.
#[inline(always)]
pub fn decode_win(c: &Code, Ghost(lens): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>,
                  p: usize, avail: usize, w: u64, Ghost(k): Ghost<nat>) -> (r: Option<(u16, u64)>)
    requires code_wf(c, lens), p + avail == b.len(), win_k(b, p as int, w, k), 15 <= k <= 64,
    ensures
        match r {
            Some((s, l)) => find_sym(lens, b, p as int, 1) == Some((s as nat, p + l)) && 1 <= l <= 15,
            None => find_sym(lens, b, p as int, 1) is None,
        },
{
    proof { lemma_win_15(b, p as int, w, k); reveal(fast_wf); }
    let ghost tb = c.tb;
    let mask = c.mask;
    let wi = w & mask;
    assert(wi < 1024) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
    let e = c.tbl[wi as usize];
    let l = (e / 1024) as u64;
    if e != 0 && l as usize <= avail {
        proof {
            let wb = wbits(wi, tb as nat);
            vbits::prim_read::lemma_p2_eq_pow2(tb as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(tb as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, tb);
            assert(wi < (1u64 << tb)) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
            assert(entry_ok(c.tbl@[wi as int], lens, wb));
            let s = (e % 1024) as nat;
            lemma_find_sym_adv(lens, wb, 0, 1);
            assert(l <= tb);
            assert forall|j: int| 0 <= j < l implies #[trigger] b[p + j] == wb[0 + j] by {
                let jj = j as u64;
                assert(((wi >> jj) & 1u64) == ((w >> jj) & 1u64)) by (bit_vector)
                    requires wi == w & mask, mask == (1u64 << tb) - 1, jj < tb, tb <= 10;
                assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
            }
            lemma_find_sym_agree(lens, b, p as int, wb, 0, 1, s, l as nat);
        }
        return Some((e % 1024, l));
    }
    decode_bits(&c.h, Ghost(lens), Ghost(b), p, avail, w)
}

/// A non-zero entry of the table at a window's low bits is the symbol whose
/// code starts at `p`, and its code length.
pub proof fn lemma_tbl_sym(c: &Code, lens: Seq<u8>, b: Seq<bool>, p: int, w: u64, k: nat)
    requires code_wf(c, lens), win_k(b, p, w, k), 15 <= k <= 64, 0 <= p, p + 15 <= b.len(),
    ensures
        (w & c.mask) < 1024,
        c.tbl@[(w & c.mask) as int] != 0 ==> ({
            let e = c.tbl@[(w & c.mask) as int];
            &&& 1 <= e / 1024 <= 15
            &&& find_sym(lens, b, p, 1) == Some(((e % 1024) as nat, p + (e / 1024) as int))
        }),
{
    lemma_win_15(b, p, w, k);
    reveal(fast_wf);
    let tb = c.tb;
    let mask = c.mask;
    let wi = w & mask;
    assert(wi < 1024) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
    let e = c.tbl@[wi as int];
    if e != 0 {
        let l = (e / 1024) as u64;
        let wb = wbits(wi, tb as nat);
        vbits::prim_read::lemma_p2_eq_pow2(tb as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(tb as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, tb);
        assert(wi < (1u64 << tb)) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
        assert(entry_ok(c.tbl@[wi as int], lens, wb));
        let s = (e % 1024) as nat;
        lemma_find_sym_adv(lens, wb, 0, 1);
        assert(l <= tb);
        assert forall|j: int| 0 <= j < l implies #[trigger] b[p + j] == wb[0 + j] by {
            let jj = j as u64;
            assert(((wi >> jj) & 1u64) == ((w >> jj) & 1u64)) by (bit_vector)
                requires wi == w & mask, mask == (1u64 << tb) - 1, jj < tb, tb <= 10;
            assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
        }
        lemma_find_sym_agree(lens, b, p, wb, 0, 1, s, l as nat);
    }
}

/// `decode_win` for a window of `k` bits ending at `q`, all inside the
/// stream with 15 to spare: no check of the input's end on the table path.
#[inline(always)]
pub fn decode_fast(c: &Code, Ghost(lens): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>,
                   q: usize, k: u64, nbits: usize, w: u64) -> (r: Option<(u16, u64)>)
    requires
        code_wf(c, lens), win_k(b, q - k, w, k as nat), 15 <= k <= 64, k <= q, q <= b.len(),
        nbits == b.len(),
    ensures
        match r {
            Some((s, l)) => find_sym(lens, b, q - k, 1) == Some((s as nat, q - k + l)) && 1 <= l <= 15,
            None => find_sym(lens, b, q - k, 1) is None,
        },
{
    let ghost p = q - k;
    proof { lemma_win_15(b, p, w, k as nat); reveal(fast_wf); }
    let ghost tb = c.tb;
    let mask = c.mask;
    let wi = w & mask;
    assert(wi < 1024) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
    let e = c.tbl[wi as usize];
    let l = (e / 1024) as u64;
    if e != 0 {
        proof {
            let wb = wbits(wi, tb as nat);
            vbits::prim_read::lemma_p2_eq_pow2(tb as nat);
            vstd::bits::lemma_u64_pow2_no_overflow(tb as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, tb);
            assert(wi < (1u64 << tb)) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
            assert(entry_ok(c.tbl@[wi as int], lens, wb));
            let s = (e % 1024) as nat;
            lemma_find_sym_adv(lens, wb, 0, 1);
            assert(l <= tb);
            assert forall|j: int| 0 <= j < l implies #[trigger] b[p + j] == wb[0 + j] by {
                let jj = j as u64;
                assert(((wi >> jj) & 1u64) == ((w >> jj) & 1u64)) by (bit_vector)
                    requires wi == w & mask, mask == (1u64 << tb) - 1, jj < tb, tb <= 10;
                assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
            }
            lemma_find_sym_agree(lens, b, p, wb, 0, 1, s, l as nat);
        }
        return Some((e % 1024, l));
    }
    let pp = q - k as usize;
    decode_resume(c, Ghost(lens), Ghost(b), pp, nbits - pp, w, wi)
}

/// The search past a window with no table entry, resumed at `tb + 1` bits
/// from the code its `tb` bits make.
#[inline(never)]
pub fn decode_resume(c: &Code, Ghost(lens): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>,
                     p: usize, avail: usize, w: u64, wi: u64) -> (r: Option<(u16, u64)>)
    requires
        code_wf(c, lens), p + avail == b.len(), win_ok(b, p as int, w), c.tb <= avail,
        wi == w & c.mask, wi < 1024, c.tbl@[wi as int] == 0,
    ensures
        match r {
            Some((s, l)) => find_sym(lens, b, p as int, 1) == Some((s as nat, p + l)) && 1 <= l <= 15,
            None => find_sym(lens, b, p as int, 1) is None,
        },
{
    let ghost tb = c.tb;
    let ghost mk = c.mask;
    let ghost wb = wbits(wi, tb as nat);
    proof {
        reveal(res_wf);
        vbits::prim_read::lemma_p2_eq_pow2(tb as nat);
        vstd::bits::lemma_u64_pow2_no_overflow(tb as nat);
        vstd::bits::lemma_u64_shl_is_mul(1u64, tb);
        assert(wi < (1u64 << tb)) by (bit_vector) requires wi == w & mk, mk == (1u64 << tb) - 1, 1 <= tb <= 10;
        assert(find_sym(lens, wb, 0, 1) is None && c.code@[wi as int] as nat == codebits(wb, 0, tb as nat));
        assert forall|j: int| 0 <= j < tb implies #[trigger] b[p + j] == wb[j] by {
            let jj = j as u64;
            assert(((wi >> jj) & 1u64) == ((w >> jj) & 1u64)) by (bit_vector)
                requires wi == w & mk, mk == (1u64 << tb) - 1, jj < tb, tb <= 10;
            assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
        }
        lemma_find_sym_past(lens, wb, b, p as int, 1);
        assert(b.subrange(p as int, p + tb) =~= wb.subrange(0, tb as int)) by {
            assert forall|j: int| 0 <= j < tb implies
                #[trigger] b.subrange(p as int, p + tb)[j] == wb.subrange(0, tb as int)[j] by {
                assert(b[p + j] == wb[j]);
            }
        }
        lemma_offs_end(&c.h, lens, (tb + 1) as int);
    }
    let l0 = c.tb + 1;
    let code0 = c.code[wi as usize] as u64;
    let index0 = c.h.offs[l0 as usize] as u64;
    decode_from(&c.h, Ghost(lens), Ghost(b), p, avail, w, l0, code0, c.first1, index0)
}

/// The symbol whose code starts at `pos`, and the position after it.
#[inline]
pub fn decode(c: &Code, Ghost(lens): Ghost<Seq<u8>>, buf: &[u8], pos: usize) -> (r: Option<(u16, usize)>)
    requires code_wf(c, lens), buf.len() < max_input(), pos <= 8 * buf.len(),
    ensures
        match r {
            Some((s, q)) => decode_sym(lens, lbits(buf@), pos as int) == Some((s as nat, q as int)),
            None => decode_sym(lens, lbits(buf@), pos as int) is None,
        },
{
    let w = peek_lsb(buf, pos, 15);
    proof {
        lemma_peek_win(buf@, pos as int, w);
        assert(win_k(lbits(buf@), pos as int, w, 15));
    }
    match decode_win(c, Ghost(lens), Ghost(lbits(buf@)), pos, 8 * buf.len() - pos, w, Ghost(15)) {
        Some((s, l)) => Some((s, pos + l as usize)),
        None => None,
    }
}

/// A peeked window of `n` bits is a window of the stream.
pub proof fn lemma_peek_win_k(buf: Seq<u8>, pos: int, n: nat, w: u64)
    requires 0 <= pos, n <= 56, w as nat == lval(lview(buf).subrange(pos, pos + n)),
    ensures win_k(lbits(buf), pos, w, n),
{
    assert forall|j: int| 0 <= j < n && pos + j < lbits(buf).len() implies
        #[trigger] lbits(buf)[pos + j] == ((w >> (j as u64)) & 1u64 == 1u64) by {
        lemma_peek_bit(buf, pos, n, w, j as nat);
    }
}

/// A field inside a window is the stream's field there.
pub proof fn lemma_win_getbits(b: Seq<bool>, p: int, w: u64, k: nat, n: nat)
    requires win_k(b, p, w, k), n <= k, k <= 64, n <= 32, 0 <= p, p + n <= b.len(),
    ensures getbits(b, p, n) == Some((w as nat) % p2(n)),
    decreases n,
{
    if n == 0 {
        assert(b.subrange(p, p) =~= Seq::<bool>::empty());
        assert(p2(0) == 1);
        assert(lval(b.subrange(p, p)) == 0);
        assert((w as nat) % 1 == 0);
    } else {
        lemma_win_shift(b, p, w, k, 1);
        lemma_win_getbits(b, p + 1, w >> 1, (k - 1) as nat, (n - 1) as nat);
        let t = b.subrange(p, p + n);
        assert(t.subrange(1, t.len() as int) =~= b.subrange(p + 1, p + 1 + (n - 1)));
        assert(t[0] == b[p]);
        assert(b[p + 0] == ((w >> 0u64) & 1u64 == 1u64));
        vstd::bits::lemma_u64_shr_is_div(w, 1);
        assert(p2(1) == 2) by { reveal_with_fuel(p2, 2); }
        assert(((w >> 0u64) & 1u64 == 1u64) == (w % 2 == 1)) by (bit_vector);
        let lo = (w as nat) % 2;
        let hi = ((w as nat) / 2) % p2((n - 1) as nat);
        vbits::bitspec::lemma_p2_pos((n - 1) as nat);
        assert(p2(n) == 2 * p2((n - 1) as nat));
        vstd::arithmetic::div_mod::lemma_mod_breakdown(w as int, 2, p2((n - 1) as nat) as int);
        assert((w as nat) % p2(n) == 2 * hi + lo);
        assert(w >> 1u64 == w / 2) by (bit_vector);
        assert(((w >> 1) as nat) == (w as nat) / 2);
        assert(lval(b.subrange(p + 1, p + 1 + (n - 1))) == hi);
        assert(lval(t) == (if t[0] { 1nat } else { 0nat }) + 2 * lval(t.subrange(1, t.len() as int)));
        assert((if t[0] { 1nat } else { 0nat }) == lo);
        assert(lval(t) == 2 * hi + lo);
    }
}

} // verus!
