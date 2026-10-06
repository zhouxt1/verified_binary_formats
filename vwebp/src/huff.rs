//! Canonical prefix codes over alphabets of up to 4096 symbols: vdeflate's
//! `Huff` (the symbols in (length, symbol) order, as puff.c) and its
//! bit-at-a-time decoder, proved equal to the spec's `decode_sym`, with the
//! bound on the alphabet raised from vdeflate's 1024 (VP8L's green
//! alphabet has up to 256 + 24 + 2048 = 2328 symbols). The lemmas about
//! the spec alone are vdeflate's.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::{bits_val, p2};
use vbits::lsb::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::huff::{lemma_count_mono, lemma_count_le, lemma_rank_lt, lemma_rank_exists, lemma_find_n,
                     lemma_find_n_range, lemma_count_step, matches, tot, win_ok, wbits, win_k,
                     lemma_find_sym_agree, lemma_find_sym_skip, lemma_find_sym_sym, lemma_win_15,
                     lemma_find_sym_past};
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
pub use vdeflate::huff::max_input;

verus! {

// --------------------------------------------------------- the table

/// A decoding table for `lens`: codes of each length, and the symbols in
/// (length, symbol) order, `offs[l]` the first of length `l`.
pub struct Huff {
    pub count: [u16; 16],
    pub offs: [u16; 16],
    pub syms: Vec<u16>,
}

pub open spec fn huff_wf(h: &Huff, lens: Seq<u8>) -> bool {
    &&& lens.len() <= 4096
    &&& lens_ok(lens)
    &&& forall|l: int| 1 <= l <= 15 ==> #[trigger] h.count[l] as nat == bl_count(lens, l as nat)
    &&& h.offs[1] == 0
    &&& forall|l: int| 1 <= l < 15 ==> #[trigger] h.offs[l + 1] as nat == h.offs[l] + h.count[l]
    &&& h.offs[15] + h.count[15] == h.syms@.len()
    &&& h.syms@.len() <= 4096
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
    requires lens.len() <= 4096, lens_ok(lens@),
    ensures huff_wf(&h, lens@),
{
    let ghost gl = lens@;
    let n = lens.len();
    let mut count = [0u16; 16];
    let mut i: usize = 0;
    while i < n
        invariant
            n == lens.len(), gl == lens@, i <= n, n <= 4096, lens_ok(gl),
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
            1 <= l <= 15, n <= 4096, n == gl.len(), lens_ok(gl),
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
            n == lens.len(), gl == lens@, i <= n, n <= 4096, lens_ok(gl),
            forall|l: int| 0 <= l < 16 ==> #[trigger] count[l] as nat == count_len(gl, l as nat, n as int),
            forall|j: int| 1 <= j <= 15 ==> #[trigger] offs[j] as nat == tot(gl, (j - 1) as nat, n as int),
            total == tot(gl, 15, n as int), syms@.len() == total, total <= 4096,
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
        first0 as nat == next_code(lens, l0 as nat), first0 as nat <= 8192 * (p2((l0 - 1) as nat) - 1),
        l0 <= 15 ==> index0 as nat == h.offs[l0 as int], index0 <= 4096,
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
            first as nat <= 8192 * (p2((l - 1) as nat) - 1),
            l <= 15 ==> index as nat == h.offs[l as int],
            index <= 4096,
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

/// A table entry for a window: 0, or the length of the code the window
/// starts with times 4096 plus its symbol (vdeflate's entries, with 12 bits
/// for the symbol: 15 * 4096 + 4095 still fits). A 0 says nothing: the
/// decoder then reads the code one bit at a time.
pub open spec fn entry_ok(e: u16, lens: Seq<u8>, wb: Seq<bool>) -> bool {
    e != 0 ==> ({
        let s = (e % 4096) as nat;
        let l = (e / 4096) as nat;
        1 <= l <= 15 && find_sym(lens, wb, 0, 1) == Some((s, l as int))
    })
}

/// A table entry for a `k`-bit window: 4096 or more, the length of the
/// code the window starts with times 4096 plus its symbol; below 4096, the
/// window has no code, and the entry is the value of its bits read as a
/// code (to go on from there one bit at a time).
pub open spec fn mlvl_ok(m: u16, lens: Seq<u8>, w: u64, k: nat) -> bool {
    &&& m >= 4096 ==> entry_ok(m, lens, wbits(w, k)) && m / 4096 <= k
    &&& m < 4096 ==> find_sym(lens, wbits(w, k), 0, 1) is None && m as nat == codebits(wbits(w, k), 0, k)
}

/// The table has an entry for every `tb`-bit window (opaque: revealed where
/// the table is built and read).
#[verifier::opaque]
pub open spec fn fast_wf(tbl: Seq<u16>, lens: Seq<u8>, tb: nat) -> bool {
    &&& tbl.len() == p2(tb)
    &&& forall|w: int| 0 <= w < p2(tb) ==> mlvl_ok(#[trigger] tbl[w], lens, w as u64, tb)
}

/// How many bits a table decodes: at most 10.
pub open spec fn tb_ok(tb: u64) -> bool { 1 <= tb <= 10 }

/// Windows that agree on their low `m` bits agree on an entry whose code is
/// at most `m` bits long.
proof fn lemma_entry_move(e: u16, lens: Seq<u8>, w1: u64, n1: nat, w2: u64, n2: nat, m: nat)
    requires
        entry_ok(e, lens, wbits(w1, n1)), e != 0 ==> e / 4096 <= m,
        m <= n1, m <= n2, n1 <= 64, n2 <= 64,
        forall|j: u64| j < m ==> #[trigger] ((w1 >> j) & 1u64) == ((w2 >> j) & 1u64),
    ensures entry_ok(e, lens, wbits(w2, n2)),
{
    if e != 0 {
        let s = (e % 4096) as nat;
        let l = (e / 4096) as nat;
        let b1 = wbits(w1, n1);
        let b2 = wbits(w2, n2);
        assert forall|j: int| 0 <= j < l implies #[trigger] b2[0 + j] == b1[0 + j] by {
            assert(((w1 >> (j as u64)) & 1u64) == ((w2 >> (j as u64)) & 1u64));
        }
        lemma_find_sym_agree(lens, b2, 0, b1, 0, 1, s, l);
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
    &&& e != 0 ==> e / 4096 <= k
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
            ((k + 1) * 4096 + h.syms@[index + (2 * (c as int) + bit - first)]) as u16
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

/// `lvl_ok`'s entry and code, merged into one entry.
proof fn lemma_lvl_m(e: u16, c: u16, lens: Seq<u8>, w: u64, k: nat)
    requires lvl_ok(e, c, lens, w, k), k <= 10, e != 0 ==> e >= 4096,
    ensures mlvl_ok(if e != 0 { e } else { c }, lens, w, k),
{
    if e == 0 {
        vbits::bitspec::lemma_bits_val_bound(wbits(w, k).subrange(0, k as int));
        vbits::prim_read::lemma_p2_mono(k, 10);
        reveal_with_fuel(p2, 11);
    }
}

/// The table for `tb`-bit windows, one window length at a time (vdeflate's
/// `build_table_c`, into one vector of `2^tb` entries whose misses hold the
/// code so far): a window of `k + 1` bits has the entry of its first `k` if
/// that has a code, and otherwise a code of exactly `k + 1` bits or none,
/// decided by the value of its bits (as `decode_bits` decides it at that
/// length). Also the first code of `tb + 1` bits.
pub fn build_table(h: &Huff, Ghost(lens): Ghost<Seq<u8>>, tb: u64) -> (r: (Vec<u16>, u64))
    requires huff_wf(h, lens), tb_ok(tb),
    ensures fast_wf(r.0@, lens, tb as nat),
        r.1 as nat == next_code(lens, (tb + 1) as nat), r.1 as nat <= 8192 * (p2(tb as nat) - 1),
{
    let size: usize = (1u64 << tb) as usize;
    proof {
        crate::code::lemma_shl1(tb);
        vbits::prim_read::lemma_p2_mono(tb as nat, 10);
        reveal_with_fuel(p2, 11);
    }
    let mut tbl: Vec<u16> = vec![0u16; size];
    let mut first: u64 = 0;   // next_code(k + 1)
    let mut k: u64 = 0;
    proof {
        lemma_p2_15();
        let wb = wbits(0, 0);
        assert(find_sym(lens, wb, 0, 1) is None);
        assert(wb.subrange(0, 0) =~= Seq::<bool>::empty());
        assert(codebits(wb, 0, 0) == 0);
        assert(mlvl_ok(tbl@[0], lens, 0, 0));
    }
    while k < tb
        invariant
            huff_wf(h, lens), k <= tb, tb_ok(tb), tbl@.len() == size,
            size as nat == p2(tb as nat), size <= 1024,
            p2(14) == 16384, p2(15) == 32768, p2(10) == 1024,
            first as nat == next_code(lens, (k + 1) as nat),
            first as nat <= 8192 * (p2(k as nat) - 1), p2(k as nat) <= p2(tb as nat), 1 <= p2(k as nat),
            forall|w: int| 0 <= w < p2(k as nat) ==> mlvl_ok(#[trigger] tbl@[w], lens, w as u64, k as nat),
        decreases tb - k,
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
            vbits::prim_read::lemma_p2_mono(l as nat, tb as nat);
            reveal_with_fuel(p2, 11);
            assert(half as nat == p2(k as nat));
            assert(p2(l as nat) == 2 * p2(k as nat));
            lemma_count_le(lens, l as nat, lens.len() as int);
            lemma_offs_end(h, lens, l as int);
        }
        let mut base: u64 = 0;
        while base < half
            invariant
                huff_wf(h, lens), k < 10, l == k + 1, tbl@.len() == size,
                half as nat == p2(k as nat), half <= 512, half == (1u64 << k), p2(15) == 32768,
                p2(l as nat) == 2 * p2(k as nat), 2 * half <= size,
                first as nat == next_code(lens, l as nat), first as nat <= 8192 * 512,
                count as nat == bl_count(lens, l as nat), count <= 4096,
                index == h.offs[l as int], index + count <= h.syms@.len(),
                base <= half,
                forall|w: int| base <= w < half ==> mlvl_ok(#[trigger] tbl@[w], lens, w as u64, k as nat),
                forall|w: int| (0 <= w < base || half <= w < half + base) ==>
                    mlvl_ok(#[trigger] tbl@[w], lens, w as u64, l as nat),
            decreases half - base,
        {
            let w1 = base + half;
            let m = tbl[base as usize];
            proof {
                assert(mlvl_ok(tbl@[base as int], lens, base, k as nat));
                assert(base < half && w1 < 2 * half);
                assert forall|j: u64| j < k implies #[trigger] ((w1 >> j) & 1u64) == ((base >> j) & 1u64) by {
                    assert(((w1 >> j) & 1u64) == ((base >> j) & 1u64)) by (bit_vector)
                        requires w1 == base + half, half == (1u64 << k), base < half, j < k, k < 10;
                }
                assert((w1 >> k) & 1u64 == 1u64 && (base >> k) & 1u64 == 0u64) by (bit_vector)
                    requires w1 == base + half, half == (1u64 << k), base < half, k < 10;
            }
            if m >= 4096 {
                proof {
                    assert forall|j: u64| j < (m / 4096) as nat implies
                        #[trigger] ((base >> j) & 1u64) == ((base >> j) & 1u64) by {}
                    lemma_entry_move(m, lens, base, k as nat, base, l as nat, (m / 4096) as nat);
                    assert forall|j: u64| j < (m / 4096) as nat implies
                        #[trigger] ((base >> j) & 1u64) == ((w1 >> j) & 1u64) by {}
                    lemma_entry_move(m, lens, base, k as nat, w1, l as nat, (m / 4096) as nat);
                }
                tbl.set(w1 as usize, m);
            } else {
                // no code of at most k bits: one of exactly k + 1, or none
                let c = m;
                proof {
                    assert(lvl_ok(0, c, lens, base, k as nat));
                    lemma_find_sym_none(lens, wbits(base, k as nat), 1, k as nat);
                    vbits::bitspec::lemma_bits_val_bound(wbits(base, k as nat).subrange(0, k as int));
                    vbits::prim_read::lemma_p2_mono(k as nat, 9);
                }
                let c0: u64 = 2 * (c as u64);
                let c1: u64 = 2 * (c as u64) + 1;
                let e1 = if c1 >= first && c1 < first + count {
                    let k1 = (index + (c1 - first)) as usize;
                    (l * 4096 + h.syms[k1] as u64) as u16
                } else { 0u16 };
                let e0 = if c0 >= first && c0 < first + count {
                    let k0 = (index + (c0 - first)) as usize;
                    (l * 4096 + h.syms[k0] as u64) as u16
                } else { 0u16 };
                proof {
                    lemma_level_miss(h, lens, base, base, k, c, 0, first, count, index, e0);
                    lemma_level_miss(h, lens, base, w1, k, c, 1, first, count, index, e1);
                    lemma_lvl_m(e0, c0 as u16, lens, base, l as nat);
                    lemma_lvl_m(e1, c1 as u16, lens, w1, l as nat);
                }
                tbl.set(w1 as usize, if e1 != 0 { e1 } else { c1 as u16 });
                tbl.set(base as usize, if e0 != 0 { e0 } else { c0 as u16 });
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
    proof {
        reveal(fast_wf);
    }
    (tbl, first)
}

/// The longest code length of a table, at least 1.
pub fn max_len(h: &Huff) -> (r: u64)
    ensures 1 <= r <= 15,
{
    let mut l: usize = 15;
    while l > 1 && h.count[l] == 0
        invariant 1 <= l <= 15,
        decreases l,
    {
        l = l - 1;
    }
    l as u64
}

/// The symbol whose code starts at `p`, from a window of at least 15 bits
/// there: a table lookup for codes of at most `tb` bits (if the code fits in
/// the bits there are, as the spec has it), else `decode_miss`. The symbol
/// and its code length.
#[inline(always)]
pub fn decode_win(h: &Huff, tbl: &Vec<u16>, mask: u64, first: u64, idx: u64, tb: u64,
                  Ghost(lens): Ghost<Seq<u8>>, Ghost(b): Ghost<Seq<bool>>, p: usize, avail: usize, w: u64,
                  Ghost(k): Ghost<nat>)
    -> (r: Option<(u16, u64)>)
    requires
        huff_wf(h, lens), tb_ok(tb), mask == (1u64 << tb) - 1, fast_wf(tbl@, lens, tb as nat),
        first as nat == next_code(lens, (tb + 1) as nat), first as nat <= 8192 * (p2(tb as nat) - 1),
        idx == h.offs[(tb + 1) as int],
        p + avail == b.len(), win_k(b, p as int, w, k), 15 <= k <= 64,
    ensures
        match r {
            Some((s, l)) => find_sym(lens, b, p as int, 1) == Some((s as nat, p + l)) && 1 <= l <= 15,
            None => find_sym(lens, b, p as int, 1) is None,
        },
{
    proof {
        reveal(fast_wf);
        crate::code::lemma_shl1(tb);
    }
    let wi = w & mask;
    assert(wi < (1u64 << tb)) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
    let e = vsimd::mem::get(tbl.as_slice(), wi as usize);
    let l = (e >> 12u16) as u64;
    if e >= 4096 && l as usize <= avail {
        let ghost wb = wbits(wi, tb as nat);
        proof {
            assert(e >> 12u16 == e / 4096) by (bit_vector);
            assert(mlvl_ok(tbl@[wi as int], lens, wi, tb as nat));
            let s = (e % 4096) as nat;
            lemma_find_sym_adv(lens, wb, 0, 1);
            assert(l <= tb);
            assert forall|j: int| 0 <= j < l implies #[trigger] b[p + j] == wb[0 + j] by {
                let jj = j as u64;
                assert(((wi >> jj) & 1u64) == ((w >> jj) & 1u64)) by (bit_vector)
                    requires wi == w & mask, mask == (1u64 << tb) - 1, jj < tb, tb <= 10;
                assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
            }
            lemma_find_sym_agree(lens, b, p as int, wb, 0, 1, s, l as nat);
            assert(e & 0xfffu16 == e % 4096) by (bit_vector);
        }
        return Some((e & 0xfff, l));
    }
    decode_miss(h, e, wi, mask, first, idx, tb, Ghost(lens), Ghost(tbl@), Ghost(b), p, avail, w, Ghost(k))
}

/// A table's size, and where a window's entry is.
pub proof fn lemma_fast_len(tbl: Seq<u16>, lens: Seq<u8>, tb: u64, mask: u64, w: u64)
    requires fast_wf(tbl, lens, tb as nat), tb_ok(tb), mask == (1u64 << tb) - 1,
    ensures (w & mask) < tbl.len(),
{
    reveal(fast_wf);
    crate::code::lemma_shl1(tb);
    let wi = w & mask;
    assert(wi < (1u64 << tb)) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
}

/// A table entry of 4096 or more whose code fits in the bits left is the
/// code at `p`.
pub proof fn lemma_hit(tbl: Seq<u16>, lens: Seq<u8>, tb: u64, mask: u64, b: Seq<bool>, p: int, avail: int,
                       w: u64, k: nat, e: u16)
    requires
        fast_wf(tbl, lens, tb as nat), tb_ok(tb), mask == (1u64 << tb) - 1,
        0 <= p, p + avail == b.len(), win_k(b, p, w, k), 15 <= k <= 64,
        (w & mask) < tbl.len(), e == tbl[(w & mask) as int], e >= 4096, (e >> 12u16) as int <= avail,
    ensures
        find_sym(lens, b, p, 1) == Some(((e & 0xfffu16) as nat, p + (e >> 12u16) as int)),
        1 <= (e >> 12u16) <= 15,
{
    reveal(fast_wf);
    crate::code::lemma_shl1(tb);
    let wi = w & mask;
    let l = (e >> 12u16) as u64;
    assert(wi < (1u64 << tb)) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
    let wb = wbits(wi, tb as nat);
    assert(e >> 12u16 == e / 4096) by (bit_vector);
    assert(mlvl_ok(tbl[wi as int], lens, wi, tb as nat));
    let s = (e % 4096) as nat;
    lemma_find_sym_adv(lens, wb, 0, 1);
    assert(l <= tb);
    assert forall|j: int| 0 <= j < l implies #[trigger] b[p + j] == wb[0 + j] by {
        let jj = j as u64;
        assert(((wi >> jj) & 1u64) == ((w >> jj) & 1u64)) by (bit_vector)
            requires wi == w & mask, mask == (1u64 << tb) - 1, jj < tb, tb <= 10;
        assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
    }
    lemma_find_sym_agree(lens, b, p, wb, 0, 1, s, l as nat);
    assert(e & 0xfffu16 == e % 4096) by (bit_vector);
}

/// A table entry `e` that is not a code within the bits left: for a window
/// with no code of at most `tb` bits, one bit at a time from length `tb + 1`
/// on, with the code so far from the table; else from the start.
#[inline(always)]
pub fn decode_miss(h: &Huff, e: u16, wi: u64, mask: u64, first: u64, idx: u64, tb: u64,
               Ghost(lens): Ghost<Seq<u8>>, Ghost(tbl): Ghost<Seq<u16>>, Ghost(b): Ghost<Seq<bool>>,
               p: usize, avail: usize, w: u64, Ghost(k): Ghost<nat>)
    -> (r: Option<(u16, u64)>)
    requires
        huff_wf(h, lens), tb_ok(tb), mask == (1u64 << tb) - 1, fast_wf(tbl, lens, tb as nat),
        first as nat == next_code(lens, (tb + 1) as nat), first as nat <= 8192 * (p2(tb as nat) - 1),
        idx == h.offs[(tb + 1) as int], wi == w & mask, wi < tbl.len(), e == tbl[wi as int],
        p + avail == b.len(), win_k(b, p as int, w, k), 15 <= k <= 64,
    ensures
        match r {
            Some((s, l)) => find_sym(lens, b, p as int, 1) == Some((s as nat, p + l)) && 1 <= l <= 15,
            None => find_sym(lens, b, p as int, 1) is None,
        },
{
    proof {
        lemma_win_15(b, p as int, w, k);
        reveal(fast_wf);
        crate::code::lemma_shl1(tb);
    }
    if e < 4096 && tb as usize <= avail {
        // no code of at most tb bits: go on from tb + 1 with the code so far
        let ghost wb = wbits(wi, tb as nat);
        proof {
            assert(wi < (1u64 << tb)) by (bit_vector) requires wi == w & mask, mask == (1u64 << tb) - 1, 1 <= tb <= 10;
            assert(mlvl_ok(tbl[wi as int], lens, wi, tb as nat));
            assert forall|j: int| 0 <= j < tb && p + j < b.len() implies #[trigger] b[p + j] == wb[j] by {
                let jj = j as u64;
                assert(((wi >> jj) & 1u64) == ((w >> jj) & 1u64)) by (bit_vector)
                    requires wi == w & mask, mask == (1u64 << tb) - 1, jj < tb, tb <= 10;
                assert(b[p + j] == ((w >> (j as u64)) & 1u64 == 1u64));
            }
            lemma_find_sym_past(lens, wb, b, p as int, 1);
            assert(b.subrange(p as int, p + tb) =~= wb.subrange(0, tb as int)) by {
                assert forall|j: int| 0 <= j < tb implies
                    #[trigger] b.subrange(p as int, p + tb)[j] == wb.subrange(0, tb as int)[j] by {
                    assert(b[p + j] == wb[j]);
                }
            }
            assert(codebits(b, p as int, tb as nat) == e as nat);
            lemma_offs_end(h, lens, (tb + 1) as int);
            assert(h.syms@.len() <= 4096);
        }
        return decode_from(h, Ghost(lens), Ghost(b), p, avail, w, tb + 1, e as u64, first, idx);
    }
    decode_bits(h, Ghost(lens), Ghost(b), p, avail, w)
}

} // verus!
