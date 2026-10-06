//! Decoding a DEFLATE stream that arrives in pieces.
//!
//! `Inflater::feed` takes the next piece of input and decodes as far as the
//! input so far allows. What it has decoded, and its verdict, hold for every
//! stream that starts with the input so far (`inv`, and `feed`'s ensures):
//!
//! * `Done`: every such stream decodes to the output so far, with the bits
//!   and the zlib flag given. In particular the input so far does;
//! * `NeedMore`: the input so far is not a whole stream (the spec has no
//!   result for it), and the output so far starts the output of every
//!   stream that does start with it;
//! * `Bad`: no stream that starts with the input so far decodes;
//! * `TooBig`: every one that does has output longer than the limit.
//!
//! So however a stream is cut into pieces, feeding them in turn ends in
//! `Done` exactly when the spec decodes the whole of it, with its result.
//!
//! The output goes to the caller's sink as it is decoded. Between pieces the
//! decoder keeps only the input it has not finished with (less than a
//! dynamic header, 7100 bits, when it waits for more) and the last 32768
//! bytes of output, which is as far back as a distance reaches
//! (`lemma_syms_win`, `lemma_blocks_win`). Inside, positions are relative
//! to the input kept; `tgt` is the spec on the whole stream, with the input
//! dropped (`dropped`) put back, and `pre` is the output dropped.
use vstd::prelude::*;
use vbits::lsb::*;
use crate::spec::*;
use crate::huff::*;
use crate::step::*;
use crate::inflate::*;
use crate::shift::*;

verus! {

/// `src` appended to `v` (one copy).
#[inline(always)]
pub fn append(v: &mut Vec<u8>, src: &[u8])
    ensures final(v)@ == old(v)@ + src@,
{
    let ghost v0 = v@;
    v.extend_from_slice(src);
    proof {
        assert forall|i: int| 0 <= i < v@.len() implies #[trigger] v@[i] == (v0 + src@)[i] by {
            if i >= v0.len() {
                assert(cloned::<u8>(src@[i - v0.len()], v@[i]));
            }
        }
        assert(v@ =~= v0 + src@);
    }
}


pub enum Mode {
    /// At a block's header.
    Header,
    /// In a stored block of `len` bytes starting at bit `q0`, `done` of them
    /// copied.
    Stored { len: usize, done: usize, q0: Ghost<int>, last: bool },
    /// In a block with the fixed codes.
    Fixed { last: bool },
    /// In a block with its own codes; `bst` is whether zlib accepts them.
    Dynamic { lit: Code, dist: Code, last: bool, bst: bool },
    /// After the final block, which ended at bit `q`.
    Done { q: usize },
}

impl Mode {
    pub fn is_done(&self) -> (r: bool)
        ensures r == (*self is Done),
    {
        match self { Mode::Done { .. } => true, _ => false }
    }
}

pub struct Inflater {
    /// The input not yet finished with.
    pub inp: Vec<u8>,
    /// The last output: `out@.take(n)`, at least 32768 bytes or all of it.
    pub out: Vec<u8>,
    pub n: usize,
    /// The next step's position, in bits from the start of `inp`.
    pub p: usize,
    /// The current block's header position.
    pub blk: Ghost<int>,
    pub st: bool,
    pub mode: Mode,
    pub fixed: Option<(Code, Code)>,
    /// How long `out@.take(n)` may grow: the limit, less the output dropped.
    pub max_out: usize,
    pub ll: Ghost<Seq<u8>>,
    pub dl: Ghost<Seq<u8>>,
    /// The input dropped, `base` bytes of it, and the output dropped.
    pub base: usize,
    pub dropped: Ghost<Seq<u8>>,
    pub pre: Ghost<Seq<u8>>,
    /// The output limit.
    pub limit: usize,
}

#[derive(PartialEq, Eq)]
pub enum Status {
    NeedMore,
    /// The stream took `bits`.
    Done { bits: usize, zlib: bool },
}

/// Positions moved by `k`.
pub open spec fn pshift(r: Option<(Seq<u8>, int, bool)>, k: int) -> Option<(Seq<u8>, int, bool)> {
    match r { None => None, Some((o, q, s)) => Some((o, q + k, s)) }
}

/// The spec on the whole stream, `dropped` then `f`, with positions from the
/// start of `f`.
pub open spec fn target(dropped: Seq<u8>, f: Seq<bool>) -> Option<(Seq<u8>, int, bool)> {
    pshift(inflate_blocks(lbits(dropped) + f, 0, Seq::empty(), true), -8 * dropped.len())
}

/// What follows a block that ended at `q` with output `o`.
pub open spec fn after_block(f: Seq<bool>, blk: int, o: Seq<u8>, q: int, last: bool, s: bool)
    -> Option<(Seq<u8>, int, bool)> {
    if last { Some((o, q, s)) } else if q <= blk || q > f.len() { None } else { inflate_blocks(f, q, o, s) }
}

pub proof fn lemma_after_grow(f: Seq<bool>, blk: int, o: Seq<u8>, q: int, last: bool, s: bool)
    ensures after_block(f, blk, o, q, last, s) matches Some((o2, _, _)) ==> o2.len() >= o.len(),
{
    if !last && !(q <= blk || q > f.len()) { lemma_blocks_grow(f, q, o, s); }
}

impl Inflater {
    pub open spec fn g(&self) -> Seq<u8> { self.out@.take(self.n as int) }

    pub open spec fn bits(&self) -> Seq<bool> { lbits(self.inp@) }

    /// The spec's result for a stream `f` that starts with the input, as the
    /// state finishes it.
    #[verifier::opaque]
    pub open spec fn cont(&self, f: Seq<bool>) -> Option<(Seq<u8>, int, bool)> {
        let g = self.g();
        let p = self.p as int;
        let blk = self.blk@;
        match self.mode {
            Mode::Header => inflate_blocks(f, p, g, self.st),
            Mode::Fixed { last } => match inflate_syms(fixed_lit(), fixed_dist(), f, p, g) {
                None => None,
                Some((o, q)) => after_block(f, blk, o, q, last, self.st),
            },
            Mode::Dynamic { last, bst, .. } => match inflate_syms(self.ll@, self.dl@, f, p, g) {
                None => None,
                Some((o, q)) => after_block(f, blk, o, q, last, self.st && bst),
            },
            Mode::Stored { len, done, q0, last } => {
                let q = q0@ + 8 * len;
                if q > f.len() {
                    None
                } else {
                    after_block(f, blk, g + bytes_at(f, q0@ + 8 * done, (len - done) as nat), q, last, self.st)
                }
            }
            Mode::Done { q } => Some((g, q as int, self.st)),
        }
    }

    pub open spec fn tgt(&self, f: Seq<bool>) -> Option<(Seq<u8>, int, bool)> {
        target(self.dropped@, f)
    }

    /// All the input so far, and all the output.
    pub open spec fn fed(&self) -> Seq<u8> { self.dropped@ + self.inp@ }

    pub open spec fn whole(&self) -> Seq<u8> { self.pre@ + self.g() }

    /// The decoding tables are right (kept opaque: their facts are large).
    #[verifier::opaque]
    pub open spec fn codes_ok(&self) -> bool {
        &&& fixed_ok(self.fixed)
        &&& match self.mode {
            Mode::Fixed { .. } => self.fixed is Some,
            Mode::Dynamic { lit, dist, .. } => code_wf(&lit, self.ll@) && code_wf(&dist, self.dl@),
            _ => true,
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.base + self.inp@.len() < max_input() && self.dropped@.len() == self.base
        &&& self.p <= 8 * self.inp@.len()
        &&& self.n <= self.max_out && self.n <= self.out@.len() && self.max_out <= max_len()
        &&& self.max_out + self.pre@.len() == self.limit && self.limit <= max_len()
        &&& (self.n >= 32768 || self.pre@.len() == 0)
        &&& self.codes_ok()
        &&& match self.mode {
            Mode::Header => true,
            Mode::Fixed { .. } => self.blk@ < self.p,
            Mode::Dynamic { .. } => self.blk@ < self.p,
            Mode::Stored { len, done, q0, .. } => done <= len && self.p == q0@ + 8 * done && self.blk@ < q0@
                && q0@ % 8 == 0 && len < 65536,
            Mode::Done { q } => q <= 8 * self.inp@.len(),
        }
        &&& forall|f: Seq<bool>| #[trigger] is_prefix(self.bits(), f) ==>
                self.tgt(f) == lift(self.pre@, self.cont(f))
    }

    pub fn new(limit: usize) -> (d: Inflater)
        requires limit <= max_len(),
        ensures d.inv(), d.fed() == Seq::<u8>::empty(), d.whole() == Seq::<u8>::empty(), d.limit == limit,
    {
        let d = Inflater {
            inp: Vec::new(), out: Vec::new(), n: 0, p: 0, blk: Ghost(0), st: true, mode: Mode::Header,
            fixed: None, max_out: limit, ll: Ghost(Seq::empty()), dl: Ghost(Seq::empty()),
            base: 0, dropped: Ghost(Seq::empty()), pre: Ghost(Seq::empty()), limit,
        };
        proof {
            assert(d.g() =~= Seq::<u8>::empty());
            assert(d.fed() =~= Seq::<u8>::empty());
            assert(d.whole() =~= Seq::<u8>::empty());
            reveal(Inflater::codes_ok);
            assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                d.tgt(f) == lift(d.pre@, d.cont(f)) by {
                cont_header(&d, f);
                assert(lbits(Seq::<u8>::empty()) =~= Seq::<bool>::empty());
                assert(lbits(d.dropped@) + f =~= f);
                match d.cont(f) { None => {}, Some((o, q, st)) => { assert(Seq::<u8>::empty() + o =~= o); } }
            }
        }
        d
    }
}

/// How much input the decoder has taken.
pub proof fn lemma_inv_len(d: &Inflater)
    requires d.inv(),
    ensures d.base + d.inp@.len() == d.fed().len(), d.fed().len() < max_input(),
{
}

pub open spec fn cur_last(d: &Inflater) -> bool {
    match d.mode {
        Mode::Fixed { last } => last,
        Mode::Dynamic { last, .. } => last,
        Mode::Stored { last, .. } => last,
        _ => true,
    }
}

pub open spec fn cur_bst(d: &Inflater) -> bool {
    match d.mode { Mode::Dynamic { bst, .. } => bst, _ => true }
}

/// The codes of the block being decoded.
pub open spec fn cur_ll(d: &Inflater) -> Seq<u8> {
    match d.mode { Mode::Fixed { .. } => fixed_lit(), _ => d.ll@ }
}

pub open spec fn cur_dl(d: &Inflater) -> Seq<u8> {
    match d.mode { Mode::Fixed { .. } => fixed_dist(), _ => d.dl@ }
}

proof fn cont_header(d: &Inflater, f: Seq<bool>)
    requires d.mode is Header,
    ensures d.cont(f) == inflate_blocks(f, d.p as int, d.g(), d.st),
{
    reveal(Inflater::cont);
}

proof fn cont_syms(d: &Inflater, f: Seq<bool>)
    requires d.mode is Fixed || d.mode is Dynamic,
    ensures d.cont(f) == match inflate_syms(cur_ll(d), cur_dl(d), f, d.p as int, d.g()) {
        None => None,
        Some((o, q)) => after_block(f, d.blk@, o, q, cur_last(d), d.st && cur_bst(d)),
    },
{
    reveal(Inflater::cont);
    assert((d.st && true) == d.st);
}

proof fn cont_stored(d: &Inflater, f: Seq<bool>)
    requires d.mode is Stored,
    ensures d.cont(f) == ({
        let (len, done, q0) = match d.mode { Mode::Stored { len, done, q0, .. } => (len, done, q0@), _ => (0, 0, 0) };
        let q = q0 + 8 * len;
        if q > f.len() { None } else {
            after_block(f, d.blk@, d.g() + bytes_at(f, q0 + 8 * done, (len - done) as nat), q, cur_last(d), d.st)
        }
    }),
{
    reveal(Inflater::cont);
}

proof fn cont_done(d: &Inflater, f: Seq<bool>)
    requires d.mode is Done,
    ensures d.cont(f) == Some((d.g(), (match d.mode { Mode::Done { q } => q, _ => 0 }) as int, d.st)),
{
    reveal(Inflater::cont);
}

/// The continuation depends only on the output so far and the state, not
/// on the input.
proof fn cont_same(d1: &Inflater, d2: &Inflater, f: Seq<bool>)
    requires d1.g() == d2.g(), d1.p == d2.p, d1.blk == d2.blk, d1.st == d2.st, d1.mode == d2.mode,
        d1.ll == d2.ll, d1.dl == d2.dl,
    ensures d1.cont(f) == d2.cont(f),
{
    reveal(Inflater::cont);
}

proof fn codes_same(d1: &Inflater, d2: &Inflater)
    requires d1.codes_ok(), d1.fixed == d2.fixed, d1.mode == d2.mode, d1.ll == d2.ll, d1.dl == d2.dl,
    ensures d2.codes_ok(),
{
    reveal(Inflater::codes_ok);
}

/// Leaving a block keeps only the fixed codes.
proof fn codes_to(d1: &Inflater, d2: &Inflater)
    requires d1.codes_ok(), d1.fixed == d2.fixed, d2.mode is Header || d2.mode is Done || d2.mode is Stored,
    ensures d2.codes_ok(),
{
    reveal(Inflater::codes_ok);
}

pub proof fn lemma_lbits_prefix(a: Seq<u8>, c: Seq<u8>)
    ensures is_prefix(lbits(a), lbits(a + c)),
{
    lemma_lbits_add(a, c);
}

pub proof fn lemma_prefix_trans(a: Seq<bool>, b: Seq<bool>, c: Seq<bool>)
    requires is_prefix(a, b), is_prefix(b, c),
    ensures is_prefix(a, c),
{
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i] == c[i] by {
        assert(a[i] == b[i]);
        assert(b[i] == c[i]);
    }
}

/// A stored block's header, as the spec's `stored_hdr`.
fn stored_hdr_x(buf: &[u8], pos: usize) -> (r: Option<(usize, usize)>)
    requires buf.len() < max_input(), pos <= 8 * buf.len(),
    ensures
        match r {
            Some((len, q0)) => stored_hdr(lbits(buf@), pos as int) == Some((len as nat, q0 as int))
                && q0 <= 8 * buf.len() && len < 65536 && q0 == align8(pos as int) + 32,
            None => stored_hdr(lbits(buf@), pos as int) is None,
        },
{
    let ghost b = lbits(buf@);
    let q: usize = if pos % 8 == 0 { pos } else { pos + (8 - pos % 8) };
    if q > 8 * buf.len() {
        return None;
    }
    let len = match getbits_x(buf, q, 16) { None => return None, Some(v) => v };
    let nlen = match getbits_x(buf, q + 16, 16) { None => return None, Some(v) => v };
    proof {
        lemma_getbits_bound(b, q as int, 16);
        lemma_getbits_bound(b, q + 16, 16);
        reveal_with_fuel(vbits::bitspec::p2, 17);
    }
    if len + nlen != 65535 {
        return None;
    }
    Some((len as usize, q + 32))
}

/// A step that fails with `bound` bits to spare fails for every stream that
/// starts with the input: dynamic headers.
proof fn lemma_dyn_none_ext(b: Seq<bool>, f: Seq<bool>, p: int)
    requires is_prefix(b, f), dyn_header(b, p) is None, 0 <= p, p + dyn_bound() <= b.len(),
    ensures dyn_header(f, p) is None,
{
    if dyn_header(f, p) is Some {
        lemma_dyn_header_pos(f, p);
        lemma_prefix_agree(b, f, p, dyn_header(f, p).unwrap().2);
        lemma_dyn_header_agree(b, f, p);
    }
}

proof fn lemma_stored_none_ext(b: Seq<bool>, f: Seq<bool>, p: int)
    requires is_prefix(b, f), stored_hdr(b, p) is None, 0 <= p, p + 39 <= b.len(),
    ensures stored_hdr(f, p) is None,
{
    if stored_hdr(f, p) is Some {
        lemma_stored_hdr_bound(f, p);
        lemma_prefix_agree(b, f, p, stored_hdr(f, p).unwrap().1);
        lemma_stored_hdr_agree(b, f, p);
    }
}

pub open spec fn mode_rank(m: Mode) -> int {
    match m { Mode::Header => 0, _ => 1 }
}

/// What a verdict says about every stream that starts with the input.
pub open spec fn res_ok(d: &Inflater, res: Result<Status, Error>) -> bool {
    let b = d.bits();
    match res {
        Ok(Status::Done { bits, zlib }) => bits <= 8 * d.inp@.len() && forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
            d.cont(f) == Some((d.g(), bits as int, zlib)),
        Ok(Status::NeedMore) => d.cont(b) is None
            && forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                (d.cont(f) matches Some((o, _, _)) ==> d.g().len() <= o.len()),
        Err(Error::Bad) => forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==> d.cont(f) is None,
        Err(Error::TooBig) => forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
            (d.cont(f) matches Some((o, _, _)) ==> o.len() > d.max_out),
    }
}

/// The input, the limit and the output so far are kept.
pub open spec fn same_io(d0: &Inflater, d1: &Inflater) -> bool {
    &&& d1.inp@ == d0.inp@ && d1.max_out == d0.max_out
    &&& d0.n <= d1.n && d1.out@.take(d0.n as int) == d0.g()
    &&& d1.base == d0.base && d1.dropped == d0.dropped && d1.pre == d0.pre && d1.limit == d0.limit
}

pub open spec fn progress(d0: &Inflater, d1: &Inflater) -> bool {
    d1.p > d0.p || (d1.p == d0.p && mode_rank(d1.mode) < mode_rank(d0.mode))
}

/// The output so far starts every output the state can finish with.
proof fn lemma_cont_grows(d: &Inflater, f: Seq<bool>)
    requires d.inv(),
    ensures d.cont(f) matches Some((o, _, _)) ==> d.g().len() <= o.len(),
{
    reveal(Inflater::cont);
    let g = d.g();
    match d.mode {
        Mode::Header => { lemma_blocks_grow(f, d.p as int, g, d.st); }
        Mode::Fixed { last } => {
            lemma_syms_grow(fixed_lit(), fixed_dist(), f, d.p as int, g);
            match inflate_syms(fixed_lit(), fixed_dist(), f, d.p as int, g) {
                None => {}
                Some((o, q)) => { lemma_after_grow(f, d.blk@, o, q, last, d.st); }
            }
        }
        Mode::Dynamic { last, bst, .. } => {
            lemma_syms_grow(d.ll@, d.dl@, f, d.p as int, g);
            match inflate_syms(d.ll@, d.dl@, f, d.p as int, g) {
                None => {}
                Some((o, q)) => { lemma_after_grow(f, d.blk@, o, q, last, d.st && bst); }
            }
        }
        Mode::Stored { len, done, q0, last } => {
            let o = g + bytes_at(f, q0@ + 8 * done, (len - done) as nat);
            lemma_after_grow(f, d.blk@, o, q0@ + 8 * len, last, d.st);
        }
        Mode::Done { .. } => {}
    }
}

/// NeedMore, from a state whose continuation of the input itself fails.
proof fn lemma_need_more(d: &Inflater)
    requires d.inv(), d.cont(d.bits()) is None,
    ensures res_ok(d, Ok(Status::NeedMore)),
{
    assert(is_prefix(d.bits(), d.bits()));
    assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
        (d.cont(f) matches Some((o, _, _)) ==> d.g().len() <= o.len()) by {
        lemma_cont_grows(d, f);
    }
}

proof fn lemma_grows_all(d: &Inflater)
    requires d.inv(),
    ensures forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) ==>
        (d.cont(f) matches Some((o, _, _)) ==> d.g().len() <= o.len()),
{
    assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
        (d.cont(f) matches Some((o, _, _)) ==> d.g().len() <= o.len()) by {
        lemma_cont_grows(d, f);
    }
}

/// A block header read, the stream from it is the block and what follows.
pub proof fn lemma_hdr(f: Seq<bool>, p: int, g: Seq<u8>, st: bool, bfinal: nat, btype: nat)
    requires getbits(f, p, 1) == Some(bfinal), getbits(f, p + 1, 2) == Some(btype),
    ensures inflate_blocks(f, p, g, st) == match block(f, p + 3, btype, g) {
        None => None,
        Some((o, q, s)) => after_block(f, p, o, q, bfinal == 1, st && s),
    },
{
}

proof fn lemma_hdr_bits(b: Seq<bool>, f: Seq<bool>, p: int, bfinal: nat, btype: nat)
    requires is_prefix(b, f), getbits(b, p, 1) == Some(bfinal), getbits(b, p + 1, 2) == Some(btype),
    ensures getbits(f, p, 1) == Some(bfinal), getbits(f, p + 1, 2) == Some(btype),
{
    lemma_prefix_agree(b, f, p, p + 3);
    lemma_agree_sub(f, b, p, p + 3, p, p + 1);
    lemma_getbits_agree(f, b, p, 1);
    lemma_agree_sub(f, b, p, p + 3, p + 1, p + 3);
    lemma_getbits_agree(f, b, p + 1, 2);
}

proof fn lemma_hdr_stored(b: Seq<bool>, f: Seq<bool>, p: int, g: Seq<u8>, st: bool, bfinal: nat,
                          len: nat, q0: int)
    requires
        is_prefix(b, f), 0 <= p, getbits(b, p, 1) == Some(bfinal), getbits(b, p + 1, 2) == Some(0nat),
        stored_hdr(b, p + 3) == Some((len, q0)),
    ensures
        inflate_blocks(f, p, g, st) == (if q0 + 8 * len > f.len() { None } else {
            after_block(f, p, g + bytes_at(f, q0, len), q0 + 8 * len, bfinal == 1, st) }),
{
    lemma_hdr_bits(b, f, p, bfinal, 0);
    lemma_hdr(f, p, g, st, bfinal, 0);
    lemma_stored_hdr_bound(b, p + 3);
    lemma_prefix_agree(b, f, p + 3, q0);
    lemma_stored_hdr_agree(f, b, p + 3);
    lemma_stored_unfold(f, p + 3);
    assert((st && true) == st);
}

proof fn lemma_hdr_fixed(b: Seq<bool>, f: Seq<bool>, p: int, g: Seq<u8>, st: bool, bfinal: nat)
    requires is_prefix(b, f), getbits(b, p, 1) == Some(bfinal), getbits(b, p + 1, 2) == Some(1nat),
    ensures
        inflate_blocks(f, p, g, st) == match inflate_syms(fixed_lit(), fixed_dist(), f, p + 3, g) {
            None => None,
            Some((o, q)) => after_block(f, p, o, q, bfinal == 1, st),
        },
{
    lemma_hdr_bits(b, f, p, bfinal, 1);
    lemma_hdr(f, p, g, st, bfinal, 1);
    assert((st && true) == st);
}

proof fn lemma_hdr_dyn(b: Seq<bool>, f: Seq<bool>, p: int, g: Seq<u8>, st: bool, bfinal: nat,
                       lit: Seq<u8>, dist: Seq<u8>, q: int, bst: bool)
    requires
        is_prefix(b, f), 0 <= p, getbits(b, p, 1) == Some(bfinal), getbits(b, p + 1, 2) == Some(2nat),
        dyn_header(b, p + 3) == Some((lit, dist, q, bst)),
    ensures
        inflate_blocks(f, p, g, st) == match inflate_syms(lit, dist, f, q, g) {
            None => None,
            Some((o, r)) => after_block(f, p, o, r, bfinal == 1, st && bst),
        },
{
    lemma_hdr_bits(b, f, p, bfinal, 2);
    lemma_hdr(f, p, g, st, bfinal, 2);
    lemma_dyn_header_pos(b, p + 3);
    lemma_prefix_agree(b, f, p + 3, q);
    lemma_dyn_header_agree(f, b, p + 3);
}

/// A header that the input cannot hold: the spec fails on the input.
proof fn lemma_blocks_none_bits(b: Seq<bool>, p: int, g: Seq<u8>, st: bool)
    requires getbits(b, p, 1) is None || getbits(b, p + 1, 2) is None,
    ensures inflate_blocks(b, p, g, st) is None,
{
}

proof fn lemma_blocks_none_stored(b: Seq<bool>, p: int, g: Seq<u8>, st: bool, bfinal: nat)
    requires getbits(b, p, 1) == Some(bfinal), getbits(b, p + 1, 2) == Some(0nat), stored_hdr(b, p + 3) is None,
    ensures inflate_blocks(b, p, g, st) is None,
{
    lemma_hdr(b, p, g, st, bfinal, 0);
    lemma_stored_unfold(b, p + 3);
}

proof fn lemma_blocks_none_dyn(b: Seq<bool>, p: int, g: Seq<u8>, st: bool, bfinal: nat)
    requires getbits(b, p, 1) == Some(bfinal), getbits(b, p + 1, 2) == Some(2nat), dyn_header(b, p + 3) is None,
    ensures inflate_blocks(b, p, g, st) is None,
{
    lemma_hdr(b, p, g, st, bfinal, 2);
}

proof fn lemma_hdr_bad(b: Seq<bool>, f: Seq<bool>, p: int, g: Seq<u8>, st: bool, bfinal: nat, btype: nat)
    requires
        is_prefix(b, f), 0 <= p, getbits(b, p, 1) == Some(bfinal), getbits(b, p + 1, 2) == Some(btype),
        btype == 0 ==> stored_hdr(b, p + 3) is None && p + 3 + 39 <= b.len(),
        btype == 2 ==> dyn_header(b, p + 3) is None && p + 3 + dyn_bound() <= b.len(),
        btype != 1,
    ensures inflate_blocks(f, p, g, st) is None,
{
    lemma_hdr_bits(b, f, p, bfinal, btype);
    lemma_hdr(f, p, g, st, bfinal, btype);
    if btype == 0 {
        lemma_stored_none_ext(b, f, p + 3);
        lemma_stored_unfold(f, p + 3);
    } else if btype == 2 {
        lemma_dyn_none_ext(b, f, p + 3);
    }
}

/// The header read, a header that no continuation has.
fn header_bad(d: &Inflater, bfinal: u64, btype: u64) -> (r: Option<Result<Status, Error>>)
    requires
        d.inv(), d.mode is Header,
        getbits(d.bits(), d.p as int, 1) == Some(bfinal as nat), getbits(d.bits(), d.p + 1, 2) == Some(btype as nat),
        btype == 0 ==> stored_hdr(d.bits(), d.p + 3) is None && d.p + 3 + 39 <= d.bits().len(),
        btype == 2 ==> dyn_header(d.bits(), d.p + 3) is None && d.p + 3 + dyn_bound() <= d.bits().len(),
        btype != 1,
    ensures r == Some(Err::<Status, Error>(Error::Bad)), res_ok(d, Err(Error::Bad)),
{
    hide(inflate_blocks);
    hide(block);
    hide(inflate_syms);
    hide(dyn_header);
    hide(stored);
    proof {
        assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
            d.cont(f) is None by {
            cont_header(d, f);
            lemma_hdr_bad(d.bits(), f, d.p as int, d.g(), d.st, bfinal as nat, btype as nat);
        }
    }
    Some(Err(Error::Bad))
}

pub open spec fn hdr_pre(d: &Inflater, bfinal: u64, btype: u64) -> bool {
    &&& d.inv() && d.mode is Header
    &&& getbits(d.bits(), d.p as int, 1) == Some(bfinal as nat)
    &&& getbits(d.bits(), d.p + 1, 2) == Some(btype as nat)
    &&& d.p + 3 <= 8 * d.inp@.len()
}

pub open spec fn step_post(d0: &Inflater, d1: &Inflater, r: Option<Result<Status, Error>>) -> bool {
    &&& d1.inv() && same_io(d0, d1)
    &&& match r { None => progress(d0, d1), Some(res) => res_ok(d1, res) }
}

proof fn lemma_same_io_refl(d: &Inflater)
    requires d.n <= d.out@.len(),
    ensures same_io(d, d),
{
    assert(d.g().take(d.n as int) =~= d.g());
    assert(d.out@.take(d.n as int) == d.g());
}

#[verifier::spinoff_prover]
fn header_stored(d: &mut Inflater, bfinal: u64) -> (r: Option<Result<Status, Error>>)
    requires hdr_pre(&*old(d), bfinal, 0),
    ensures step_post(&*old(d), &*final(d), r),
{
    hide(inflate_blocks);
    hide(block);
    hide(inflate_syms);
    hide(dyn_header);
    hide(stored);
    let ghost b = d.bits();
    let ghost g = d.g();
    let ghost d0 = *d;
    proof { lemma_same_io_refl(&*d); assert(is_prefix(b, b)); }
    let nbits = 8 * d.inp.len();
    let p = d.p;
    match stored_hdr_x(&d.inp, p + 3) {
        None => {
            if nbits - (p + 3) >= 39 {
                return header_bad(&*d, bfinal, 0);
            }
            proof {
                lemma_blocks_none_stored(b, p as int, g, d.st, bfinal as nat);
                cont_header(&*d, b);
                lemma_need_more(&*d);
            }
            Some(Ok(Status::NeedMore))
        }
        Some((len, q0)) => {
            d.mode = Mode::Stored { len, done: 0, q0: Ghost(q0 as int), last: bfinal == 1 };
            d.blk = Ghost(p as int);
            d.p = q0;
            proof {
                codes_to(&d0, &*d);
                assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                    d.tgt(f) == lift(d.pre@, d.cont(f)) by {
                    assert(is_prefix(d0.bits(), f));
                    cont_header(&d0, f);
                    cont_stored(&*d, f);
                    lemma_hdr_stored(b, f, p as int, g, d.st, bfinal as nat, len as nat, q0 as int);
                    assert(d.g() == g);
                }
            }
            None
        }
    }
}

#[verifier::spinoff_prover]
fn header_fixed(d: &mut Inflater, bfinal: u64) -> (r: Option<Result<Status, Error>>)
    requires hdr_pre(&*old(d), bfinal, 1),
    ensures step_post(&*old(d), &*final(d), r),
{
    hide(inflate_blocks);
    hide(block);
    hide(inflate_syms);
    hide(dyn_header);
    hide(stored);
    let ghost b = d.bits();
    let ghost g = d.g();
    let ghost d0 = *d;
    proof { lemma_same_io_refl(&*d); reveal(Inflater::codes_ok); }
    let p = d.p;
    if d.fixed.is_none() {
        let ll = fixed_lit_x();
        let dl = fixed_dist_x();
        proof {
            assert(lens_ok(ll@)) by { assert forall|i: int| 0 <= i < ll@.len() implies #[trigger] ll@[i] <= 15 by {} }
            assert(lens_ok(dl@)) by { assert forall|i: int| 0 <= i < dl@.len() implies #[trigger] dl@[i] <= 15 by {} }
        }
        d.fixed = Some((build_code(&ll, 10), build_code(&dl, 5)));
    }
    d.mode = Mode::Fixed { last: bfinal == 1 };
    d.blk = Ghost(p as int);
    d.p = p + 3;
    proof {
        reveal(Inflater::codes_ok);
        assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
            d.tgt(f) == lift(d.pre@, d.cont(f)) by {
            assert(is_prefix(d0.bits(), f));
            cont_header(&d0, f);
            cont_syms(&*d, f);
            lemma_hdr_fixed(b, f, p as int, g, d.st, bfinal as nat);
            assert(d.g() == g);
        }
    }
    None
}

#[verifier::spinoff_prover]
fn header_dyn(d: &mut Inflater, bfinal: u64) -> (r: Option<Result<Status, Error>>)
    requires hdr_pre(&*old(d), bfinal, 2),
    ensures step_post(&*old(d), &*final(d), r),
{
    hide(inflate_blocks);
    hide(block);
    hide(inflate_syms);
    hide(dyn_header);
    hide(stored);
    let ghost b = d.bits();
    let ghost g = d.g();
    let ghost d0 = *d;
    proof { lemma_same_io_refl(&*d); assert(is_prefix(b, b)); reveal(Inflater::codes_ok); }
    let nbits = 8 * d.inp.len();
    let p = d.p;
    match dyn_header_x(&d.inp, p + 3) {
        Err(_) => {
            if nbits - (p + 3) >= 7100 {
                return header_bad(&*d, bfinal, 2);
            }
            proof { lemma_blocks_none_dyn(b, p as int, g, d.st, bfinal as nat); cont_header(&*d, b); lemma_need_more(&*d); }
            Some(Ok(Status::NeedMore))
        }
        Ok((lit, dist, q, bst)) => {
            let lh = build_code(&lit, 10);
            let dh = build_code(&dist, 10);
            d.ll = Ghost(lit@);
            d.dl = Ghost(dist@);
            d.mode = Mode::Dynamic { lit: lh, dist: dh, last: bfinal == 1, bst };
            d.blk = Ghost(p as int);
            d.p = q;
            proof {
                reveal(Inflater::codes_ok);
                lemma_dyn_header_pos(b, p + 3);
                assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                    d.tgt(f) == lift(d.pre@, d.cont(f)) by {
                    assert(is_prefix(d0.bits(), f));
                    cont_header(&d0, f);
                    cont_syms(&*d, f);
                    lemma_hdr_dyn(b, f, p as int, g, d.st, bfinal as nat, lit@, dist@, q as int, bst);
                    assert(d.g() == g);
                }
            }
            None
        }
    }
}

/// A block header.
fn step_header(d: &mut Inflater) -> (r: Option<Result<Status, Error>>)
    requires old(d).inv(), old(d).mode is Header,
    ensures step_post(&*old(d), &*final(d), r),
{
    hide(inflate_blocks);
    hide(block);
    hide(inflate_syms);
    hide(dyn_header);
    hide(stored);
    proof { lemma_same_io_refl(&*d); }
    let p = d.p;
    let bfinal = match getbits_x(&d.inp, p, 1) {
        None => {
            proof { lemma_blocks_none_bits(d.bits(), p as int, d.g(), d.st); cont_header(&*d, d.bits()); lemma_need_more(&*d); }
            return Some(Ok(Status::NeedMore));
        }
        Some(v) => v,
    };
    let btype = match getbits_x(&d.inp, p + 1, 2) {
        None => {
            proof { lemma_blocks_none_bits(d.bits(), p as int, d.g(), d.st); cont_header(&*d, d.bits()); lemma_need_more(&*d); }
            return Some(Ok(Status::NeedMore));
        }
        Some(v) => v,
    };
    if btype == 0 {
        header_stored(d, bfinal)
    } else if btype == 1 {
        header_fixed(d, bfinal)
    } else if btype == 2 {
        header_dyn(d, bfinal)
    } else {
        header_bad(&*d, bfinal, btype)
    }
}


/// Run the block's symbols from `d.p`; `syms_run`'s result, with the codes
/// of the current block.
#[verifier::spinoff_prover]
fn run_block(d: &mut Inflater) -> (r: (Run, usize, usize))
    requires old(d).inv(), old(d).mode is Fixed || old(d).mode is Dynamic,
    ensures
        ({
            let (run, p, n) = r;
            let b = old(d).bits();
            let ll = cur_ll(&*old(d));
            let dl = cur_dl(&*old(d));
            let g0 = old(d).g();
            let g = final(d).out@.take(n as int);
            &&& final(d).inp == old(d).inp && final(d).n == old(d).n && final(d).p == old(d).p
            &&& final(d).blk == old(d).blk && final(d).st == old(d).st && final(d).mode == old(d).mode
            &&& final(d).fixed == old(d).fixed && final(d).max_out == old(d).max_out
            &&& final(d).ll == old(d).ll && final(d).dl == old(d).dl
            &&& final(d).base == old(d).base && final(d).dropped == old(d).dropped
            &&& final(d).pre == old(d).pre && final(d).limit == old(d).limit
            &&& p <= 8 * old(d).inp@.len() && n <= old(d).max_out && n <= final(d).out@.len()
            &&& old(d).n <= n && final(d).out@.take(old(d).n as int) == g0 && old(d).p <= p
            &&& match run {
                Run::End => forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                    inflate_syms(ll, dl, f, old(d).p as int, g0) == Some((g, p as int)),
                Run::Pause => (forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                        inflate_syms(ll, dl, f, old(d).p as int, g0) == inflate_syms(ll, dl, f, p as int, g))
                    && sym_step(ll, dl, b, p as int) is None,
                Run::Bad => forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                    inflate_syms(ll, dl, f, old(d).p as int, g0) is None,
                Run::TooBig => forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                    (inflate_syms(ll, dl, f, old(d).p as int, g0) matches Some((o, _)) ==> o.len() > old(d).max_out),
            }
        }),
{
    proof { reveal(Inflater::codes_ok); }
    match &d.mode {
        Mode::Dynamic { lit, dist, .. } =>
            syms_run(lit, dist, d.ll, d.dl, &d.inp, d.p, &mut d.out, d.n, d.max_out),
        _ => match &d.fixed {
            Some((lh, dh)) =>
                syms_run(lh, dh, Ghost(fixed_lit()), Ghost(fixed_dist()), &d.inp, d.p, &mut d.out, d.n, d.max_out),
            None => (Run::Bad, d.p, d.n),  // not reached
        },
    }
}

/// A block's symbols, as far as the input goes.
#[verifier::spinoff_prover]
fn step_syms(d: &mut Inflater) -> (r: Option<Result<Status, Error>>)
    requires old(d).inv(), old(d).mode is Fixed || old(d).mode is Dynamic,
    ensures step_post(&*old(d), &*final(d), r),
{
    hide(inflate_blocks);
    hide(block);
    hide(inflate_syms);
    hide(dyn_header);
    hide(stored);
    let ghost d0 = *d;
    let ghost b = d.bits();
    let ghost g = d.g();
    let ghost ll = cur_ll(&*d);
    let ghost dl = cur_dl(&*d);
    proof { lemma_same_io_refl(&*d); assert(is_prefix(b, b)); }
    let (last, bst) = match &d.mode {
        Mode::Fixed { last } => (*last, true),
        Mode::Dynamic { last, bst, .. } => (*last, *bst),
        _ => (true, true),
    };
    let p0 = d.p;
    let n0 = d.n;
    let (run, p2, n2) = run_block(d);
    let ghost g2 = d.out@.take(n2 as int);
    proof { assert(d.g() == g); codes_same(&d0, &*d); }
    match run {
        Run::End => {
            d.n = n2;
            d.p = p2;
            d.st = d.st && bst;
            proof { lemma_syms_pos(ll, dl, b, p0 as int, g); }
            if last {
                d.mode = Mode::Done { q: p2 };
                proof {
                    codes_to(&d0, &*d);
                    assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                        d.tgt(f) == lift(d.pre@, d.cont(f)) by {
                        assert(is_prefix(d0.bits(), f));
                        cont_syms(&d0, f);
                        cont_done(&*d, f);
                    }
                    assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                        d.cont(f) == Some((d.g(), p2 as int, d.st)) by {
                        cont_done(&*d, f);
                    }
                }
                return Some(Ok(Status::Done { bits: p2, zlib: d.st }));
            }
            proof { assert(p2 > d.blk@); }
            d.mode = Mode::Header;
            proof {
                codes_to(&d0, &*d);
                assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                    d.tgt(f) == lift(d.pre@, d.cont(f)) by {
                    assert(is_prefix(d0.bits(), f));
                    cont_syms(&d0, f);
                    cont_header(&*d, f);
                    assert(f.len() >= b.len());
                }
            }
            None
        }
        Run::Pause => {
            d.n = n2;
            d.p = p2;
            proof {
                codes_same(&d0, &*d);
                assert(cur_ll(&*d) == ll && cur_dl(&*d) == dl);
                assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                    d.tgt(f) == lift(d.pre@, d.cont(f)) by {
                    assert(is_prefix(d0.bits(), f));
                    cont_syms(&d0, f);
                    cont_syms(&*d, f);
                }
                lemma_syms_unfold(ll, dl, b, p2 as int, g2);
                cont_syms(&*d, b);
                lemma_need_more(&*d);
            }
            Some(Ok(Status::NeedMore))
        }
        Run::Bad => {
            proof {
                codes_same(&d0, &*d);
                assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                    d.cont(f) is None by {
                    assert(is_prefix(d0.bits(), f));
                    cont_syms(&d0, f);
                    cont_same(&*d, &d0, f);
                }
                assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                    d.tgt(f) == lift(d.pre@, d.cont(f)) by {
                    assert(is_prefix(d0.bits(), f));
                    cont_same(&*d, &d0, f);
                }
            }
            Some(Err(Error::Bad))
        }
        Run::TooBig => {
            proof {
                codes_same(&d0, &*d);
                assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                    (d.cont(f) matches Some((o, _, _)) ==> o.len() > d.max_out) by {
                    assert(is_prefix(d0.bits(), f));
                    cont_syms(&d0, f);
                    cont_same(&*d, &d0, f);
                    match inflate_syms(ll, dl, f, p0 as int, g) {
                        None => {}
                        Some((o, q)) => { lemma_after_grow(f, d0.blk@, o, q, last, d0.st && bst); }
                    }
                }
                assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                    d.tgt(f) == lift(d.pre@, d.cont(f)) by {
                    assert(is_prefix(d0.bits(), f));
                    cont_same(&*d, &d0, f);
                }
            }
            Some(Err(Error::TooBig))
        }
    }
}

/// A stored block's bytes, as many as the input has.
#[verifier::spinoff_prover]
fn step_stored(d: &mut Inflater) -> (r: Option<Result<Status, Error>>)
    requires old(d).inv(), old(d).mode is Stored,
    ensures step_post(&*old(d), &*final(d), r),
{
    hide(inflate_blocks);
    hide(block);
    hide(inflate_syms);
    hide(dyn_header);
    hide(stored);
    let ghost d0 = *d;
    let ghost b = d.bits();
    let ghost g = d.g();
    proof { lemma_same_io_refl(&*d); assert(is_prefix(b, b)); }
    let (len, done, q0, last) = match &d.mode {
        Mode::Stored { len, done, q0, last } => (*len, *done, *q0, *last),
        _ => (0, 0, Ghost(0), true),
    };
    let nbits = 8 * d.inp.len();
    let p = d.p;
    let n = d.n;
    let rem = len - done;
    if rem > d.max_out - d.n {
        proof {
            assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
                (d.cont(f) matches Some((o, _, _)) ==> o.len() > d.max_out) by {
                cont_stored(&d0, f);
                let o = g + bytes_at(f, q0@ + 8 * done, rem as nat);
                lemma_after_grow(f, d.blk@, o, q0@ + 8 * len, last, d.st);
            }
        }
        return Some(Err(Error::TooBig));
    }
    let avail = (nbits - p) / 8;
    let m = if rem < avail { rem } else { avail };
    grow(&mut d.out, n, n + m);
    let ol = d.out.len();
    let il = d.inp.len();
    let start = p / 8;
    assert(8 * start == p) by (nonlinear_arith)
        requires start == p / 8, p == q0@ + 8 * done, q0@ % 8 == 0;
    assert(start + m <= d.inp@.len()) by (nonlinear_arith)
        requires avail == (nbits - p) / 8, m <= avail, nbits == 8 * d.inp@.len(), 8 * start == p, p <= nbits;
    let mut j: usize = 0;
    while j < m
        invariant
            j <= m, n + m <= ol, ol == d.out@.len(), start + m <= il, il == d.inp@.len(), 8 * start == p,
            b == lbits(d.inp@),
            d.out@.take((n + j) as int) == g + bytes_at(b, p as int, j as nat),
        decreases m - j,
    {
        let ghost o1 = d.out@;
        let x = d.inp[start + j];
        d.out.set(n + j, x);
        proof {
            lemma_aligned_byte_at(d.inp@, (start + j) as int);
            assert(8 * (start + j) == p + 8 * j);
            assert(bytes_at(b, p as int, (j + 1) as nat) =~= bytes_at(b, p as int, j as nat).push(x));
            assert(d.out@.take((n + j + 1) as int) =~= o1.take((n + j) as int).push(x));
        }
        j = j + 1;
    }
    proof {
        assert(d.out@.take(n as int) =~= d.out@.take((n + m) as int).take(n as int));
        assert((g + bytes_at(b, p as int, m as nat)).take(n as int) =~= g);
    }
    d.n = n + m;
    d.p = p + 8 * m;
    d.mode = Mode::Stored { len, done: done + m, q0, last };
    proof {
        codes_to(&d0, &*d);
        assert(d.g() == g + bytes_at(b, p as int, m as nat));
        assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
            d.tgt(f) == lift(d.pre@, d.cont(f)) by {
            assert(is_prefix(d0.bits(), f));
            cont_stored(&d0, f);
            cont_stored(&*d, f);
            lemma_prefix_agree(b, f, p as int, p + 8 * m);
            lemma_bytes_agree(f, b, p as int, m as nat);
            lemma_bytes_split(f, p as int, rem as nat, m as nat);
            assert(q0@ + 8 * done == p);
            assert(g + bytes_at(f, p as int, rem as nat)
                =~= (g + bytes_at(b, p as int, m as nat)) + bytes_at(f, p + 8 * m, (rem - m) as nat));
            assert(q0@ + 8 * (done + m) == p + 8 * m);
        }
    }
    if done + m < len {
        proof {
            assert(q0@ + 8 * len > nbits) by (nonlinear_arith)
                requires avail == (nbits - p) / 8, m == avail, m < rem, rem == len - done, p == q0@ + 8 * done, p <= nbits;
            cont_stored(&*d, b);
            lemma_need_more(&*d);
        }
        return Some(Ok(Status::NeedMore));
    }
    let q = d.p;
    if last {
        d.mode = Mode::Done { q };
        proof {
            codes_to(&d0, &*d);
            assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                d.tgt(f) == lift(d.pre@, d.cont(f)) by {
                assert(is_prefix(d0.bits(), f));
                cont_stored(&d0, f);
                cont_done(&*d, f);
                lemma_bytes_split(f, p as int, rem as nat, m as nat);
                assert(bytes_at(f, q as int, 0) =~= Seq::<u8>::empty());
                assert(d.g() + bytes_at(f, q as int, 0) =~= d.g());
                lemma_prefix_agree(b, f, p as int, p + 8 * m);
                lemma_bytes_agree(f, b, p as int, m as nat);
            }
            assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                d.cont(f) == Some((d.g(), q as int, d.st)) by {
                cont_done(&*d, f);
            }
        }
        return Some(Ok(Status::Done { bits: q, zlib: d.st }));
    }
    d.mode = Mode::Header;
    proof {
        codes_to(&d0, &*d);
        assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
            d.tgt(f) == lift(d.pre@, d.cont(f)) by {
            assert(is_prefix(d0.bits(), f));
            cont_stored(&d0, f);
            cont_header(&*d, f);
            lemma_bytes_split(f, p as int, rem as nat, m as nat);
            assert(bytes_at(f, q as int, 0) =~= Seq::<u8>::empty());
            assert(d.g() + bytes_at(f, q as int, 0) =~= d.g());
            lemma_prefix_agree(b, f, p as int, p + 8 * m);
            lemma_bytes_agree(f, b, p as int, m as nat);
            assert(f.len() >= b.len());
        }
    }
    None
}

/// The byte at a byte-aligned bit position is the buffer's byte.
proof fn lemma_aligned_byte_at(buf: Seq<u8>, k: int)
    requires 0 <= k < buf.len(),
    ensures vbits::lsb::lval(lbits(buf).subrange(8 * k, 8 * k + 8)) == buf[k] as nat,
{
    assert(lbits(buf).subrange(8 * k, 8 * k + 8) =~= lbits(seq![buf[k]])) by {
        assert forall|i: int| 0 <= i < 8 implies
            #[trigger] lbits(buf).subrange(8 * k, 8 * k + 8)[i] == lbits(seq![buf[k]])[i] by {
            assert((8 * k + i) / 8 == k) by (nonlinear_arith) requires 0 <= i < 8;
            assert((8 * k + i) % 8 == i) by (nonlinear_arith) requires 0 <= i < 8;
        }
    }
    lemma_lval_byte(buf[k]);
}

// ------------------------------------------------ keeping memory bounded

proof fn lemma_after_win(f: Seq<bool>, blk: int, o: Seq<u8>, pre: Seq<u8>, q: int, last: bool, s: bool)
    requires win_of(o, pre + o),
    ensures after_block(f, blk, pre + o, q, last, s) == lift(pre, after_block(f, blk, o, q, last, s)),
{
    if !last && !(q <= blk || q > f.len()) {
        lemma_blocks_win(f, q, o, pre + o, s);
        assert((pre + o).take((pre + o).len() - o.len()) =~= pre);
    }
}

/// Trimming the output: the continuation is the trimmed one's, with the
/// trimmed bytes in front.
proof fn cont_win(d: &Inflater, d2: &Inflater, t: nat, f: Seq<bool>)
    requires
        t <= d.n, d.n <= d.out@.len(), d2.g() == d.g().skip(t as int), d2.n >= 32768, d2.n <= d2.out@.len(),
        d2.p == d.p, d2.blk == d.blk, d2.st == d.st, d2.mode == d.mode, d2.ll == d.ll, d2.dl == d.dl,
    ensures d.cont(f) == lift(d.g().take(t as int), d2.cont(f)),
{
    let g = d.g();
    let w = d2.g();
    let pre = g.take(t as int);
    assert(g =~= pre + w);
    assert(win_of(w, g)) by { assert(g.skip(g.len() - w.len()) =~= w); }
    assert(g.take(g.len() - w.len()) =~= pre);
    if d.mode is Header {
        cont_header(d, f);
        cont_header(d2, f);
        lemma_blocks_win(f, d.p as int, w, g, d.st);
    } else if d.mode is Fixed || d.mode is Dynamic {
        cont_syms(d, f);
        cont_syms(d2, f);
        lemma_syms_win(cur_ll(d), cur_dl(d), f, d.p as int, w, g);
        match inflate_syms(cur_ll(d), cur_dl(d), f, d.p as int, w) {
            None => {}
            Some((o, q)) => { lemma_after_win(f, d.blk@, o, pre, q, cur_last(d), d.st && cur_bst(d)); }
        }
    } else if d.mode is Stored {
        cont_stored(d, f);
        cont_stored(d2, f);
        let (len, done, q0) = match d.mode { Mode::Stored { len, done, q0, .. } => (len, done, q0@), _ => (0, 0, 0) };
        let q = q0 + 8 * len;
        if q <= f.len() {
            let x = bytes_at(f, q0 + 8 * done, (len - done) as nat);
            lemma_win_append(w, g, x);
            assert(g + x =~= pre + (w + x));
            lemma_after_win(f, d.blk@, w + x, pre, q, cur_last(d), d.st);
        }
    } else {
        cont_done(d, f);
        cont_done(d2, f);
    }
}

proof fn lemma_after_shift(f: Seq<bool>, k: int, blk: int, o: Seq<u8>, q: int, last: bool, s: bool)
    requires 0 <= k <= q, k <= f.len(), k % 8 == 0,
    ensures after_block(f, blk, o, q, last, s) == pshift(after_block(f.skip(k), blk - k, o, q - k, last, s), k),
{
    if !last && !(q <= blk || q > f.len()) {
        lemma_blocks_shift(f, k, q, o, s);
    }
}

pub open spec fn shift_rel(d: &Inflater, d2: &Inflater, k: nat) -> bool {
    &&& 8 * k <= d.p && d2.p == d.p - 8 * k && d2.blk@ == d.blk@ - 8 * k
    &&& d2.g() == d.g() && d2.st == d.st && d2.ll == d.ll && d2.dl == d.dl
    &&& k <= d.inp@.len()
    &&& match (d.mode, d2.mode) {
        (Mode::Header, Mode::Header) => true,
        (Mode::Fixed { last }, Mode::Fixed { last: l2 }) => last == l2,
        (Mode::Dynamic { last, bst, .. }, Mode::Dynamic { last: l2, bst: b2, .. }) => last == l2 && bst == b2,
        (Mode::Stored { len, done, q0, last }, Mode::Stored { len: n2, done: e2, q0: r2, last: l2 }) =>
            len == n2 && done == e2 && last == l2 && r2@ == q0@ - 8 * k && d.p == q0@ + 8 * done && done <= len,
        (Mode::Done { q }, Mode::Done { q: q2 }) => q2 == q - 8 * k,
        _ => false,
    }
}

proof fn cont_shift_syms(d: &Inflater, d2: &Inflater, k: nat, f2: Seq<bool>)
    requires shift_rel(d, d2, k), d.mode is Fixed || d.mode is Dynamic,
    ensures d.cont(lbits(d.inp@.take(k as int)) + f2) == pshift(d2.cont(f2), 8 * k as int),
{
    let kk: int = 8 * k as int;
    let f = lbits(d.inp@.take(k as int)) + f2;
    assert(f.skip(kk) =~= f2);
    let g = d.g();
    cont_syms(d, f);
    cont_syms(d2, f2);
    assert(cur_ll(d2) == cur_ll(d) && cur_dl(d2) == cur_dl(d) && cur_last(d2) == cur_last(d) && cur_bst(d2) == cur_bst(d));
    lemma_syms_shift(cur_ll(d), cur_dl(d), f, kk, d.p as int, g);
    match inflate_syms(cur_ll(d), cur_dl(d), f2, d2.p as int, g) {
        None => {}
        Some((o, q)) => {
            lemma_syms_pos(cur_ll(d), cur_dl(d), f2, d2.p as int, g);
            lemma_after_shift(f, kk, d.blk@, o, q + kk, cur_last(d), d.st && cur_bst(d));
        }
    }
}

proof fn cont_shift_stored(d: &Inflater, d2: &Inflater, k: nat, f2: Seq<bool>)
    requires shift_rel(d, d2, k), d.mode is Stored,
    ensures d.cont(lbits(d.inp@.take(k as int)) + f2) == pshift(d2.cont(f2), 8 * k as int),
{
    hide(inflate_blocks);
    hide(block);
    hide(inflate_syms);
    hide(dyn_header);
    hide(stored);
    let kk: int = 8 * k as int;
    let f = lbits(d.inp@.take(k as int)) + f2;
    assert(f.skip(kk) =~= f2);
    let g = d.g();
    cont_stored(d, f);
    cont_stored(d2, f2);
    let (len, done, q0) = match d.mode { Mode::Stored { len, done, q0, .. } => (len, done, q0@), _ => (0, 0, 0) };
    let q = q0 + 8 * len;
    if q <= f.len() {
        assert(q0 + 8 * done + 8 * (len - done) == q) by (nonlinear_arith) requires done <= len, q == q0 + 8 * len;
        lemma_bytes_shift(f, kk, q0 + 8 * done, (len - done) as nat);
        lemma_after_shift(f, kk, d.blk@, g + bytes_at(f, q0 + 8 * done, (len - done) as nat), q, cur_last(d), d.st);
    }
}

/// Dropping `k` bytes of input: the continuation is the shorter one's, its
/// positions moved.
proof fn cont_shift(d: &Inflater, d2: &Inflater, k: nat, f2: Seq<bool>)
    requires shift_rel(d, d2, k),
    ensures d.cont(lbits(d.inp@.take(k as int)) + f2) == pshift(d2.cont(f2), 8 * k as int),
{
    let kk: int = 8 * k as int;
    let f = lbits(d.inp@.take(k as int)) + f2;
    assert(f.skip(kk) =~= f2);
    if d.mode is Header {
        cont_header(d, f);
        cont_header(d2, f2);
        lemma_blocks_shift(f, kk, d.p as int, d.g(), d.st);
    } else if d.mode is Fixed || d.mode is Dynamic {
        cont_shift_syms(d, d2, k, f2);
    } else if d.mode is Stored {
        cont_shift_stored(d, d2, k, f2);
    } else {
        cont_done(d, f);
        cont_done(d2, f2);
    }
}

/// Keep the last 32768 bytes of output, if there are more than 65536.
#[verifier::spinoff_prover]
fn trim_out(d: &mut Inflater)
    requires old(d).inv(),
    ensures
        final(d).inv(), final(d).whole() == old(d).whole(), final(d).fed() == old(d).fed(),
        final(d).inp == old(d).inp && final(d).p == old(d).p && final(d).base == old(d).base,
        final(d).limit == old(d).limit, final(d).mode == old(d).mode,
        final(d).n <= 65536,
{
    if d.n > 65536 {
        let ghost d0 = *d;
        let t = d.n - 32768;
        let n = d.n;
        d.out.as_mut_slice().copy_within(t..n, 0);
        let ghost pre2 = d0.pre@ + d0.g().take(t as int);
        d.n = 32768;
        d.max_out = d.max_out - t;
        d.pre = Ghost(pre2);
        proof {
            assert(d.g() =~= d0.g().skip(t as int)) by {
                assert forall|i: int| 0 <= i < 32768 implies #[trigger] d.g()[i] == d0.g().skip(t as int)[i] by {
                    assert(d.out@[i] == d0.out@[t + i]);
                }
            }
            assert(d.whole() =~= d0.whole()) by {
                assert(d0.g() =~= d0.g().take(t as int) + d0.g().skip(t as int));
            }
            codes_same(&d0, &*d);
            assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                d.tgt(f) == lift(d.pre@, d.cont(f)) by {
                assert(is_prefix(d0.bits(), f));
                cont_win(&d0, &*d, t as nat, f);
                match d.cont(f) {
                    None => {}
                    Some((o, q, st)) => { assert(d0.pre@ + (d0.g().take(t as int) + o) =~= pre2 + o); }
                }
            }
        }
    }
}

/// Drop the input before the byte the next step starts in.
#[verifier::spinoff_prover]
fn drop_in(d: &mut Inflater)
    requires old(d).inv(),
    ensures
        final(d).inv(), final(d).whole() == old(d).whole(), final(d).fed() == old(d).fed(),
        final(d).limit == old(d).limit, final(d).n == old(d).n,
        !(old(d).mode is Done) ==> final(d).p < 8,
        final(d).inp@.len() + final(d).base == old(d).inp@.len() + old(d).base,
{
    hide(inflate_blocks);
    hide(block);
    hide(inflate_syms);
    hide(dyn_header);
    hide(stored);
    let k = d.p / 8;
    if k == 0 || d.mode.is_done() {
        proof { assert(k == 0 ==> d.p < 8); }
        return;
    }
    let ghost d0 = *d;
    let mut inp2: Vec<u8> = Vec::with_capacity(d.inp.len() - k);
    append(&mut inp2, vstd::slice::slice_subrange(d.inp.as_slice(), k, d.inp.len()));
    proof { assert(inp2@ =~= d.inp@.subrange(k as int, d.inp@.len() as int)); }
    let ghost dropped2 = d0.dropped@ + d0.inp@.take(k as int);
    d.inp = inp2;
    d.p = d.p - 8 * k;
    d.blk = Ghost(d0.blk@ - 8 * k);
    d.base = d.base + k;
    d.dropped = Ghost(dropped2);
    let ghost kk = 8 * k as int;
    match &mut d.mode {
        Mode::Stored { q0, .. } => { *q0 = Ghost(q0@ - kk); }
        _ => {}
    }
    proof {
        assert(d.inp@ =~= d0.inp@.skip(k as int));
        assert(d.fed() =~= d0.fed()) by {
            assert(d0.inp@ =~= d0.inp@.take(k as int) + d0.inp@.skip(k as int));
        }
        assert(d.p < 8) by (nonlinear_arith) requires d.p == d0.p - 8 * (d0.p / 8);
        if d.mode is Stored { codes_to(&d0, &*d); } else { codes_same(&d0, &*d); }
        lemma_lbits_add(d0.inp@.take(k as int), d.inp@);
        assert forall|f2: Seq<bool>| #[trigger] is_prefix(d.bits(), f2) implies
            d.tgt(f2) == lift(d.pre@, d.cont(f2)) by {
            let pre = lbits(d0.inp@.take(k as int));
            let f = pre + f2;
            assert(lbits(d0.inp@) =~= pre + lbits(d.inp@)) by {
                assert(d0.inp@ =~= d0.inp@.take(k as int) + d.inp@);
            }
            assert(is_prefix(d0.bits(), f)) by {
                assert forall|i: int| 0 <= i < d0.bits().len() implies #[trigger] d0.bits()[i] == f[i] by {
                    if i >= pre.len() { assert(d.bits()[i - pre.len()] == f2[i - pre.len()]); }
                }
            }
            cont_shift(&d0, &*d, k as nat, f2);
            lemma_lbits_add(d0.dropped@, d0.inp@.take(k as int));
            assert(lbits(dropped2) + f2 =~= lbits(d0.dropped@) + f);
        }
    }
}

/// What a verdict says about every stream that starts with all the input.
pub open spec fn global_ok(d: &Inflater, res: Result<Status, Error>) -> bool {
    let b = lbits(d.fed());
    match res {
        Ok(Status::Done { bits, zlib }) => forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
            inflate_blocks(f, 0, Seq::empty(), true) == Some((d.whole(), bits as int, zlib)),
        Ok(Status::NeedMore) => inflate_blocks(b, 0, Seq::empty(), true) is None
            && forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
                (inflate_blocks(f, 0, Seq::empty(), true) matches Some((o, _, _)) ==> d.whole().len() <= o.len()),
        Err(Error::Bad) => forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
            inflate_blocks(f, 0, Seq::empty(), true) is None,
        Err(Error::TooBig) => forall|f: Seq<bool>| #[trigger] is_prefix(b, f) ==>
            (inflate_blocks(f, 0, Seq::empty(), true) matches Some((o, _, _)) ==> o.len() > d.limit),
    }
}

/// A stream that starts with all the input is the dropped input, then one
/// that starts with the input kept.
proof fn lemma_global(d: &Inflater, f: Seq<bool>)
    requires d.inv(), is_prefix(lbits(d.fed()), f),
    ensures
        is_prefix(d.bits(), f.skip(8 * d.base)),
        inflate_blocks(f, 0, Seq::empty(), true) == pshift(lift(d.pre@, d.cont(f.skip(8 * d.base))), 8 * d.base),
{
    hide(inflate_blocks);
    let k = 8 * d.base;
    lemma_lbits_add(d.dropped@, d.inp@);
    let f2 = f.skip(k);
    assert(lbits(d.dropped@).len() == k);
    assert(lbits(d.dropped@) + f2 =~= f) by {
        assert forall|i: int| 0 <= i < k implies #[trigger] f[i] == lbits(d.dropped@)[i] by {
            assert(lbits(d.fed())[i] == f[i]);
        }
    }
    assert forall|i: int| 0 <= i < d.bits().len() implies #[trigger] d.bits()[i] == f2[i] by {
        assert(lbits(d.fed())[k + i] == f[k + i]);
    }
    assert(is_prefix(d.bits(), f2));
    match inflate_blocks(f, 0, Seq::empty(), true) {
        None => {}
        Some((o, q, s)) => {}
    }
}

proof fn lemma_global_done(d: &Inflater, bits: usize, zlib: bool)
    requires d.inv(), res_ok(d, Ok(Status::Done { bits, zlib })),
    ensures forall|f: Seq<bool>| #[trigger] is_prefix(lbits(d.fed()), f) ==>
        inflate_blocks(f, 0, Seq::empty(), true) == Some((d.whole(), 8 * d.base + bits, zlib)),
{
    hide(inflate_blocks);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(d.fed()), f) implies
        inflate_blocks(f, 0, Seq::empty(), true) == Some((d.whole(), 8 * d.base + bits, zlib)) by {
        lemma_global(d, f);
    }
}

proof fn lemma_global_need(d: &Inflater)
    requires d.inv(), res_ok(d, Ok(Status::NeedMore)),
    ensures global_ok(d, Ok(Status::NeedMore)),
{
    hide(inflate_blocks);
    let b = lbits(d.fed());
    assert(is_prefix(b, b));
    lemma_global(d, b);
    lemma_lbits_add(d.dropped@, d.inp@);
    assert(b.skip(8 * d.base) =~= d.bits());
    assert forall|f: Seq<bool>| #[trigger] is_prefix(b, f) implies
        (inflate_blocks(f, 0, Seq::empty(), true) matches Some((o, _, _)) ==> d.whole().len() <= o.len()) by {
        lemma_global(d, f);
    }
}

proof fn lemma_global_bad(d: &Inflater)
    requires d.inv(), res_ok(d, Err(Error::Bad)),
    ensures global_ok(d, Err(Error::Bad)),
{
    hide(inflate_blocks);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(d.fed()), f) implies
        inflate_blocks(f, 0, Seq::empty(), true) is None by {
        lemma_global(d, f);
    }
}

proof fn lemma_global_big(d: &Inflater)
    requires d.inv(), res_ok(d, Err(Error::TooBig)),
    ensures global_ok(d, Err(Error::TooBig)),
{
    hide(inflate_blocks);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(d.fed()), f) implies
        (inflate_blocks(f, 0, Seq::empty(), true) matches Some((o, _, _)) ==> o.len() > d.limit) by {
        lemma_global(d, f);
    }
}

/// After the steps: the new output to the sink, the verdict about the
/// whole stream, and, when more input is wanted, only what the rest needs.
#[verifier::spinoff_prover]
fn finish_feed(d: Inflater, res: Result<Status, Error>, n_start: usize, sink: &mut Vec<u8>,
               Ghost(w0): Ghost<Seq<u8>>) -> (r: (Inflater, Result<Status, Error>))
    requires
        d.inv(), res_ok(&d, res), n_start <= d.n, w0 == d.pre@ + d.out@.take(n_start as int),
    ensures
        ({
            let (d2, res2) = r;
            &&& d2.inv() && d2.fed() == d.fed() && d2.limit == d.limit && d2.whole() == d.whole()
            &&& final(sink)@ == old(sink)@ + d.whole().skip(w0.len() as int)
            &&& d.whole().take(w0.len() as int) == w0
            &&& global_ok(&d2, res2)
            &&& (res2 == Ok::<Status, Error>(Status::NeedMore) ==> d2.p < 8 && d2.n <= 65536 + 266)
        }),
{
    let mut d = d;
    let ghost sk0 = sink@;
    append(sink, vstd::slice::slice_subrange(d.out.as_slice(), n_start, d.n));
    proof {
        assert(d.whole() =~= w0 + d.out@.subrange(n_start as int, d.n as int)) by {
            assert(d.g() =~= d.out@.take(n_start as int) + d.out@.subrange(n_start as int, d.n as int));
        }
        assert(d.whole().take(w0.len() as int) =~= w0);
        assert(d.whole().skip(w0.len() as int) =~= d.out@.subrange(n_start as int, d.n as int));
        match res {
            Ok(Status::Done { bits, zlib }) => { lemma_global_done(&d, bits, zlib); }
            Ok(Status::NeedMore) => { lemma_global_need(&d); }
            Err(Error::Bad) => { lemma_global_bad(&d); }
            Err(Error::TooBig) => { lemma_global_big(&d); }
        }
    }
    let ghost dres = d;
    match res {
        Ok(Status::Done { bits, zlib }) => {
            let bits_g = 8 * d.base + bits;
            proof {
                assert(d.inv());
                assert(global_ok(&d, Ok(Status::Done { bits: bits_g, zlib })));
                assert(sink@ == sk0 + d.whole().skip(w0.len() as int));
            }
            (d, Ok(Status::Done { bits: bits_g, zlib }))
        }
        Ok(Status::NeedMore) => {
            proof { if d.mode is Done { cont_done(&d, d.bits()); } }
            // keep only what the rest needs
            trim_out(&mut d);
            drop_in(&mut d);
            proof {
                assert(d.fed() == dres.fed());
                assert(d.whole() == dres.whole());
                assert(d.inv());
                assert(global_ok(&dres, Ok(Status::NeedMore)));
                assert(global_ok(&d, Ok(Status::NeedMore)));
                assert(d.p < 8);
                assert(d.n <= 65536 + 266);
            }
            (d, Ok(Status::NeedMore))
        }
        Err(e) => (d, Err(e)),
    }
}

impl Inflater {
    /// Take the next piece of input, decode as far as it allows, and append
    /// the output decoded to `sink`.
    #[verifier::spinoff_prover]
    pub fn feed(self, chunk: &[u8], sink: &mut Vec<u8>) -> (r: (Inflater, Result<Status, Error>))
        requires self.inv(), self.base + self.inp@.len() + chunk@.len() < max_input(),
        ensures
            ({
                let (d, res) = r;
                &&& d.inv()
                &&& d.fed() == self.fed() + chunk@
                &&& d.limit == self.limit
                &&& d.whole().len() >= self.whole().len() && d.whole().take(self.whole().len() as int) == self.whole()
                &&& final(sink)@ == old(sink)@ + d.whole().skip(self.whole().len() as int)
                &&& global_ok(&d, res)
                &&& (res == Ok::<Status, Error>(Status::NeedMore) ==> d.p < 8 && d.n <= 65536 + 266)
            }),
    {
        let ghost s0 = self;
        let Inflater { mut inp, out, n, p, blk, st, mode, fixed, max_out, ll, dl, base, dropped, pre, limit } = self;
        let ghost b0 = lbits(inp@);
        let ghost inp0 = inp@;
        append(&mut inp, chunk);
        proof {
            assert(chunk@.take(chunk.len() as int) =~= chunk@);
            lemma_lbits_prefix(inp0, chunk@);
            assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(inp@), f) implies is_prefix(b0, f) by {
                lemma_prefix_trans(b0, lbits(inp@), f);
            }
        }
        let ghost b = lbits(inp@);
        let nbits: usize = 8 * inp.len();
        let n_start = n;
        let mut d = Inflater { inp, out, n, p, blk, st, mode, fixed, max_out, ll, dl, base, dropped, pre, limit };
        proof {
            codes_same(&s0, &d);
            assert(d.fed() =~= s0.fed() + chunk@);
            assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                d.tgt(f) == lift(d.pre@, d.cont(f)) by {
                assert(is_prefix(b0, f));
                assert(is_prefix(s0.bits(), f));
                assert(d.g() == s0.g());
                cont_same(&d, &s0, f);
            }
        }
        loop
            invariant
                d.inv(), d.inp@ == inp0 + chunk@, b == d.bits(), nbits == 8 * d.inp@.len(),
                inp0 == self.inp@, d.fed() == s0.fed() + chunk@, d.limit == s0.limit,
                d.pre == s0.pre, d.base == s0.base, d.dropped == s0.dropped,
                n_start <= d.n, d.out@.take(n_start as int) == s0.g(), n_start == s0.n,
                sink@ == old(sink)@, s0 == self,
            decreases nbits - d.p, mode_rank(d.mode),
        {
            let ghost dprev = d;
            let tag: u8 = match &d.mode {
                Mode::Header => 0,
                Mode::Stored { .. } => 1,
                Mode::Done { .. } => 2,
                _ => 3,
            };
            let r = if tag == 0 {
                step_header(&mut d)
            } else if tag == 1 {
                step_stored(&mut d)
            } else if tag == 2 {
                let q = match &d.mode { Mode::Done { q } => *q, _ => 0 };
                proof {
                    lemma_same_io_refl(&d);
                    assert forall|f: Seq<bool>| #[trigger] is_prefix(d.bits(), f) implies
                        d.cont(f) == Some((d.g(), q as int, d.st)) by {
                        cont_done(&d, f);
                    }
                }
                Some(Ok(Status::Done { bits: q, zlib: d.st }))
            } else {
                step_syms(&mut d)
            };
            proof {
                assert(d.out@.take(n_start as int) =~= d.out@.take(dprev.n as int).take(n_start as int));
                assert(dprev.g().take(n_start as int) =~= dprev.out@.take(n_start as int));
            }
            match r {
                None => {}
                Some(res) => {
                    proof { assert(s0.whole() =~= d.pre@ + d.out@.take(n_start as int)); }
                    let ghost dd = d;
                    let r = finish_feed(d, res, n_start, sink, Ghost(s0.whole()));
                    proof {
                        let (d2, res2) = r;
                        assert(d2.inv());
                        assert(d2.fed() == self.fed() + chunk@);
                        assert(d2.limit == self.limit);
                        assert(d2.whole().take(self.whole().len() as int) == self.whole());
                        assert(sink@ == old(sink)@ + d2.whole().skip(self.whole().len() as int));
                        assert(global_ok(&d2, res2));
                    }
                    return r;
                }
            }
        }
    }
}

} // verus!
