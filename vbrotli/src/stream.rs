//! The streaming decoder: input in pieces, output as it is decided, in
//! bounded memory. Its verdict after each piece holds for every stream that
//! starts with the input so far.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vbits::bitspec::p2;
use vbits::lsb::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::spec::getbits;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use vdeflate::step::is_prefix;
use crate::spec::*;
use crate::sspec::*;
use crate::moves::*;
use crate::code::*;
use crate::hdr::*;
use crate::cmd::*;
use crate::dec::*;
use crate::br::*;

verus! {

// ---------------------------------------------------------------- bytes

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

// ---------------------------------------------------------------- input

/// The input not yet dropped, `inp`, is the input so far `fed` after its
/// first `din` bytes: its bits at `pin` are the stream's at `8 * din + pin`.
pub proof fn lemma_fed_same(fed: Seq<u8>, din: int, inp: Seq<u8>, f: Seq<bool>, pin: int)
    requires 0 <= din <= fed.len(), fed.skip(din) == inp, is_prefix(lbits(fed), f), 0 <= pin <= 8 * inp.len(),
    ensures same(lbits(inp), pin, f, 8 * din + pin, 8 * inp.len() - pin),
{
    assert forall|j: int| 0 <= j < 8 * inp.len() - pin implies
        #[trigger] lbits(inp)[pin + j] == f[8 * din + pin + j] by {
        let i = pin + j;
        assert((8 * din + i) / 8 == din + i / 8) by (nonlinear_arith) requires i >= 0, din >= 0;
        assert((8 * din + i) % 8 == i % 8) by (nonlinear_arith) requires i >= 0, din >= 0;
        assert(lbits(fed)[8 * din + i] == lbits(inp)[i]);
    }
    assert((8 * din + pin - pin) % 8 == 0) by (nonlinear_arith) requires din >= 0;
}

pub proof fn lemma_same_sym(b1: Seq<bool>, pa: int, b2: Seq<bool>, pb: int, n: int)
    requires same(b1, pa, b2, pb, n),
    ensures same(b2, pb, b1, pa, n),
{
    assert((pa - pb) % 8 == 0) by (nonlinear_arith) requires (pb - pa) % 8 == 0;
    assert forall|j: int| 0 <= j < n implies #[trigger] b2[pb + j] == b1[pa + j] by {
        assert(b1[pa + j] == b2[pb + j]);
    }
}

// ------------------------------------------------------------ the state

/// Where the decoder is, with what it needs there (see `Ph`).
#[derive(Clone, Copy)]
pub enum XPh {
    Start,
    Mb,
    Skip { left: usize, last: bool },
    Raw { left: usize },
    Hdr { end: usize, last: bool },
    Cmd { end: usize, last: bool, bl: XBlk, bi: XBlk, bd: XBlk },
    Lits { end: usize, last: bool, n: u64, bl: XBlk, bd: XBlk, c: u64, clen: u64, n0: usize, p0: usize,
           left0: u64, bi2: XBlk },
    Fill,
    Done { bits: usize },
    Failed { e: Error },
}

/// What a piece of input leaves: a whole stream, or not yet.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Status {
    /// The stream ends here: all its output has been sent, and it took
    /// `bits` bits.
    Done { bits: usize },
    /// Not a whole stream yet.
    NeedMore,
}

pub struct Decoder {
    /// The input not yet dropped, and how many bytes were.
    pub inp: Vec<u8>,
    pub din: usize,
    /// The bit position in `inp`.
    pub pin: usize,
    /// The output: `pre + out.take(n)`, `pre` dropped (`base` bytes).
    pub out: Vec<u8>,
    pub n: usize,
    pub base: usize,
    pub window: u64,
    pub ring: [u64; 4],
    pub google: bool,
    pub limit: usize,
    /// Where the current meta-block started (total bits).
    pub mbp: usize,
    /// How much of the output has been sent.
    pub sent: usize,
    pub ph: XPh,
    pub h: Option<XHdr>,
    pub fed: Ghost<Seq<u8>>,
    pub pre: Ghost<Seq<u8>>,
    pub dict: Ghost<Seq<u8>>,
    pub sh: Ghost<Hdr>,
}

pub open spec fn m_b_of(ph: XPh) -> int {
    match ph { XPh::Cmd { bi, .. } => bi.left as int, XPh::Lits { bi2, .. } => bi2.left as int, _ => 0 }
}

pub open spec fn m_s_of(ph: XPh) -> int {
    match ph { XPh::Skip { .. } | XPh::Raw { .. } | XPh::Hdr { .. } | XPh::Lits { .. } => 1, _ => 0 }
}

pub open spec fn lits_n_of(ph: XPh) -> u64 { match ph { XPh::Lits { n, .. } => n, _ => 0 } }

pub open spec fn big() -> nat { 0x0100_0000_0000_0000 }

/// `a` is below `b` in the step loop's measure (lexicographically).
pub open spec fn below(a: &Decoder, b: &Decoder) -> bool {
    a.m_r() < b.m_r() || (a.m_r() == b.m_r() && (a.m_o() < b.m_o() || (a.m_o() == b.m_o()
        && (a.m_b() < b.m_b() || (a.m_b() == b.m_b() && a.m_s() < b.m_s())))))
}

/// The decoder's promise: for every stream that starts with the input so
/// far, the spec's result is the continuation from here; or, once failed,
/// the failure holds for all of them.
#[verifier::opaque]
pub open spec fn promise(dict: Seq<u8>, fed: Seq<u8>, window: nat, ph: Ph, pos: int, st: St, fail: Option<Error>,
                         limit: nat) -> bool {
    match fail {
        Some(Error::Bad) => forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==> brotli(dict, f) is None,
        Some(Error::TooBig) => forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==>
            (brotli(dict, f) matches Some((o, q, g)) ==> o.len() > limit),
        None => forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==>
            brotli(dict, f) == cont(dict, window, ph, f, pos, st),
    }
}

impl Decoder {
    /// The position in the stream, in bits.
    pub open spec fn pos(&self) -> int { 8 * self.din + self.pin }

    /// All the output so far.
    pub open spec fn whole(&self) -> Seq<u8> { ov(self.pre@, self.out@, self.n as int) }

    pub open spec fn st(&self) -> St { St { out: self.whole(), ring: rseq(self.ring), google: self.google } }

    pub open spec fn xh(&self) -> XHdr { self.h.unwrap() }

    /// The phase, as the spec's.
    pub open spec fn gph(&self) -> Ph { self.gph_with(self.ph) }

    /// Phase `ph`, as the spec's (with the decoder's position and header).
    pub open spec fn gph_with(&self, ph: XPh) -> Ph {
        match ph {
            XPh::Start => Ph::Start,
            XPh::Mb => Ph::Mb,
            XPh::Skip { left, last } => Ph::Skip { q_end: self.pos() + 8 * left, last, mbp: self.mbp as int },
            XPh::Raw { left } => Ph::Raw { q_end: self.pos() + 8 * left, mbp: self.mbp as int },
            XPh::Hdr { end, last } => Ph::Hdr { end: end as nat, last, mbp: self.mbp as int },
            XPh::Cmd { end, last, bl, bi, bd } =>
                Ph::Cmd { h: self.sh@, end: end as nat, last, mbp: self.mbp as int, bl: blk(bl), bi: blk(bi), bd: blk(bd) },
            XPh::Lits { end, last, n, bl, bd, c, clen, n0, p0, left0, bi2 } =>
                Ph::Lits { h: self.sh@, end: end as nat, last, mbp: self.mbp as int, n: n as nat, bl: blk(bl), bd: blk(bd),
                           k: Cmd0 { c: c as nat, clen: clen as nat, n0: n0 as nat, p0: p0 as int, left0: left0 as nat,
                                     bi2: blk(bi2) } },
            XPh::Fill => Ph::Fill,
            XPh::Done { bits } => Ph::Done { bits: bits as nat },
            XPh::Failed { e } => Ph::Start,
        }
    }

    /// What the decoder's input and output are.
    pub open spec fn io_ok(&self) -> bool { self.io_ok_with(self.ph) }

    pub open spec fn io_ok_with(&self, ph: XPh) -> bool {
        &&& dict_ok(self.dict@)
        &&& self.fed@.len() < big() && self.din <= self.fed@.len() && self.fed@.skip(self.din as int) == self.inp@
        &&& self.pin <= 8 * self.inp@.len()
        &&& self.base == self.pre@.len() && self.n <= self.out@.len() && self.whole().len() <= self.limit
        &&& self.limit < big() && self.mbp <= self.pos()
        &&& self.base <= self.sent <= self.whole().len()
        &&& two_ok(self.pre@, self.n as int)
        &&& !(ph is Start) && !(ph is Failed) ==>
                (1008 <= self.window < 0x100_0000 && (self.n >= self.window || self.base == 0) && ring_ok(self.ring))
    }

    /// What each phase needs.
    pub open spec fn ph_ok(&self) -> bool { self.ph_ok_with(self.ph) }

    pub open spec fn ph_ok_with(&self, ph: XPh) -> bool {
        match ph {
            XPh::Start => self.din == 0 && self.pin == 0 && self.n == 0 && self.base == 0
                && self.ring == [4u64, 11, 15, 16] && self.google,
            XPh::Mb => true,
            XPh::Skip { left, last } => self.pin % 8 == 0 && left <= 0x100_0000 && self.mbp < self.pos(),
            XPh::Raw { left } => self.pin % 8 == 0 && left <= 0x100_0000 && self.whole().len() + left <= self.limit
                && self.n + left + 16 <= self.out@.len() && self.mbp < self.pos(),
            XPh::Hdr { end, last } => self.whole().len() < end <= self.limit && end - self.base + 16 <= self.out@.len()
                && self.mbp < self.pos(),
            XPh::Cmd { end, last, bl, bi, bd } =>
                self.h is Some && xhdr_wf(&self.xh(), self.sh@) && blk_ok(bl, &self.xh().cl) && blk_ok(bi, &self.xh().ci)
                && blk_ok(bd, &self.xh().cd) && self.whole().len() < end <= self.limit && end - self.base + 16 <= self.out@.len()
                && self.mbp < self.pos(),
            XPh::Lits { end, last, n, bl, bd, c, clen, n0, p0, left0, bi2 } =>
                self.h is Some && xhdr_wf(&self.xh(), self.sh@) && blk_ok(bl, &self.xh().cl) && blk_ok(bi2, &self.xh().ci)
                && blk_ok(bd, &self.xh().cd) && self.whole().len() + n <= end <= self.limit
                && end - self.base + 16 <= self.out@.len() && 2 <= clen < 0x200_0000 && self.mbp < self.pos()
                && n0 <= self.whole().len() && p0 <= self.pos(),
            XPh::Fill => true,
            XPh::Done { bits } => true,
            XPh::Failed { e } => true,
        }
    }

    /// How the decoder failed, if it did.
    pub open spec fn gfail(&self) -> Option<Error> { self.gfail_with(self.ph) }

    pub open spec fn gfail_with(&self, ph: XPh) -> Option<Error> {
        match ph { XPh::Failed { e } => Some(e), _ => None }
    }

    /// The decoder's promise (see `promise`).
    pub open spec fn tgt_ok(&self) -> bool { self.tgt_ok_with(self.ph) }

    pub open spec fn tgt_ok_with(&self, ph: XPh) -> bool {
        promise(self.dict@, self.fed@, self.window as nat, self.gph_with(ph), self.pos(), self.st(), self.gfail_with(ph),
                self.limit as nat)
    }

    pub open spec fn inv(&self) -> bool { self.inv_with(self.ph) }

    /// The invariant with the phase `ph` (the command runs keep the phase
    /// in a local and store it once).
    pub open spec fn inv_with(&self, ph: XPh) -> bool { self.io_ok_with(ph) && self.ph_ok_with(ph) && self.tgt_ok_with(ph) }

    /// The measure the step loop decreases: input bits left, room left
    /// under the limit, the command block's count, and a phase rank.
    pub open spec fn m_r(&self) -> int { 8 * self.inp@.len() - self.pin }
    pub open spec fn m_o(&self) -> int { self.limit - self.whole().len() }
    pub open spec fn m_b(&self) -> int { m_b_of(self.ph) }
    pub open spec fn m_s(&self) -> int { m_s_of(self.ph) }

    /// A decoder for a stream whose output may be at most `limit` bytes.
    pub fn new(dict: &[u8], limit: usize) -> (d: Decoder)
        requires dict_ok(dict@),
        ensures d.inv(), d.fed@ == Seq::<u8>::empty(), d.whole() == Seq::<u8>::empty(), d.dict@ == dict@,
            d.limit == if limit < 0x0100_0000_0000_0000 { limit } else { 0x00ff_ffff_ffff_ffff },
    {
        let lim = if limit < 0x0100_0000_0000_0000 { limit } else { 0x00ff_ffff_ffff_ffff };
        let d = Decoder {
            inp: Vec::new(), din: 0, pin: 0, out: Vec::new(), n: 0, base: 0, window: 0, ring: [4, 11, 15, 16],
            google: true, limit: lim, mbp: 0, sent: 0, ph: XPh::Start, h: None,
            fed: Ghost(Seq::empty()), pre: Ghost(Seq::empty()), dict: Ghost(dict@),
            sh: Ghost(arbitrary()),
        };
        proof {
            reveal(promise);
            assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(d.fed@), f) implies
                brotli(d.dict@, f) == cont(d.dict@, d.window as nat, d.gph(), f, d.pos(), d.st()) by {
                lemma_cont_start(d.dict@, d.window as nat, f, d.pos(), d.st());
            }
            assert(d.whole() =~= Seq::<u8>::empty());
            assert(Seq::<u8>::empty().skip(0) =~= Seq::<u8>::empty());
            assert(d.inp@ =~= Seq::<u8>::empty());
        }
        d
    }
}

/// What a step leaves: progress (and the decoder may go on), more input
/// needed, or the end (done, or an error).
pub enum StepR {
    Go,
    More,
    Stop,
}

// ------------------------------------------------------------- WBITS

pub proof fn lemma_wbits_mv(b1: Seq<bool>, b2: Seq<bool>, nn: int)
    requires wbits(b1) matches Some((w, q)) && q <= nn, same(b1, 0, b2, 0, nn),
    ensures wbits(b2) == wbits(b1),
{
    lemma_getbits_mv(b1, 0, b2, 0, nn, 1);
    if getbits(b1, 0, 1).unwrap() != 0 {
        lemma_same_sub(b1, 0, b2, 0, nn, 1, nn - 1);
        lemma_getbits_mv(b1, 1, b2, 1, nn - 1, 3);
        if getbits(b1, 1, 3).unwrap() == 0 {
            lemma_same_sub(b1, 0, b2, 0, nn, 4, nn - 4);
            lemma_getbits_mv(b1, 4, b2, 4, nn - 4, 3);
        }
    }
}

pub proof fn lemma_wbits_pos(b: Seq<bool>)
    ensures wbits(b) matches Some((w, q)) ==> 1 <= q <= 7 && q <= b.len() && 10 <= w <= 24,
{
    if let Some(x) = getbits(b, 0, 1) {
        if x != 0 {
            if let Some(n) = getbits(b, 1, 3) {
                lemma_getbits_bound_(b, 1, 3);
                assert(p2(3) == 8) by { reveal_with_fuel(p2, 4); }
                if n == 0 {
                    if let Some(m) = getbits(b, 4, 3) { lemma_getbits_bound_(b, 4, 3); }
                }
            }
        }
    }
}

/// What WBITS read from the input says about every stream that extends it.
pub proof fn lemma_start(dict: Seq<u8>, fed: Seq<u8>, window: nat)
    requires wbits(lbits(fed)) matches Some((w, p)) && window == (p2(w) - 16) as nat,
    ensures forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==>
        brotli(dict, f) == cont(dict, window, Ph::Mb, f, wbits(lbits(fed)).unwrap().1,
                                St { out: Seq::empty(), ring: seq![4int, 11, 15, 16], google: true }),
{
    hide(metablocks);
    hide(cont);
    let b = lbits(fed);
    lemma_wbits_pos(b);
    assert(fed.skip(0) =~= fed);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        brotli(dict, f) == cont(dict, window, Ph::Mb, f, wbits(lbits(fed)).unwrap().1,
                                St { out: Seq::empty(), ring: seq![4int, 11, 15, 16], google: true }) by {
        lemma_fed_same(fed, 0, fed, f, 0);
        lemma_wbits_mv(b, f, (8 * fed.len()) as int);
        lemma_cont_mb(dict, window, f, wbits(lbits(fed)).unwrap().1,
                      St { out: Seq::empty(), ring: seq![4int, 11, 15, 16], google: true });
    }
}

/// No stream extending the input has WBITS, once the input has a byte.
pub proof fn lemma_start_bad(dict: Seq<u8>, fed: Seq<u8>)
    requires wbits(lbits(fed)) is None, fed.len() >= 1,
    ensures forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==> brotli(dict, f) is None,
{
    hide(metablocks);
    let b = lbits(fed);
    assert(fed.skip(0) =~= fed);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies brotli(dict, f) is None by {
        lemma_wbits_pos(f);
        if let Some((w, q)) = wbits(f) {
            lemma_fed_same(fed, 0, fed, f, 0);
            lemma_same_sym(b, 0, f, 0, (8 * fed.len()) as int);
            lemma_same_sub(f, 0, b, 0, (8 * fed.len()) as int, 0, q);
            lemma_wbits_mv(f, b, q);
        }
    }
}

impl Decoder {
    /// Before WBITS.
    #[verifier::spinoff_prover]
    pub fn step_start(&mut self) -> (r: StepR)
        requires old(self).inv(), old(self).ph is Start,
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, final(self).whole() == old(self).whole(),
            r is More ==> final(self).ph is Start,
            r is Stop ==> final(self).ph is Failed,
            r is Go ==> final(self).ph is Mb,
            final(self).inp == old(self).inp, final(self).sent == old(self).sent,
            r is Go ==> below(final(self), old(self)),
    {
        hide(brotli);
        hide(cont);
        let ghost fed = self.fed@;
        proof { assert(fed.skip(0) =~= fed); assert(self.inp@ == fed); }
        match wbits_x(&self.inp) {
            Some((w, p)) => {
                proof { lemma_wbits_pos(lbits(fed)); }
                let window = window_x(w);
                proof {
                    reveal(promise);
                    lemma_start(self.dict@, fed, window as nat);
                    assert(p2(10) == 1024) by { reveal_with_fuel(p2, 11); }
                    vbits::prim_read::lemma_p2_mono(10, w as nat);
                }
                self.window = window;
                self.pin = p;
                self.mbp = p;
                self.ph = XPh::Mb;
                proof {
                    assert(rseq(self.ring) =~= seq![4int, 11, 15, 16]);
                    assert(ring_ok(self.ring)) by {
                        assert forall|i: int| 0 <= i < 4 implies 1 <= #[trigger] self.ring[i] < 0x100_0000 by {
                            assert(self.ring[i] == [4u64, 11, 15, 16][i]);
                        }
                    }
                    assert(self.whole() =~= Seq::<u8>::empty());
                    assert(self.st() == St { out: Seq::<u8>::empty(), ring: seq![4int, 11, 15, 16], google: true });
                    assert(self.gph() == Ph::Mb);
                    assert(self.pos() == p);
                }
                StepR::Go
            }
            None => {
                if self.inp.len() >= 1 {
                    proof { reveal(promise); lemma_start_bad(self.dict@, fed); }
                    self.ph = XPh::Failed { e: Error::Bad };
                    StepR::Stop
                } else {
                    StepR::More
                }
            }
        }
    }
}

// ------------------------------------------------ a meta-block's header

/// Make the buffer `need` long (exactly, if it grows), keeping its first
/// `n` bytes.
pub fn room(out: &mut Vec<u8>, n: usize, need: usize)
    requires n <= old(out)@.len(),
    ensures
        final(out)@.len() >= need, final(out)@.len() >= old(out)@.len(),
        final(out)@.take(n as int) == old(out)@.take(n as int),
{
    if out.len() < need {
        let ghost o = out@;
        if out.len() == 0 {
            // a first buffer from the allocator's zeroed memory
            *out = vec![0u8; need];
        } else {
            out.resize(need, 0);
        }
        proof { assert(out@.take(n as int) =~= o.take(n as int)); }
    }
}

pub enum XMh {
    LastEmpty,
    Meta { a: usize, n: u64, last: bool },
    Raw { a: usize, mlen: u64 },
    Comp { r: usize, mlen: u64, last: bool },
}

pub open spec fn xmh(m: XMh) -> Mh {
    match m {
        XMh::LastEmpty => Mh::LastEmpty,
        XMh::Meta { a, n, last } => Mh::Meta { a: a as int, n: n as nat, last },
        XMh::Raw { a, mlen } => Mh::Raw { a: a as int, mlen: mlen as nat },
        XMh::Comp { r, mlen, last } => Mh::Comp { r: r as int, mlen: mlen as nat, last },
    }
}

#[verifier::spinoff_prover]
pub fn meta_head_x(buf: &[u8], pm: usize, last: bool) -> (r: Option<XMh>)
    requires buf_ok(buf@), pm <= 8 * buf.len(),
    ensures
        match r {
            Some(m) => mb_meta(lbits(buf@), pm as int, last) == Some(xmh(m)),
            None => mb_meta(lbits(buf@), pm as int, last) is None,
        },
{
    proof { reveal_with_fuel(p2, 3); }
    let reserved = match getbits_x(buf, pm, 1) { None => return None, Some(x) => x };
    let nbytes = match getbits_x(buf, pm + 1, 2) { None => return None, Some(x) => x };
    let n: u64 = if nbytes == 0 {
        0
    } else {
        let v = match getbits_x(buf, pm + 3, 8 * nbytes) { None => return None, Some(x) => x };
        proof {
            vbits::prim_read::lemma_p2_eq_pow2((8 * (nbytes - 1)) as nat);
            vstd::bits::lemma_u64_pow2_no_overflow((8 * (nbytes - 1)) as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, (8 * (nbytes - 1)) as u64);
            vbits::prim_read::lemma_p2_mono((8 * nbytes) as nat, 24);
            assert(p2(24) == 0x100_0000) by { reveal_with_fuel(p2, 25); }
        }
        if nbytes > 1 && v / (1u64 << (8 * (nbytes - 1))) == 0 {
            return None;
        }
        v + 1
    };
    let r = pm + 3 + 8 * nbytes as usize;
    if reserved != 0 || r > 8 * buf.len() || !zero_fill_x(buf, r) {
        return None;
    }
    Some(XMh::Meta { a: align8_x(r), n, last })
}

pub fn data_head_x(buf: &[u8], q: usize, m: u64, last: bool) -> (r: Option<XMh>)
    requires buf_ok(buf@), q + 2 <= 8 * buf.len(), m < 3,
    ensures
        match r {
            Some(x) => mb_data(lbits(buf@), q as int, m as nat, last) == Some(xmh(x)),
            None => mb_data(lbits(buf@), q as int, m as nat, last) is None,
        },
{
    let nib = m + 4;
    let mlen = match read_mlen_x(buf, q + 2, nib) { None => return None, Some(x) => x };
    let pd = q + 2 + 4 * nib as usize;
    if last {
        return Some(XMh::Comp { r: pd, mlen, last: true });
    }
    let u = match getbits_x(buf, pd, 1) { None => return None, Some(x) => x };
    let r = pd + 1;
    if u == 1 {
        if !zero_fill_x(buf, r) {
            return None;
        }
        Some(XMh::Raw { a: align8_x(r), mlen })
    } else {
        Some(XMh::Comp { r, mlen, last: false })
    }
}

pub fn mb_head_x(buf: &[u8], p: usize) -> (r: Option<XMh>)
    requires buf_ok(buf@), p <= 8 * buf.len(),
    ensures
        match r {
            Some(m) => mb_head(lbits(buf@), p as int) == Some(xmh(m)),
            None => mb_head(lbits(buf@), p as int) is None,
        },
{
    hide(mb_meta);
    hide(mb_data);
    proof { reveal_with_fuel(p2, 3); }
    let islast = match getbits_x(buf, p, 1) { None => return None, Some(x) => x };
    let e = if islast == 1 { match getbits_x(buf, p + 1, 1) { None => return None, Some(x) => x } } else { 0 };
    if e == 1 {
        return Some(XMh::LastEmpty);
    }
    let last = islast == 1;
    let q = if last { p + 2 } else { p + 1 };
    let m = match getbits_x(buf, q, 2) { None => return None, Some(x) => x };
    if m == 3 { meta_head_x(buf, q + 2, last) } else { data_head_x(buf, q, m, last) }
}

/// A header read from the input is every extension's header.
pub proof fn lemma_mb_step(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St, m: Mh)
    requires 0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin <= 8 * inp.len(),
        mb_head(lbits(inp), pin) == Some(m),
    ensures
        forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==>
            cont(dict, window, Ph::Mb, f, 8 * din + pin, st) == mb_next(dict, window, f, 8 * din + pin, st, mh_mv(m, 8 * din)),
        forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==> (m is Raw || m is Comp) ==>
            (cont(dict, window, Ph::Mb, f, 8 * din + pin, st) matches Some((o, q, g)) ==>
                o.len() >= st.out.len() + match m { Mh::Raw { a, mlen } => mlen, Mh::Comp { r, mlen, last } => mlen, _ => 0nat }),
        mh_end(m, pin) <= pin + 40, mh_end(m, pin) <= 8 * inp.len(),
{
    hide(cont); hide(mb_next); hide(mb_head);
    let b = lbits(inp);
    lemma_mb_head_pos(b, pin);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Mb, f, 8 * din + pin, st) == mb_next(dict, window, f, 8 * din + pin, st, mh_mv(m, 8 * din))
        && ((m is Raw || m is Comp) ==>
            (cont(dict, window, Ph::Mb, f, 8 * din + pin, st) matches Some((o, q, g)) ==>
                o.len() >= st.out.len() + match m { Mh::Raw { a, mlen } => mlen, Mh::Comp { r, mlen, last } => mlen, _ => 0nat })) by {
        lemma_fed_same(fed, din, inp, f, pin);
        lemma_mb_head_mv(b, pin, f, 8 * din + pin, 8 * inp.len() - pin);
        assert(mh_mv(m, (8 * din + pin) - pin) == mh_mv(m, 8 * din));
        lemma_mb_next(dict, window, f, 8 * din + pin, st);
        if m is Raw || m is Comp {
            lemma_mb_grows(dict, window, f, 8 * din + pin, st);
        }
    }
}

/// With 40 bits in hand, a header that fails fails on every extension.
pub proof fn lemma_mb_step_bad(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St)
    requires 0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin, pin + 40 <= 8 * inp.len(),
        mb_head(lbits(inp), pin) is None,
    ensures forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==> cont(dict, window, Ph::Mb, f, 8 * din + pin, st) is None,
{
    hide(cont); hide(mb_head);
    let b = lbits(inp);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Mb, f, 8 * din + pin, st) is None by {
        lemma_fed_same(fed, din, inp, f, pin);
        lemma_mb_head_pos(f, 8 * din + pin);
        if mb_head(f, 8 * din + pin) is Some {
            lemma_same_sym(b, pin, f, 8 * din + pin, 8 * inp.len() - pin);
            lemma_mb_head_mv(f, 8 * din + pin, b, pin, 8 * inp.len() - pin);
        } else {
            lemma_mb_bad(dict, window, f, 8 * din + pin, st);
        }
    }
}

/// The promise carries over to a phase whose continuation is the same on
/// every extension.
pub proof fn lemma_promise_step(dict: Seq<u8>, fed: Seq<u8>, window: nat, ph1: Ph, pos1: int, st1: St,
                                ph2: Ph, pos2: int, st2: St, limit: nat)
    requires promise(dict, fed, window, ph1, pos1, st1, None, limit),
        forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==>
            cont(dict, window, ph1, f, pos1, st1) == cont(dict, window, ph2, f, pos2, st2),
    ensures promise(dict, fed, window, ph2, pos2, st2, None, limit),
{
    reveal(promise);
}

pub proof fn lemma_promise_bad(dict: Seq<u8>, fed: Seq<u8>, window: nat, ph1: Ph, pos1: int, st1: St,
                               ph2: Ph, pos2: int, st2: St, limit: nat)
    requires promise(dict, fed, window, ph1, pos1, st1, None, limit),
        forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==> cont(dict, window, ph1, f, pos1, st1) is None,
    ensures promise(dict, fed, window, ph2, pos2, st2, Some(Error::Bad), limit),
{
    reveal(promise);
}

pub proof fn lemma_promise_toobig(dict: Seq<u8>, fed: Seq<u8>, window: nat, ph1: Ph, pos1: int, st1: St,
                                  ph2: Ph, pos2: int, st2: St, limit: nat)
    requires promise(dict, fed, window, ph1, pos1, st1, None, limit),
        forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==>
            (cont(dict, window, ph1, f, pos1, st1) matches Some((o, q, g)) ==> o.len() > limit),
    ensures promise(dict, fed, window, ph2, pos2, st2, Some(Error::TooBig), limit),
{
    reveal(promise);
}

/// A meta-block's header read from the input: the promise at the phase
/// after it, or a result too long.
pub proof fn lemma_mb_advance(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St,
                              m: Mh, limit: nat, pos_f: int)
    requires promise(dict, fed, window, Ph::Mb, 8 * din + pin, st, None, limit),
        0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin <= 8 * inp.len(),
        mb_head(lbits(inp), pin) == Some(m),
    ensures
        promise(dict, fed, window, mh_ph(mh_mv(m, 8 * din), 8 * din + pin, st).0,
                mh_ph(mh_mv(m, 8 * din), 8 * din + pin, st).1, st, None, limit),
        (m is Raw || m is Comp) && st.out.len() + (match m { Mh::Raw { a, mlen } => mlen, Mh::Comp { r, mlen, last } => mlen,
            _ => 0nat }) > limit ==> promise(dict, fed, window, Ph::Start, pos_f, st, Some(Error::TooBig), limit),
        mh_end(m, pin) <= pin + 40, mh_end(m, pin) <= 8 * inp.len(),
{
    hide(cont); hide(mb_next); hide(mh_ph);
    lemma_mb_step(dict, window, fed, din, inp, pin, st, m);
    let p = 8 * din + pin;
    let m2 = mh_mv(m, 8 * din);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Mb, f, p, st) == cont(dict, window, mh_ph(m2, p, st).0, f, mh_ph(m2, p, st).1, st) by {
        lemma_mb_next_ph(dict, window, f, p, st, m2);
    }
    lemma_promise_step(dict, fed, window, Ph::Mb, p, st, mh_ph(m2, p, st).0, mh_ph(m2, p, st).1, st, limit);
    if (m is Raw || m is Comp) && st.out.len() + (match m { Mh::Raw { a, mlen } => mlen, Mh::Comp { r, mlen, last } => mlen,
            _ => 0nat }) > limit {
        lemma_promise_toobig(dict, fed, window, Ph::Mb, p, st, Ph::Start, pos_f, st, limit);
    }
}

impl Decoder {
    /// Send the output not sent yet to `sink`, and, if the buffer holds more
    /// than two windows of output, drop all but the last window of it.
    #[verifier::spinoff_prover]
    pub fn flush(&mut self, sink: &mut Vec<u8>)
        requires old(self).inv(), !(old(self).ph is Start), !(old(self).ph is Failed),
            old(self).ph is Mb || old(self).ph is Fill || old(self).ph is Done || old(self).ph is Skip,
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, final(self).whole() == old(self).whole(),
            final(self).sent == final(self).whole().len(),
            final(sink)@ == old(sink)@ + old(self).whole().skip(old(self).sent as int),
            final(self).ph == old(self).ph, final(self).pos() == old(self).pos(),
            final(self).window == old(self).window, final(self).st() == old(self).st(),
            final(self).mbp == old(self).mbp, final(self).inp == old(self).inp,
            final(self).out@.len() <= old(self).out@.len(),
            final(self).n <= 2 * old(self).window || final(self).n == old(self).n,
    {
        let ghost w0 = self.whole();
        let ghost s0 = sink@;
        let from = self.sent - self.base;
        append(sink, vstd::slice::slice_subrange(self.out.as_slice(), from, self.n));
        proof {
            assert(self.out@.subrange(from as int, self.n as int) =~= w0.skip(self.sent as int));
        }
        self.sent = self.base + self.n;
        let keep = self.window as usize;
        if self.n > 2 * keep {
            let drop = self.n - keep;
            let ghost o = self.out@;
            self.out.as_mut_slice().copy_within(drop..self.n, 0);
            proof {
                assert(self.out@.take(keep as int) =~= o.subrange(drop as int, self.n as int));
            }
            self.pre = Ghost(self.pre@ + o.take(drop as int));
            self.base = self.base + drop;
            self.n = keep;
            proof {
                assert(self.whole() =~= w0);
            }
        }
    }

    /// At a meta-block's start: its header.
    #[verifier::spinoff_prover]
    pub fn step_mb(&mut self) -> (r: StepR)
        requires old(self).inv(), old(self).ph is Mb,
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, final(self).whole() == old(self).whole(),
            final(self).sent == old(self).sent,
            r is More ==> final(self).ph is Mb,
            r is Stop ==> final(self).ph is Failed,
            final(self).inp == old(self).inp,
            r is Go ==> below(final(self), old(self)),
    {
        hide(cont); hide(mb_head); hide(mh_ph);
        let ghost fed = self.fed@;
        let ghost st = self.st();
        let ghost din = self.din as int;
        let ghost d = self.dict@;
        let ghost w = self.window as nat;
        let ghost lim = self.limit as nat;
        match mb_head_x(&self.inp, self.pin) {
            None => {
                if 8 * self.inp.len() - self.pin >= 40 {
                    proof {
                        lemma_mb_step_bad(d, w, fed, din, self.inp@, self.pin as int, st);
                        lemma_promise_bad(d, fed, w, Ph::Mb, self.pos(), st, Ph::Start, self.pos(), st, lim);
                    }
                    self.ph = XPh::Failed { e: Error::Bad };
                    StepR::Stop
                } else {
                    StepR::More
                }
            }
            Some(m) => {
                proof {
                    lemma_mb_advance(d, w, fed, din, self.inp@, self.pin as int, st, xmh(m), lim, self.pos());
                    lemma_mb_head_pos(lbits(self.inp@), self.pin as int);
                }
                let mbp = 8 * self.din + self.pin;
                proof { reveal(mh_ph); }
                match m {
                    XMh::LastEmpty => {
                        self.pin = self.pin + 2;
                        self.mbp = mbp;
                        self.ph = XPh::Fill;
                        StepR::Go
                    }
                    XMh::Meta { a, n, last } => {
                        self.pin = a;
                        self.mbp = mbp;
                        self.ph = XPh::Skip { left: n as usize, last };
                        StepR::Go
                    }
                    XMh::Raw { a, mlen } => {
                        if mlen as usize > self.limit - (self.base + self.n) {
                            self.ph = XPh::Failed { e: Error::TooBig };
                            return StepR::Stop;
                        }
                        room(&mut self.out, self.n, self.n + mlen as usize + 16);
                        self.pin = a;
                        self.mbp = mbp;
                        self.ph = XPh::Raw { left: mlen as usize };
                        StepR::Go
                    }
                    XMh::Comp { r, mlen, last } => {
                        if mlen as usize > self.limit - (self.base + self.n) {
                            self.ph = XPh::Failed { e: Error::TooBig };
                            return StepR::Stop;
                        }
                        room(&mut self.out, self.n, self.n + mlen as usize + 16);
                        self.pin = r;
                        self.mbp = mbp;
                        self.ph = XPh::Hdr { end: self.base + self.n + mlen as usize, last };
                        StepR::Go
                    }
                }
            }
        }
    }
}

// -------------------------------------------- metadata, raw bytes, fill

/// A position within the input so far is within every extension.
pub proof fn lemma_pos_in(fed: Seq<u8>, f: Seq<bool>, q: int)
    requires is_prefix(lbits(fed), f), q <= 8 * fed.len(),
    ensures q <= f.len(),
{
}

pub proof fn lemma_skip_on(dict: Seq<u8>, window: nat, fed: Seq<u8>, st: St, q_end: int, last: bool, mbp: int,
                           p1: int, p2: int, limit: nat)
    requires promise(dict, fed, window, Ph::Skip { q_end, last, mbp }, p1, st, None, limit),
    ensures promise(dict, fed, window, Ph::Skip { q_end, last, mbp }, p2, st, None, limit),
{
    hide(cont); hide(mb_rest);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Skip { q_end, last, mbp }, f, p1, st) == cont(dict, window, Ph::Skip { q_end, last, mbp }, f, p2, st) by {
        lemma_cont_skip(dict, window, f, p1, st, q_end, last, mbp);
        lemma_cont_skip(dict, window, f, p2, st, q_end, last, mbp);
    }
    lemma_promise_step(dict, fed, window, Ph::Skip { q_end, last, mbp }, p1, st, Ph::Skip { q_end, last, mbp }, p2, st, limit);
}

/// A meta-block that ends at the byte boundary `q`: the next one, or, if it
/// was the last, the stream's end.
pub proof fn lemma_mb_end(dict: Seq<u8>, window: nat, fed: Seq<u8>, st: St, q: int, last: bool, mbp: int, f: Seq<bool>)
    requires is_prefix(lbits(fed), f), q % 8 == 0, 0 <= q <= 8 * fed.len(), mbp < q,
    ensures fin(mb_rest(dict, window, f, mbp, q, st, last))
        == (if last { cont(dict, window, Ph::Done { bits: q as nat }, f, q, st) } else { cont(dict, window, Ph::Mb, f, q, st) }),
{
    hide(cont); hide(metablocks);
    lemma_pos_in(fed, f, q);
    lemma_cont_done(dict, window, f, q, st, q as nat);
    lemma_cont_mb(dict, window, f, q, st);
    assert(align8(q) == q);
    assert(f.subrange(q, q) =~= Seq::<bool>::empty());
}

pub proof fn lemma_skip_end(dict: Seq<u8>, window: nat, fed: Seq<u8>, st: St, q: int, last: bool, mbp: int, limit: nat)
    requires promise(dict, fed, window, Ph::Skip { q_end: q, last, mbp }, q, st, None, limit),
        q % 8 == 0, 0 <= q <= 8 * fed.len(), mbp < q,
    ensures promise(dict, fed, window, if last { Ph::Done { bits: q as nat } } else { Ph::Mb }, q, st, None, limit),
{
    hide(cont); hide(mb_rest);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Skip { q_end: q, last, mbp }, f, q, st)
        == cont(dict, window, if last { Ph::Done { bits: q as nat } } else { Ph::Mb }, f, q, st) by {
        lemma_cont_skip(dict, window, f, q, st, q, last, mbp);
        lemma_pos_in(fed, f, q);
        lemma_mb_end(dict, window, fed, st, q, last, mbp, f);
    }
    lemma_promise_step(dict, fed, window, Ph::Skip { q_end: q, last, mbp }, q, st,
                       if last { Ph::Done { bits: q as nat } } else { Ph::Mb }, q, st, limit);
}

/// Copying `t` raw bytes from the input.
pub proof fn lemma_raw_copy(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St,
                            q_end: int, mbp: int, t: nat, limit: nat)
    requires promise(dict, fed, window, Ph::Raw { q_end, mbp }, 8 * din + pin, st, None, limit),
        0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin, pin + 8 * t <= 8 * inp.len(), pin % 8 == 0,
        8 * din + pin + 8 * t <= q_end, (q_end - (8 * din + pin)) % 8 == 0,
    ensures promise(dict, fed, window, Ph::Raw { q_end, mbp }, 8 * din + pin + 8 * t,
                    St { out: st.out + bytes_at(lbits(inp), pin, t), ring: st.ring, google: st.google }, None, limit),
{
    hide(cont); hide(mb_rest);
    let p = 8 * din + pin;
    let s2 = St { out: st.out + bytes_at(lbits(inp), pin, t), ring: st.ring, google: st.google };
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Raw { q_end, mbp }, f, p, st) == cont(dict, window, Ph::Raw { q_end, mbp }, f, p + 8 * t, s2) by {
        lemma_cont_raw(dict, window, f, p, st, q_end, mbp);
        lemma_cont_raw(dict, window, f, p + 8 * t, s2, q_end, mbp);
        lemma_fed_same(fed, din, inp, f, pin);
        lemma_same_sub(lbits(inp), pin, f, p, 8 * inp.len() - pin, 0, (8 * t) as int);
        lemma_bytes_at_mv(lbits(inp), pin, f, p, (8 * t) as int, t);
        let left = ((q_end - p) / 8) as nat;
        assert(left >= t);
        lemma_bytes_split(f, p, t, (left - t) as nat);
        assert(((q_end - (p + 8 * t)) / 8) as nat == (left - t) as nat);
        assert(st.out + bytes_at(f, p, left) =~= s2.out + bytes_at(f, p + 8 * t, (left - t) as nat));
    }
    lemma_promise_step(dict, fed, window, Ph::Raw { q_end, mbp }, p, st, Ph::Raw { q_end, mbp }, p + 8 * t, s2, limit);
}

pub proof fn lemma_raw_end(dict: Seq<u8>, window: nat, fed: Seq<u8>, st: St, q: int, mbp: int, limit: nat)
    requires promise(dict, fed, window, Ph::Raw { q_end: q, mbp }, q, st, None, limit),
        q % 8 == 0, 0 <= q <= 8 * fed.len(), mbp < q,
    ensures promise(dict, fed, window, Ph::Mb, q, st, None, limit),
{
    hide(cont); hide(mb_rest);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Raw { q_end: q, mbp }, f, q, st) == cont(dict, window, Ph::Mb, f, q, st) by {
        lemma_cont_raw(dict, window, f, q, st, q, mbp);
        assert(st.out + bytes_at(f, q, 0) =~= st.out);
        assert(St { out: st.out + bytes_at(f, q, ((q - q) / 8) as nat), ring: st.ring, google: st.google } == st);
        lemma_mb_end(dict, window, fed, st, q, false, mbp, f);
    }
    lemma_promise_step(dict, fed, window, Ph::Raw { q_end: q, mbp }, q, st, Ph::Mb, q, st, limit);
}

/// The fill bits after the last meta-block, read from the input.
pub proof fn lemma_fill(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St, limit: nat)
    requires promise(dict, fed, window, Ph::Fill, 8 * din + pin, st, None, limit),
        0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin <= 8 * inp.len(),
    ensures
        zero_fill(lbits(inp), pin) ==>
            promise(dict, fed, window, Ph::Done { bits: (8 * din + align8(pin)) as nat }, 8 * din + pin, st, None, limit),
        !zero_fill(lbits(inp), pin) ==>
            promise(dict, fed, window, Ph::Start, 8 * din + pin, st, Some(Error::Bad), limit),
{
    hide(cont);
    let p = 8 * din + pin;
    assert(align8(pin) <= 8 * inp.len()) by {
        assert((8 * inp.len()) % 8 == 0) by (nonlinear_arith);
    }
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Fill, f, p, st) == (if zero_fill(lbits(inp), pin) {
            cont(dict, window, Ph::Done { bits: (8 * din + align8(pin)) as nat }, f, p, st) } else { None }) by {
        lemma_cont_fill(dict, window, f, p, st);
        lemma_cont_done(dict, window, f, p, st, (8 * din + align8(pin)) as nat);
        lemma_fed_same(fed, din, inp, f, pin);
        lemma_zero_fill_mv(lbits(inp), pin, f, p, 8 * inp.len() - pin);
    }
    if zero_fill(lbits(inp), pin) {
        lemma_promise_step(dict, fed, window, Ph::Fill, p, st, Ph::Done { bits: (8 * din + align8(pin)) as nat }, p, st, limit);
    } else {
        lemma_promise_bad(dict, fed, window, Ph::Fill, p, st, Ph::Start, p, st, limit);
    }
}

impl Decoder {
    /// Skipping metadata.
    #[verifier::spinoff_prover]
    pub fn step_skip(&mut self) -> (r: StepR)
        requires old(self).inv(), old(self).ph is Skip,
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, final(self).whole() == old(self).whole(),
            final(self).sent == old(self).sent, final(self).inp == old(self).inp,
            !(r is Stop), r is Go ==> below(final(self), old(self)),
            r is More ==> final(self).ph is Skip,
    {
        let (left, last) = match self.ph { XPh::Skip { left, last } => (left, last), _ => { assert(false); (0, false) } };
        let ghost q_end = self.pos() + 8 * left;
        let avail = (8 * self.inp.len() - self.pin) / 8;
        let t = if left < avail { left } else { avail };
        if t == 0 && left > 0 {
            return StepR::More;
        }
        let ghost p1 = self.pos();
        self.pin = self.pin + 8 * t;
        let left2 = left - t;
        if left2 > 0 {
            self.ph = XPh::Skip { left: left2, last };
            proof { lemma_skip_on(self.dict@, self.window as nat, self.fed@, self.st(), q_end, last, self.mbp as int,
                                  p1, self.pos(), self.limit as nat); }
            return StepR::Go;
        }
        let q = 8 * self.din + self.pin;
        proof {
            lemma_skip_on(self.dict@, self.window as nat, self.fed@, self.st(), q_end, last, self.mbp as int,
                          p1, self.pos(), self.limit as nat);
            assert((8 * self.din + self.pin) % 8 == 0) by (nonlinear_arith) requires self.pin % 8 == 0;
            assert(self.pos() <= 8 * self.fed@.len());
            lemma_skip_end(self.dict@, self.window as nat, self.fed@, self.st(), q as int, last, self.mbp as int,
                           self.limit as nat);
        }
        if last {
            self.ph = XPh::Done { bits: q };
        } else {
            self.ph = XPh::Mb;
        }
        StepR::Go
    }

    /// Copying uncompressed data.
    #[verifier::spinoff_prover]
    pub fn step_raw(&mut self) -> (r: StepR)
        requires old(self).inv(), old(self).ph is Raw,
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, ext(old(self).whole(), final(self).whole()),
            final(self).sent == old(self).sent, final(self).inp == old(self).inp,
            !(r is Stop), r is Go ==> below(final(self), old(self)),
            r is More ==> final(self).ph is Raw && final(self).whole() == old(self).whole(),
    {
        let left = match self.ph { XPh::Raw { left } => left, _ => { assert(false); 0 } };
        let ghost q_end = self.pos() + 8 * left;
        let ghost w0 = self.whole();
        let avail = (8 * self.inp.len() - self.pin) / 8;
        let t = if left < avail { left } else { avail };
        if t == 0 && left > 0 {
            proof { assert(w0.take(w0.len() as int) =~= w0); }
            return StepR::More;
        }
        let ghost st0 = self.st();
        let ghost p1 = self.pin as int;
        let ghost o0 = self.out@;
        bytes_at_x(&self.inp, self.pin, t, &mut self.out, self.n);
        proof {
            lemma_raw_copy(self.dict@, self.window as nat, self.fed@, self.din as int, self.inp@, p1, st0, q_end,
                           self.mbp as int, t as nat, self.limit as nat);
            assert(ov(self.pre@, self.out@, (self.n + t) as int) == w0 + bytes_at(lbits(self.inp@), p1, t as nat));
            lemma_ext_append(w0, bytes_at(lbits(self.inp@), p1, t as nat));
        }
        self.n = self.n + t;
        self.pin = self.pin + 8 * t;
        let left2 = left - t;
        self.ph = XPh::Raw { left: left2 };
        if left2 == 0 {
            let q = 8 * self.din + self.pin;
            proof {
                assert((8 * self.din + self.pin) % 8 == 0) by (nonlinear_arith) requires self.pin % 8 == 0;
                lemma_raw_end(self.dict@, self.window as nat, self.fed@, self.st(), q as int, self.mbp as int, self.limit as nat);
            }
            self.ph = XPh::Mb;
        }
        StepR::Go
    }

    /// The fill bits after the last meta-block.
    #[verifier::spinoff_prover]
    pub fn step_fill(&mut self) -> (r: StepR)
        requires old(self).inv(), old(self).ph is Fill,
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, final(self).whole() == old(self).whole(),
            final(self).sent == old(self).sent, final(self).inp == old(self).inp,
            final(self).ph is Done || final(self).ph is Failed,
            r is Stop,
    {
        proof {
            lemma_fill(self.dict@, self.window as nat, self.fed@, self.din as int, self.inp@, self.pin as int, self.st(),
                       self.limit as nat);
        }
        if zero_fill_x(&self.inp, self.pin) {
            let bits = 8 * self.din + align8_x(self.pin);
            self.ph = XPh::Done { bits };
        } else {
            self.ph = XPh::Failed { e: Error::Bad };
        }
        StepR::Stop
    }
}

// ------------------------------------------------ headers and commands

/// A header the decoder holds has what the bounds need.
pub proof fn lemma_xhdr_ok(x: &XHdr, h: Hdr)
    requires xhdr_wf(x, h),
    ensures hdr_ok(h),
{
    reveal(codes_ok);
    assert forall|i: int| 0 <= i < h.cmd.len() implies (#[trigger] h.cmd[i]).len() == 704 by {
        assert(x.cmd@[i].lens@ == h.cmd[i]);
    }
    assert forall|i: int| 0 <= i < h.cmapd.len() implies (#[trigger] h.cmapd[i]) < h.dist.len() by {
        assert(h.cmapd[i] == x.cmapd@[i] as nat);
    }
    assert forall|i: int| 0 <= i < h.dist.len() implies (#[trigger] h.dist[i]).len() == dist_asize(h.npostfix, h.ndirect) by {
        assert(x.dist@[i].lens@ == h.dist[i]);
    }
}

pub proof fn lemma_xhdr_cats(x: &XHdr, h: Hdr)
    requires xhdr_wf(x, h),
    ensures xcat_wf(&x.cl, h.cl), xcat_wf(&x.ci, h.ci), xcat_wf(&x.cd, h.cd),
{
}

pub proof fn lemma_blk_in(k: XBlk, x: &XCat, c: Cat)
    requires blk_ok(k, x), xcat_wf(x, c),
    ensures blk_in(blk(k), c),
{
}

pub proof fn lemma_hdr_advance(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St,
                               end: nat, last: bool, mbp: int, limit: nat, h: Hdr, r2: int)
    requires promise(dict, fed, window, Ph::Hdr { end, last, mbp }, 8 * din + pin, st, None, limit),
        0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin <= 8 * inp.len(),
        read_hdr(lbits(inp), pin) == Some((h, r2)), r2 <= 8 * inp.len(),
    ensures promise(dict, fed, window, Ph::Cmd { h, end, last, mbp, bl: blk0(h.cl), bi: blk0(h.ci), bd: blk0(h.cd) },
                    8 * din + r2, st, None, limit),
{
    hide(cont); hide(cmds_rest); hide(read_hdr);
    let p = 8 * din + pin;
    let ph2 = Ph::Cmd { h, end, last, mbp, bl: blk0(h.cl), bi: blk0(h.ci), bd: blk0(h.cd) };
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Hdr { end, last, mbp }, f, p, st) == cont(dict, window, ph2, f, 8 * din + r2, st) by {
        lemma_cont_hdr(dict, window, f, p, st, end, last, mbp);
        lemma_cont_cmd(dict, window, f, 8 * din + r2, st, h, end, last, mbp, blk0(h.cl), blk0(h.ci), blk0(h.cd));
        lemma_fed_same(fed, din, inp, f, pin);
        lemma_read_hdr_mv(lbits(inp), pin, f, p, 8 * inp.len() - pin);
    }
    lemma_promise_step(dict, fed, window, Ph::Hdr { end, last, mbp }, p, st, ph2, 8 * din + r2, st, limit);
}

pub proof fn lemma_hdr_bad(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St,
                           end: nat, last: bool, mbp: int, limit: nat)
    requires promise(dict, fed, window, Ph::Hdr { end, last, mbp }, 8 * din + pin, st, None, limit),
        0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin, pin + hdr_bits() <= 8 * inp.len(),
        read_hdr(lbits(inp), pin) is None,
    ensures promise(dict, fed, window, Ph::Start, 8 * din + pin, st, Some(Error::Bad), limit),
{
    hide(cont); hide(cmds_rest); hide(read_hdr);
    let p = 8 * din + pin;
    let b = lbits(inp);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Hdr { end, last, mbp }, f, p, st) is None by {
        lemma_cont_hdr(dict, window, f, p, st, end, last, mbp);
        lemma_fed_same(fed, din, inp, f, pin);
        lemma_read_hdr_pos(f, p);
        if read_hdr(f, p) is Some {
            lemma_same_sym(b, pin, f, p, 8 * inp.len() - pin);
            lemma_read_hdr_mv(f, p, b, pin, 8 * inp.len() - pin);
        }
    }
    lemma_promise_bad(dict, fed, window, Ph::Hdr { end, last, mbp }, p, st, Ph::Start, p, st, limit);
}

pub proof fn lemma_cmd_advance(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St,
                               h: Hdr, end: nat, last: bool, mbp: int, bl: Blk, bi: Blk, bd: Blk, limit: nat,
                               bi2: Blk, c: nat, ilen: nat, clen: nat, q3: int)
    requires promise(dict, fed, window, Ph::Cmd { h, end, last, mbp, bl, bi, bd }, 8 * din + pin, st, None, limit),
        0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin <= 8 * inp.len(),
        cmd_head(h, lbits(inp), pin, bi) == Some((bi2, c, ilen, clen, q3)), q3 <= 8 * inp.len(),
    ensures
        st.out.len() + ilen <= end ==> promise(dict, fed, window,
            Ph::Lits { h, end, last, mbp, n: ilen, bl, bd,
                       k: Cmd0 { c, clen, n0: st.out.len(), p0: 8 * din + pin, left0: bi.left, bi2 } },
            8 * din + q3, st, None, limit),
        st.out.len() + ilen > end ==> promise(dict, fed, window, Ph::Start, 8 * din + pin, st, Some(Error::Bad), limit),
{
    hide(cont); hide(cmds_rest); hide(lits_rest); hide(cmd_head);
    let p = 8 * din + pin;
    let k = Cmd0 { c, clen, n0: st.out.len(), p0: p, left0: bi.left, bi2 };
    let ph2 = Ph::Lits { h, end, last, mbp, n: ilen, bl, bd, k };
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Cmd { h, end, last, mbp, bl, bi, bd }, f, p, st)
        == (if st.out.len() + ilen > end { None } else { cont(dict, window, ph2, f, 8 * din + q3, st) }) by {
        lemma_cont_cmd(dict, window, f, p, st, h, end, last, mbp, bl, bi, bd);
        lemma_cont_lits(dict, window, f, 8 * din + q3, st, h, end, last, mbp, ilen, bl, bd, k);
        lemma_cmds_unfold(dict, window, h, f, p, end, st, bl, bi, bd, mbp, last);
        lemma_fed_same(fed, din, inp, f, pin);
        lemma_cmd_head_mv(h, lbits(inp), pin, f, p, 8 * inp.len() - pin, bi);
    }
    if st.out.len() + ilen <= end {
        lemma_promise_step(dict, fed, window, Ph::Cmd { h, end, last, mbp, bl, bi, bd }, p, st, ph2, 8 * din + q3, st, limit);
    } else {
        lemma_promise_bad(dict, fed, window, Ph::Cmd { h, end, last, mbp, bl, bi, bd }, p, st, Ph::Start, p, st, limit);
    }
}

pub proof fn lemma_cmd_bad(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St,
                           h: Hdr, end: nat, last: bool, mbp: int, bl: Blk, bi: Blk, bd: Blk, limit: nat)
    requires promise(dict, fed, window, Ph::Cmd { h, end, last, mbp, bl, bi, bd }, 8 * din + pin, st, None, limit),
        0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin, pin + 117 <= 8 * inp.len(),
        cmd_head(h, lbits(inp), pin, bi) is None, hdr_ok(h), blk_in(bi, h.ci),
    ensures promise(dict, fed, window, Ph::Start, 8 * din + pin, st, Some(Error::Bad), limit),
{
    hide(cont); hide(cmds_rest); hide(lits_rest); hide(cmd_head);
    let p = 8 * din + pin;
    let b = lbits(inp);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Cmd { h, end, last, mbp, bl, bi, bd }, f, p, st) is None by {
        lemma_cont_cmd(dict, window, f, p, st, h, end, last, mbp, bl, bi, bd);
        lemma_cmds_unfold(dict, window, h, f, p, end, st, bl, bi, bd, mbp, last);
        lemma_fed_same(fed, din, inp, f, pin);
        lemma_cmd_head_pos(h, f, p, bi);
        if cmd_head(h, f, p, bi) is Some {
            lemma_same_sym(b, pin, f, p, 8 * inp.len() - pin);
            lemma_cmd_head_mv(h, f, p, b, pin, 8 * inp.len() - pin, bi);
        }
    }
    lemma_promise_bad(dict, fed, window, Ph::Cmd { h, end, last, mbp, bl, bi, bd }, p, st, Ph::Start, p, st, limit);
}

impl Decoder {
    /// A compressed meta-block's header.
    #[verifier::spinoff_prover]
    pub fn step_hdr(&mut self) -> (r: StepR)
        requires old(self).inv(), old(self).ph is Hdr,
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, final(self).whole() == old(self).whole(),
            final(self).sent == old(self).sent, final(self).inp == old(self).inp,
            r is More ==> final(self).ph is Hdr,
            r is Stop ==> final(self).ph is Failed,
            r is Go ==> below(final(self), old(self)),
    {
        hide(xhdr_wf);
        hide(read_hdr);
        let (end, last) = match self.ph { XPh::Hdr { end, last } => (end, last), _ => { assert(false); (0, false) } };
        match read_hdr_x(&self.inp, self.pin) {
            None => {
                if 8 * self.inp.len() - self.pin >= 7_500_000 {
                    proof {
                        lemma_hdr_bad(self.dict@, self.window as nat, self.fed@, self.din as int, self.inp@, self.pin as int,
                                      self.st(), end as nat, last, self.mbp as int, self.limit as nat);
                    }
                    self.ph = XPh::Failed { e: Error::Bad };
                    StepR::Stop
                } else {
                    StepR::More
                }
            }
            Some((h, r2)) => {
                let ghost sh = read_hdr(lbits(self.inp@), self.pin as int).unwrap().0;
                proof {
                    lemma_read_hdr_pos(lbits(self.inp@), self.pin as int);
                    lemma_hdr_advance(self.dict@, self.window as nat, self.fed@, self.din as int, self.inp@, self.pin as int,
                                      self.st(), end as nat, last, self.mbp as int, self.limit as nat, sh, r2 as int);
                }
                proof { lemma_xhdr_cats(&h, sh); }
                let bl = blk0_x(&h.cl, Ghost(sh.cl));
                let bi = blk0_x(&h.ci, Ghost(sh.ci));
                let bd = blk0_x(&h.cd, Ghost(sh.cd));
                self.h = Some(h);
                self.sh = Ghost(sh);
                self.pin = r2;
                self.ph = XPh::Cmd { end, last, bl, bi, bd };
                StepR::Go
            }
        }
    }

    /// A command's start: its head.
    #[verifier::spinoff_prover]
    pub fn step_cmd(&mut self) -> (r: StepR)
        requires old(self).inv(), old(self).ph is Cmd,
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, final(self).whole() == old(self).whole(),
            final(self).sent == old(self).sent, final(self).inp == old(self).inp,
            r is More ==> final(self).ph is Cmd,
            r is Stop ==> final(self).ph is Failed,
            r is Go ==> below(final(self), old(self)),
    {
        let (end, last, bl, bi, bd) = match self.ph {
            XPh::Cmd { end, last, bl, bi, bd } => (end, last, bl, bi, bd),
            _ => { assert(false); (0, false, bl_dummy(), bl_dummy(), bl_dummy()) }
        };
        let ghost sh = self.sh@;
        let ghost p = self.pos();
        let ghost st = self.st();
        let mut x = br_at(&self.inp, self.pin);
        let mut bi2 = bi;
        let hd = match &self.h { Some(h) => h, None => { assert(false); return StepR::More; } };
        proof { lemma_xhdr_ok(hd, sh); }
        match cmd_head_x(hd, Ghost(sh), &self.inp, &mut x, &mut bi2) {
            None => {
                if 8 * self.inp.len() - self.pin >= 117 {
                    proof {
                        lemma_cmd_bad(self.dict@, self.window as nat, self.fed@, self.din as int, self.inp@, self.pin as int,
                                      st, sh, end as nat, last, self.mbp as int, blk(bl), blk(bi), blk(bd), self.limit as nat);
                    }
                    self.ph = XPh::Failed { e: Error::Bad };
                    StepR::Stop
                } else {
                    StepR::More
                }
            }
            Some((c, ilen, clen)) => {
                proof {
                    lemma_cmd_advance(self.dict@, self.window as nat, self.fed@, self.din as int, self.inp@, self.pin as int,
                                      st, sh, end as nat, last, self.mbp as int, blk(bl), blk(bi), blk(bd), self.limit as nat,
                                      blk(bi2), c as nat, ilen as nat, clen as nat, x.p as int);
                    lemma_cmd_head_blk(sh, lbits(self.inp@), self.pin as int, blk(bi));
                }
                let wl = self.base + self.n;
                if ilen > (end - wl) as u64 {
                    self.ph = XPh::Failed { e: Error::Bad };
                    return StepR::Stop;
                }
                let p0 = 8 * self.din + self.pin;
                self.pin = x.p;
                self.ph = XPh::Lits { end, last, n: ilen, bl, bd, c, clen, n0: wl, p0, left0: bi.left, bi2 };
                StepR::Go
            }
        }
    }
}

pub fn bl_dummy() -> (r: XBlk) { XBlk { t: 0, prev: 0, left: 0 } }

// ------------------------------------------------------------- literals

pub proof fn lemma_lits_advance(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St,
                                h: Hdr, end: nat, last: bool, mbp: int, n: nat, bl: Blk, bd: Blk, k: Cmd0, limit: nat,
                                j: nat, o: Seq<u8>, bl2: Blk, q: int)
    requires promise(dict, fed, window, Ph::Lits { h, end, last, mbp, n, bl, bd, k }, 8 * din + pin, st, None, limit),
        0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin <= 8 * inp.len(), j <= n,
        lits(h, lbits(inp), pin, j, st.out, bl) == Some((o, bl2, q)), q <= 8 * inp.len(),
    ensures promise(dict, fed, window, Ph::Lits { h, end, last, mbp, n: (n - j) as nat, bl: bl2, bd, k }, 8 * din + q,
                    St { out: o, ring: st.ring, google: st.google }, None, limit),
{
    hide(cont); hide(lits_rest); hide(lits);
    let p = 8 * din + pin;
    let s2 = St { out: o, ring: st.ring, google: st.google };
    let ph2 = Ph::Lits { h, end, last, mbp, n: (n - j) as nat, bl: bl2, bd, k };
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Lits { h, end, last, mbp, n, bl, bd, k }, f, p, st) == cont(dict, window, ph2, f, 8 * din + q, s2) by {
        lemma_cont_lits(dict, window, f, p, st, h, end, last, mbp, n, bl, bd, k);
        lemma_cont_lits(dict, window, f, 8 * din + q, s2, h, end, last, mbp, (n - j) as nat, bl2, bd, k);
        assert(n == j + (n - j) as nat);
        lemma_lits_rest_split(dict, window, h, f, p, j, (n - j) as nat, end, st, bl, bd, k, mbp, last);
        lemma_fed_same(fed, din, inp, f, pin);
        lemma_lits_mv(h, lbits(inp), pin, f, p, 8 * inp.len() - pin, j, st.out, bl);
    }
    lemma_promise_step(dict, fed, window, Ph::Lits { h, end, last, mbp, n, bl, bd, k }, p, st, ph2, 8 * din + q, s2, limit);
}

pub proof fn lemma_lits_bad(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St,
                            h: Hdr, end: nat, last: bool, mbp: int, n: nat, bl: Blk, bd: Blk, k: Cmd0, limit: nat, j: nat)
    requires promise(dict, fed, window, Ph::Lits { h, end, last, mbp, n, bl, bd, k }, 8 * din + pin, st, None, limit),
        0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin, pin + 69 * j <= 8 * inp.len(), j <= n,
        lits(h, lbits(inp), pin, j, st.out, bl) is None,
    ensures promise(dict, fed, window, Ph::Start, 8 * din + pin, st, Some(Error::Bad), limit),
{
    hide(cont); hide(lits_rest); hide(lits);
    let p = 8 * din + pin;
    let b = lbits(inp);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Lits { h, end, last, mbp, n, bl, bd, k }, f, p, st) is None by {
        lemma_cont_lits(dict, window, f, p, st, h, end, last, mbp, n, bl, bd, k);
        assert(n == j + (n - j) as nat);
        lemma_lits_rest_split(dict, window, h, f, p, j, (n - j) as nat, end, st, bl, bd, k, mbp, last);
        lemma_fed_same(fed, din, inp, f, pin);
        lemma_lits_pos(h, f, p, j, st.out, bl);
        if lits(h, f, p, j, st.out, bl) is Some {
            lemma_same_sym(b, pin, f, p, 8 * inp.len() - pin);
            lemma_lits_mv(h, f, p, b, pin, 8 * inp.len() - pin, j, st.out, bl);
        }
    }
    lemma_promise_bad(dict, fed, window, Ph::Lits { h, end, last, mbp, n, bl, bd, k }, p, st, Ph::Start, p, st, limit);
}

/// Literals that fill the meta-block: it ends here.
pub proof fn lemma_lits_end(dict: Seq<u8>, window: nat, fed: Seq<u8>, p: int, st: St, h: Hdr, end: nat, last: bool,
                            mbp: int, bl: Blk, bd: Blk, k: Cmd0, limit: nat)
    requires promise(dict, fed, window, Ph::Lits { h, end, last, mbp, n: 0, bl, bd, k }, p, st, None, limit),
        st.out.len() >= end, mbp < p <= 8 * fed.len(),
    ensures promise(dict, fed, window, if last { Ph::Fill } else { Ph::Mb }, p, st, None, limit),
{
    hide(cont); hide(lits_rest); hide(tail_rest); hide(mb_rest);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, Ph::Lits { h, end, last, mbp, n: 0, bl, bd, k }, f, p, st)
        == cont(dict, window, if last { Ph::Fill } else { Ph::Mb }, f, p, st) by {
        lemma_cont_lits(dict, window, f, p, st, h, end, last, mbp, 0, bl, bd, k);
        lemma_lits_rest_zero(dict, window, h, f, p, end, st, bl, bd, k, mbp, last);
        reveal(tail_rest);
        lemma_pos_in(fed, f, p);
        lemma_mb_rest_next(dict, window, f, mbp, p, st, last);
    }
    lemma_promise_step(dict, fed, window, Ph::Lits { h, end, last, mbp, n: 0, bl, bd, k }, p, st,
                       if last { Ph::Fill } else { Ph::Mb }, p, st, limit);
}

/// The progress `commands` requires of a command that neither ends the
/// meta-block nor passes it.
pub open spec fn progressed(k: Cmd0, n2: nat, q5: int) -> bool {
    (n2 > k.n0) || (n2 == k.n0 && k.p0 < q5) || (n2 == k.n0 && q5 == k.p0 && k.bi2.left < k.left0)
}

/// A command's tail read from the input.
#[verifier::spinoff_prover]
pub proof fn lemma_tail_advance(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St,
                                h: Hdr, end: nat, last: bool, mbp: int, bl: Blk, bd: Blk, k: Cmd0, limit: nat,
                                st2: St, bd2: Blk, q5: int)
    requires promise(dict, fed, window, Ph::Lits { h, end, last, mbp, n: 0, bl, bd, k }, 8 * din + pin, st, None, limit),
        0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin <= 8 * inp.len(), st.out.len() < end, mbp < 8 * din + pin,
        cmd_tail(dict, window, h, lbits(inp), pin, end, st, k.c, k.clen, bd) == Some((st2, bd2, q5)), pin <= q5 <= 8 * inp.len(),
    ensures
        st2.out.len() >= end ==> promise(dict, fed, window, if last { Ph::Fill } else { Ph::Mb }, 8 * din + q5, st2, None, limit),
        st2.out.len() < end && progressed(k, st2.out.len(), 8 * din + q5) ==>
            promise(dict, fed, window, Ph::Cmd { h, end, last, mbp, bl, bi: k.bi2, bd: bd2 }, 8 * din + q5, st2, None, limit),
        st2.out.len() < end && !progressed(k, st2.out.len(), 8 * din + q5) ==>
            promise(dict, fed, window, Ph::Start, 8 * din + pin, st, Some(Error::Bad), limit),
{
    hide(cont); hide(lits_rest); hide(tail_rest); hide(mb_rest); hide(cmds_rest); hide(cmd_tail);
    let p = 8 * din + pin;
    let q = 8 * din + q5;
    let ph1 = Ph::Lits { h, end, last, mbp, n: 0, bl, bd, k };
    let ph2 = if st2.out.len() >= end { if last { Ph::Fill } else { Ph::Mb } }
              else { Ph::Cmd { h, end, last, mbp, bl, bi: k.bi2, bd: bd2 } };
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies
        cont(dict, window, ph1, f, p, st) == (if st2.out.len() < end && !progressed(k, st2.out.len(), q) { None }
                                               else { cont(dict, window, ph2, f, q, st2) }) by {
        lemma_cont_lits(dict, window, f, p, st, h, end, last, mbp, 0, bl, bd, k);
        lemma_lits_rest_zero(dict, window, h, f, p, end, st, bl, bd, k, mbp, last);
        lemma_fed_same(fed, din, inp, f, pin);
        lemma_cmd_tail_mv(dict, window, h, lbits(inp), pin, f, p, 8 * inp.len() - pin, end, st, k.c, k.clen, bd);
        lemma_pos_in(fed, f, q);
        reveal(tail_rest);
        lemma_mb_rest_next(dict, window, f, mbp, q, st2, last);
        lemma_cont_cmd(dict, window, f, q, st2, h, end, last, mbp, bl, k.bi2, bd2);
    }
    if st2.out.len() < end && !progressed(k, st2.out.len(), q) {
        lemma_promise_bad(dict, fed, window, ph1, p, st, Ph::Start, p, st, limit);
    } else {
        lemma_promise_step(dict, fed, window, ph1, p, st, ph2, q, st2, limit);
    }
}

pub proof fn lemma_tail_bad(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St,
                            h: Hdr, end: nat, last: bool, mbp: int, bl: Blk, bd: Blk, k: Cmd0, limit: nat)
    requires promise(dict, fed, window, Ph::Lits { h, end, last, mbp, n: 0, bl, bd, k }, 8 * din + pin, st, None, limit),
        0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin, pin + 93 <= 8 * inp.len(), st.out.len() < end,
        cmd_tail(dict, window, h, lbits(inp), pin, end, st, k.c, k.clen, bd) is None,
        hdr_ok(h), blk_in(bd, h.cd), k.clen >= 2,
    ensures promise(dict, fed, window, Ph::Start, 8 * din + pin, st, Some(Error::Bad), limit),
{
    hide(cont); hide(lits_rest); hide(tail_rest); hide(cmd_tail);
    let p = 8 * din + pin;
    let b = lbits(inp);
    let ph1 = Ph::Lits { h, end, last, mbp, n: 0, bl, bd, k };
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) implies cont(dict, window, ph1, f, p, st) is None by {
        lemma_cont_lits(dict, window, f, p, st, h, end, last, mbp, 0, bl, bd, k);
        lemma_lits_rest_zero(dict, window, h, f, p, end, st, bl, bd, k, mbp, last);
        reveal(tail_rest);
        lemma_fed_same(fed, din, inp, f, pin);
        reveal(cmd_tail);
        lemma_read_dist_pos(h, st.ring, k.c, k.clen, f, p, bd);
        if cmd_tail(dict, window, h, f, p, end, st, k.c, k.clen, bd) is Some {
            lemma_same_sym(b, pin, f, p, 8 * inp.len() - pin);
            lemma_cmd_tail_mv(dict, window, h, f, p, b, pin, 8 * inp.len() - pin, end, st, k.c, k.clen, bd);
        }
    }
    lemma_promise_bad(dict, fed, window, ph1, p, st, Ph::Start, p, st, limit);
}

/// A whole command read from the input (`cmd_step`, as the whole-buffer
/// decoder reads it): the promise moves to the next command, or past the
/// meta-block's end; the output only grows.
#[verifier::spinoff_prover]
pub proof fn lemma_step_advance(dict: Seq<u8>, window: nat, fed: Seq<u8>, din: int, inp: Seq<u8>, pin: int, st: St,
                                h: Hdr, end: nat, last: bool, mbp: int, bl: Blk, bi: Blk, bd: Blk, limit: nat, r: Step)
    requires promise(dict, fed, window, Ph::Cmd { h, end, last, mbp, bl, bi, bd }, 8 * din + pin, st, None, limit),
        0 <= din <= fed.len(), fed.skip(din) == inp, 0 <= pin <= 8 * inp.len(), mbp < 8 * din + pin, st.out.len() < end,
        cmd_step(dict, window, h, lbits(inp), pin, end, st, bl, bi, bd) == Some(r),
        match r { Step::Done(s2, q) => q <= 8 * inp.len(), Step::Next(s2, a, b2, c2, q) => q <= 8 * inp.len() },
    ensures
        match r {
            Step::Done(st2, q) => ext(st.out, st2.out)
                && promise(dict, fed, window, if last { Ph::Fill } else { Ph::Mb }, 8 * din + q, st2, None, limit),
            Step::Next(st2, bl2, bi2, bd2, q) => ext(st.out, st2.out)
                && ((st2.out.len() > st.out.len() || (st2.out.len() == st.out.len() && pin < q)
                     || (st2.out.len() == st.out.len() && q == pin && bi2.left < bi.left))
                    ==> promise(dict, fed, window, Ph::Cmd { h, end, last, mbp, bl: bl2, bi: bi2, bd: bd2 }, 8 * din + q,
                                st2, None, limit)),
        },
{
    let b = lbits(inp);
    let p = 8 * din + pin;
    assert(inp.len() == fed.len() - din);
    let (bi2, c, ilen, clen, q3) = cmd_head(h, b, pin, bi).unwrap();
    lemma_cmd_head_pos(h, b, pin, bi);
    let (out2, bl2, q4) = lits(h, b, q3, ilen, st.out, bl).unwrap();
    lemma_lits_pos(h, b, q3, ilen, st.out, bl);
    crate::sspec::lemma_lits_ext(h, b, q3, ilen, st.out, bl);
    let s1 = St { out: out2, ring: st.ring, google: st.google };
    let k = Cmd0 { c, clen, n0: st.out.len(), p0: p, left0: bi.left, bi2 };
    if out2.len() >= end {
        lemma_cmd_advance(dict, window, fed, din, inp, pin, st, h, end, last, mbp, bl, bi, bd, limit, bi2, c, ilen, clen, q3);
        lemma_lits_advance(dict, window, fed, din, inp, q3, st, h, end, last, mbp, ilen, bl, bd, k, limit, ilen, out2, bl2, q4);
        assert((ilen - ilen) as nat == 0);
        lemma_lits_end(dict, window, fed, 8 * din + q4, s1, h, end, last, mbp, bl2, bd, k, limit);
    } else {
        let (st2, bd2, q5) = cmd_tail(dict, window, h, b, q4, end, s1, c, clen, bd).unwrap();
        crate::moves::lemma_read_dist_pos(h, s1.ring, c, clen, b, q4, bd);
        crate::sspec::lemma_cmd_tail_ext(dict, window, h, b, q4, end, s1, c, clen, bd);
        lemma_ext_trans(st.out, out2, st2.out);
        lemma_cmd_advance(dict, window, fed, din, inp, pin, st, h, end, last, mbp, bl, bi, bd, limit, bi2, c, ilen, clen, q3);
        lemma_lits_advance(dict, window, fed, din, inp, q3, st, h, end, last, mbp, ilen, bl, bd, k, limit, ilen, out2, bl2, q4);
        assert((ilen - ilen) as nat == 0);
        lemma_tail_advance(dict, window, fed, din, inp, q4, s1, h, end, last, mbp, bl2, bd, k, limit, st2, bd2, q5);
    }
}

impl Decoder {
    pub open spec fn lits_n(&self) -> u64 { match self.ph { XPh::Lits { n, .. } => n, _ => 0 } }

    /// A batch of a command's literals: as many as the bits in hand surely
    /// hold (69 bits each), or one.
    #[verifier::spinoff_prover]
    pub fn step_lits(&mut self) -> (r: StepR)
        requires old(self).inv(), old(self).ph is Lits, old(self).lits_n() > 0,
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, ext(old(self).whole(), final(self).whole()),
            final(self).sent == old(self).sent, final(self).inp == old(self).inp,
            r is More ==> final(self).ph is Lits && final(self).whole() == old(self).whole(),
            r is Stop ==> final(self).ph is Failed,
            r is Go ==> below(final(self), old(self)),
    {
        hide(xhdr_wf);
        let (end, last, n, bl, bd, c, clen, n0, p0, left0, bi2) = match self.ph {
            XPh::Lits { end, last, n, bl, bd, c, clen, n0, p0, left0, bi2 } => (end, last, n, bl, bd, c, clen, n0, p0, left0, bi2),
            _ => { assert(false); (0, false, 0, bl_dummy(), bl_dummy(), 0, 0, 0, 0, 0, bl_dummy()) }
        };
        let ghost sh = self.sh@;
        let ghost st = self.st();
        let ghost w0 = self.whole();
        let ghost k = Cmd0 { c: c as nat, clen: clen as nat, n0: n0 as nat, p0: p0 as int, left0: left0 as nat, bi2: blk(bi2) };
        let avail = 8 * self.inp.len() - self.pin;
        let fit = (avail / 69) as u64;
        let j: u64 = if n < fit { n } else if fit == 0 { 1 } else { fit };
        let mut x = br_at(&self.inp, self.pin);
        let mut bl2 = bl;
        let hd = match &self.h { Some(h) => h, None => { assert(false); return StepR::More; } };
        let ok = lits_x(hd, Ghost(sh), &self.inp, &mut x, j, &mut self.out, self.n, &mut bl2, Ghost(self.pre@));
        if !ok {
            proof { assert(w0.take(w0.len() as int) =~= w0); }
            if avail as u64 >= 69 * j {
                proof {
                    lemma_lits_bad(self.dict@, self.window as nat, self.fed@, self.din as int, self.inp@, self.pin as int,
                                   st, sh, end as nat, last, self.mbp as int, n as nat, blk(bl), blk(bd), k,
                                   self.limit as nat, j as nat);
                }
                self.ph = XPh::Failed { e: Error::Bad };
                return StepR::Stop;
            }
            return StepR::More;
        }
        proof {
            crate::sspec::lemma_lits_ext(sh, lbits(self.inp@), self.pin as int, j as nat, w0, blk(bl));
            lemma_lits_advance(self.dict@, self.window as nat, self.fed@, self.din as int, self.inp@, self.pin as int,
                               st, sh, end as nat, last, self.mbp as int, n as nat, blk(bl), blk(bd), k,
                               self.limit as nat, j as nat, ov(self.pre@, self.out@, (self.n + j) as int), blk(bl2), x.p as int);
        }
        self.n = self.n + j as usize;
        self.pin = x.p;
        self.ph = XPh::Lits { end, last, n: n - j, bl: bl2, bd, c, clen, n0, p0, left0, bi2 };
        StepR::Go
    }

    /// A command after its literals: the meta-block's end, or its distance
    /// and copy, and the next command.
    #[verifier::spinoff_prover]
    pub fn step_tail(&mut self, dict: &[u8]) -> (r: StepR)
        requires old(self).inv(), old(self).ph is Lits, old(self).lits_n() == 0, dict@ == old(self).dict@,
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, ext(old(self).whole(), final(self).whole()),
            final(self).sent == old(self).sent, final(self).inp == old(self).inp,
            r is More ==> final(self).ph is Lits && final(self).whole() == old(self).whole(),
            r is Stop ==> final(self).ph is Failed,
            r is Go ==> below(final(self), old(self)),
    {
        hide(xhdr_wf);
        let (end, last, bl, bd, c, clen, n0, p0, left0, bi2) = match self.ph {
            XPh::Lits { end, last, n, bl, bd, c, clen, n0, p0, left0, bi2 } => (end, last, bl, bd, c, clen, n0, p0, left0, bi2),
            _ => { assert(false); (0, false, bl_dummy(), bl_dummy(), 0, 0, 0, 0, 0, bl_dummy()) }
        };
        let ghost sh = self.sh@;
        let ghost st = self.st();
        let ghost w0 = self.whole();
        let ghost k = Cmd0 { c: c as nat, clen: clen as nat, n0: n0 as nat, p0: p0 as int, left0: left0 as nat, bi2: blk(bi2) };
        let ghost ph1 = self.gph();
        proof { assert(w0.take(w0.len() as int) =~= w0); }
        if self.base + self.n >= end {
            proof {
                assert(self.pos() <= 8 * self.fed@.len());
                lemma_lits_end(self.dict@, self.window as nat, self.fed@, self.pos(), st, sh, end as nat, last,
                               self.mbp as int, blk(bl), blk(bd), k, self.limit as nat);
            }
            self.ph = if last { XPh::Fill } else { XPh::Mb };
            return StepR::Go;
        }
        let mut x = br_at(&self.inp, self.pin);
        let mut bd2 = bd;
        let hd = match &self.h { Some(h) => h, None => { assert(false); return StepR::More; } };
        proof {
            lemma_xhdr_ok(hd, sh);
            lemma_xhdr_cats(hd, sh);
            lemma_blk_in(bd, &hd.cd, sh.cd);
        }
        let end_l = end - self.base;
        match cmd_tail_x(dict, self.window, hd, Ghost(sh), &self.inp, &mut x, end_l, &mut self.out, self.n, self.ring,
                         self.google, c, clen, &mut bd2, Ghost(self.pre@), self.base) {
            None => {
                if 8 * self.inp.len() - self.pin >= 93 {
                    proof {
                        lemma_tail_bad(self.dict@, self.window as nat, self.fed@, self.din as int, self.inp@, self.pin as int,
                                       st, sh, end as nat, last, self.mbp as int, blk(bl), blk(bd), k, self.limit as nat);
                    }
                    self.ph = XPh::Failed { e: Error::Bad };
                    StepR::Stop
                } else {
                    StepR::More
                }
            }
            Some((ring2, g2, n2)) => {
                let ghost st2 = St { out: ov(self.pre@, self.out@, n2 as int), ring: rseq(ring2), google: g2 };
                proof {
                    crate::sspec::lemma_cmd_tail_ext(self.dict@, self.window as nat, sh, lbits(self.inp@), self.pin as int,
                                                     end as nat, st, c as nat, clen as nat, blk(bd));
                    lemma_tail_advance(self.dict@, self.window as nat, self.fed@, self.din as int, self.inp@, self.pin as int,
                                       st, sh, end as nat, last, self.mbp as int, blk(bl), blk(bd), k, self.limit as nat,
                                       st2, blk(bd2), x.p as int);
                }
                let q = 8 * self.din + x.p;
                let wl = self.base + n2;
                proof {
                    // the output before the tail is still there
                    let pre = self.pre@;
                    assert(ext(w0, st2.out));
                    assert(w0.len() == pre.len() + self.n);
                    assert(st2.out.take(w0.len() as int) =~= ov(pre, self.out@, self.n as int));
                    assert(self.whole() == w0);
                }
                if wl < end && !((wl > n0) || (wl == n0 && p0 < q) || (wl == n0 && q == p0 && bi2.left < left0)) {
                    self.ph = XPh::Failed { e: Error::Bad };
                    return StepR::Stop;
                }
                self.n = n2;
                self.ring = ring2;
                self.google = g2;
                if wl >= end {
                    self.pin = x.p;
                    self.ph = if last { XPh::Fill } else { XPh::Mb };
                    return StepR::Go;
                }
                self.pin = x.p;
                self.ph = XPh::Cmd { end, last, bl, bi: bi2, bd: bd2 };
                StepR::Go
            }
        }
    }
}

// ------------------------------------------------------- runs of commands

/// The step loop's measure, lexicographically below or equal.
pub open spec fn meas_le(a: (int, int, int, int), b: (int, int, int, int)) -> bool {
    a.0 < b.0 || (a.0 == b.0 && (a.1 < b.1 || (a.1 == b.1 && (a.2 < b.2 || (a.2 == b.2 && a.3 <= b.3)))))
}

pub open spec fn meas_lt(a: (int, int, int, int), b: (int, int, int, int)) -> bool {
    a.0 < b.0 || (a.0 == b.0 && (a.1 < b.1 || (a.1 == b.1 && (a.2 < b.2 || (a.2 == b.2 && a.3 < b.3)))))
}

pub proof fn lemma_meas_trans(a: (int, int, int, int), b: (int, int, int, int), c: (int, int, int, int))
    requires meas_lt(a, b) || a == b, meas_le(b, c),
    ensures meas_le(a, c),
{
}

pub proof fn lemma_below_le(a: &Decoder, b: &Decoder, c: &Decoder)
    requires meas_le(a.meas(), b.meas()), below(b, c),
    ensures below(a, c),
{
}

impl Decoder {
    pub open spec fn meas(&self) -> (int, int, int, int) { (self.m_r(), self.m_o(), self.m_b(), self.m_s()) }

    pub open spec fn meas_with(&self, ph: XPh) -> (int, int, int, int) {
        (self.m_r(), self.m_o(), m_b_of(ph), m_s_of(ph))
    }

    /// All of a command's literals, from the window `x` at `pin`: `true` if
    /// they are there (the phase is then `Lits` with none left), else
    /// nothing changes that the invariant sees.
    #[verifier::spinoff_prover]
    #[inline(always)]
    fn run_lits(&mut self, ph: &mut XPh, x: &mut Br) -> (ok: bool)
        requires old(self).inv_with(*old(ph)), *old(ph) is Lits, lits_n_of(*old(ph)) > 0, br_wf(old(self).inp@, *old(x)),
            old(x).p == old(self).pin,
        ensures
            final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, ext(old(self).whole(), final(self).whole()),
            final(self).sent == old(self).sent, final(self).inp == old(self).inp,
            br_wf(final(self).inp@, *final(x)), final(x).p == final(self).pin,
            final(self).inv_with(*final(ph)), final(self).ph == old(self).ph,
            ok ==> *final(ph) is Lits && lits_n_of(*final(ph)) == 0
                && meas_lt(final(self).meas_with(*final(ph)), old(self).meas_with(*old(ph))),
            !ok ==> final(self).meas_with(*final(ph)) == old(self).meas_with(*old(ph)) && *final(ph) == *old(ph),
    {
        hide(xhdr_wf);
        let (end, last, n, bl, bd, c, clen, n0, p0, left0, bi2) = match *ph {
            XPh::Lits { end, last, n, bl, bd, c, clen, n0, p0, left0, bi2 } => (end, last, n, bl, bd, c, clen, n0, p0, left0, bi2),
            _ => { assert(false); (0, false, 0, bl_dummy(), bl_dummy(), 0, 0, 0, 0, 0, bl_dummy()) }
        };
        let ghost sh = self.sh@;
        let ghost st = self.st();
        let ghost w0 = self.whole();
        let ghost k = Cmd0 { c: c as nat, clen: clen as nat, n0: n0 as nat, p0: p0 as int, left0: left0 as nat, bi2: blk(bi2) };
        let mut x2 = Br { w: x.w, k: x.k, p: x.p };
        let mut bl2 = bl;
        let hd = match &self.h { Some(h) => h, None => { assert(false); return false; } };
        let ok = lits_x(hd, Ghost(sh), &self.inp, &mut x2, n, &mut self.out, self.n, &mut bl2, Ghost(self.pre@));
        if !ok {
            proof { assert(w0.take(w0.len() as int) =~= w0); assert(self.whole() =~= w0); }
            return false;
        }
        proof {
            crate::sspec::lemma_lits_ext(sh, lbits(self.inp@), self.pin as int, n as nat, w0, blk(bl));
            lemma_lits_advance(self.dict@, self.window as nat, self.fed@, self.din as int, self.inp@, self.pin as int,
                               st, sh, end as nat, last, self.mbp as int, n as nat, blk(bl), blk(bd), k,
                               self.limit as nat, n as nat, ov(self.pre@, self.out@, (self.n + n) as int), blk(bl2), x2.p as int);
        }
        self.n = self.n + n as usize;
        self.pin = x2.p;
        *ph = XPh::Lits { end, last, n: 0, bl: bl2, bd, c, clen, n0, p0, left0, bi2 };
        *x = x2;
        true
    }

    /// A command's tail, from the window `x` at `pin`: 1 if it is there and
    /// another command follows (the phase is then `Cmd`), 2 if the
    /// meta-block ends (the phase is then `Mb` or `Fill`), 0 if it is not
    /// there (or anything else: the step for the phase decides).
    #[verifier::spinoff_prover]
    #[inline(always)]
    fn run_tail(&mut self, dict: &[u8], ph: &mut XPh, x: &mut Br) -> (r: u8)
        requires old(self).inv_with(*old(ph)), *old(ph) is Lits, lits_n_of(*old(ph)) == 0, dict@ == old(self).dict@,
            br_wf(old(self).inp@, *old(x)), old(x).p == old(self).pin,
        ensures
            final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, ext(old(self).whole(), final(self).whole()),
            final(self).sent == old(self).sent, final(self).inp == old(self).inp,
            br_wf(final(self).inp@, *final(x)), final(x).p == final(self).pin,
            final(self).inv_with(*final(ph)), final(self).ph == old(self).ph,
            r == 1 ==> *final(ph) is Cmd && meas_lt(final(self).meas_with(*final(ph)), old(self).meas_with(*old(ph))),
            r == 2 ==> meas_lt(final(self).meas_with(*final(ph)), old(self).meas_with(*old(ph)))
                && (*final(ph) is Mb || *final(ph) is Fill),
            r == 0 ==> final(self).meas_with(*final(ph)) == old(self).meas_with(*old(ph)) && *final(ph) == *old(ph),
            r <= 2,
    {
        hide(xhdr_wf);
        let (end, last, bl, bd, c, clen, n0, p0, left0, bi2) = match *ph {
            XPh::Lits { end, last, n, bl, bd, c, clen, n0, p0, left0, bi2 } => (end, last, bl, bd, c, clen, n0, p0, left0, bi2),
            _ => { assert(false); (0, false, bl_dummy(), bl_dummy(), 0, 0, 0, 0, 0, bl_dummy()) }
        };
        let ghost sh = self.sh@;
        let ghost st = self.st();
        let ghost w0 = self.whole();
        let ghost k = Cmd0 { c: c as nat, clen: clen as nat, n0: n0 as nat, p0: p0 as int, left0: left0 as nat, bi2: blk(bi2) };
        proof { assert(w0.take(w0.len() as int) =~= w0); }
        if self.base + self.n >= end {
            return 0;
        }
        let mut x2 = Br { w: x.w, k: x.k, p: x.p };
        let mut bd2 = bd;
        let hd = match &self.h { Some(h) => h, None => { assert(false); return 0; } };
        proof {
            lemma_xhdr_ok(hd, sh);
            lemma_xhdr_cats(hd, sh);
            lemma_blk_in(bd, &hd.cd, sh.cd);
        }
        let end_l = end - self.base;
        match cmd_tail_x(dict, self.window, hd, Ghost(sh), &self.inp, &mut x2, end_l, &mut self.out, self.n, self.ring,
                         self.google, c, clen, &mut bd2, Ghost(self.pre@), self.base) {
            None => 0,
            Some((ring2, g2, n2)) => {
                let ghost st2 = St { out: ov(self.pre@, self.out@, n2 as int), ring: rseq(ring2), google: g2 };
                proof {
                    crate::sspec::lemma_cmd_tail_ext(self.dict@, self.window as nat, sh, lbits(self.inp@), self.pin as int,
                                                     end as nat, st, c as nat, clen as nat, blk(bd));
                    lemma_tail_advance(self.dict@, self.window as nat, self.fed@, self.din as int, self.inp@, self.pin as int,
                                       st, sh, end as nat, last, self.mbp as int, blk(bl), blk(bd), k, self.limit as nat,
                                       st2, blk(bd2), x2.p as int);
                }
                let q = 8 * self.din + x2.p;
                let wl = self.base + n2;
                proof {
                    let pre = self.pre@;
                    assert(ext(w0, st2.out));
                    assert(w0.len() == pre.len() + self.n);
                    assert(st2.out.take(w0.len() as int) =~= ov(pre, self.out@, self.n as int));
                }
                if wl < end && !((wl > n0) || (wl == n0 && p0 < q) || (wl == n0 && q == p0 && bi2.left < left0)) {
                    // the output beyond `n` has changed, which the invariant does not see
                    proof { assert(self.whole() =~= w0); }
                    return 0;
                }
                self.n = n2;
                self.ring = ring2;
                self.google = g2;
                self.pin = x2.p;
                *x = x2;
                if wl >= end {
                    *ph = if last { XPh::Fill } else { XPh::Mb };
                    return 2;
                }
                *ph = XPh::Cmd { end, last, bl, bi: bi2, bd: bd2 };
                1
            }
        }
    }

    /// A command's head, from the window `x` at `pin`: `true` if it is there
    /// (the phase is then `Lits`), else nothing changes.
    #[verifier::spinoff_prover]
    #[inline(always)]
    fn run_head(&mut self, ph: &mut XPh, x: &mut Br) -> (ok: bool)
        requires old(self).inv_with(*old(ph)), *old(ph) is Cmd, br_wf(old(self).inp@, *old(x)), old(x).p == old(self).pin,
        ensures
            final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, final(self).whole() == old(self).whole(),
            final(self).sent == old(self).sent, final(self).inp == old(self).inp,
            br_wf(final(self).inp@, *final(x)), final(x).p == final(self).pin,
            final(self).inv_with(*final(ph)), final(self).ph == old(self).ph,
            ok ==> *final(ph) is Lits && meas_lt(final(self).meas_with(*final(ph)), old(self).meas_with(*old(ph))),
            !ok ==> final(self).meas_with(*final(ph)) == old(self).meas_with(*old(ph)) && *final(ph) == *old(ph),
    {
        let (end, last, bl, bi, bd) = match *ph {
            XPh::Cmd { end, last, bl, bi, bd } => (end, last, bl, bi, bd),
            _ => { assert(false); (0, false, bl_dummy(), bl_dummy(), bl_dummy()) }
        };
        let ghost sh = self.sh@;
        let ghost st = self.st();
        let mut x2 = Br { w: x.w, k: x.k, p: x.p };
        let mut bi2 = bi;
        let hd = match &self.h { Some(h) => h, None => { assert(false); return false; } };
        proof { lemma_xhdr_ok(hd, sh); }
        match cmd_head_x(hd, Ghost(sh), &self.inp, &mut x2, &mut bi2) {
            None => false,
            Some((c, ilen, clen)) => {
                proof {
                    lemma_cmd_advance(self.dict@, self.window as nat, self.fed@, self.din as int, self.inp@, self.pin as int,
                                      st, sh, end as nat, last, self.mbp as int, blk(bl), blk(bi), blk(bd), self.limit as nat,
                                      blk(bi2), c as nat, ilen as nat, clen as nat, x2.p as int);
                    lemma_cmd_head_blk(sh, lbits(self.inp@), self.pin as int, blk(bi));
                }
                let wl = self.base + self.n;
                if ilen > (end - wl) as u64 {
                    return false;
                }
                let p0 = 8 * self.din + self.pin;
                self.pin = x2.p;
                *x = x2;
                *ph = XPh::Lits { end, last, n: ilen, bl, bd, c, clen, n0: wl, p0, left0: bi.left, bi2 };
                true
            }
        }
    }

    /// Whole commands from the `Cmd` phase, each read by the whole-buffer
    /// decoder's command step (`command_x`) with the state in locals and
    /// stored once at the end: 2 if the meta-block ends (the phase is then
    /// `Mb` or `Fill`), else 1 (the phase is `Cmd`: the next command is not
    /// all there, or the steps are to decide).
    #[verifier::spinoff_prover]
    fn run_fast(&mut self, dict: &[u8], ph: &mut XPh, x: &mut Br) -> (r: u8)
        requires old(self).inv_with(*old(ph)), *old(ph) is Cmd, dict@ == old(self).dict@,
            br_wf(old(self).inp@, *old(x)), old(x).p == old(self).pin,
        ensures
            final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, ext(old(self).whole(), final(self).whole()),
            final(self).sent == old(self).sent, final(self).inp == old(self).inp,
            br_wf(final(self).inp@, *final(x)), final(x).p == final(self).pin,
            final(self).inv_with(*final(ph)), final(self).ph == old(self).ph,
            r == 2 ==> meas_lt(final(self).meas_with(*final(ph)), old(self).meas_with(*old(ph)))
                && (*final(ph) is Mb || *final(ph) is Fill),
            r != 2 ==> *final(ph) is Cmd && meas_le(final(self).meas_with(*final(ph)), old(self).meas_with(*old(ph))),
    {
        hide(xhdr_wf);
        let (end, last, bl, bi, bd) = match *ph {
            XPh::Cmd { end, last, bl, bi, bd } => (end, last, bl, bi, bd),
            _ => { assert(false); (0, false, bl_dummy(), bl_dummy(), bl_dummy()) }
        };
        let ghost sh = self.sh@;
        let ghost w0 = self.whole();
        let ghost m0 = self.meas_with(*ph);
        let ghost pre = self.pre@;
        let ghost s0 = *old(self);
        let hd = match &self.h { Some(h) => h, None => { assert(false); return 1; } };
        let end_l = end - self.base;
        let mut cs = CState { x: Br { w: x.w, k: x.k, p: x.p }, n: self.n, ring: self.ring, google: self.google,
                              bl, bi, bd };
        let mut go = true;
        let mut done = false;
        proof {
            assert(w0.take(w0.len() as int) =~= w0);
            assert(*hd == self.xh());
        }
        while go
            invariant
                self.inp == s0.inp, self.din == s0.din, self.pin == s0.pin, self.n == s0.n, self.base == s0.base,
                self.window == s0.window, self.ring == s0.ring, self.google == s0.google, self.limit == s0.limit,
                self.mbp == s0.mbp, self.sent == s0.sent, self.ph == s0.ph, self.h == s0.h, self.fed == s0.fed,
                self.pre == s0.pre, self.dict == s0.dict, self.sh == s0.sh, self.out@.len() == s0.out@.len(),
                s0.inv_with(XPh::Cmd { end, last, bl, bi, bd }), dict@ == s0.dict@, pre == s0.pre@, sh == s0.sh@,
                *hd == s0.xh(), s0.h is Some, xhdr_wf(hd, sh), end_l == end - s0.base, end_l + 16 <= s0.out@.len(),
                w0 == s0.whole(), m0 == s0.meas_with(XPh::Cmd { end, last, bl, bi, bd }),
                crate::cmd::cs_wf(&cs, hd, s0.inp@, end_l as nat), s0.n <= cs.n,
                two_ok(pre, cs.n as int), cs.n >= s0.window || s0.base == 0, s0.pin <= cs.x.p,
                ext(w0, ov(pre, self.out@, cs.n as int)),
                done ==> !go && cs.n == end_l,
                !done ==> cs.n < end_l,
                !done ==> promise(s0.dict@, s0.fed@, s0.window as nat,
                                  Ph::Cmd { h: sh, end: end as nat, last, mbp: s0.mbp as int, bl: blk(cs.bl), bi: blk(cs.bi),
                                            bd: blk(cs.bd) },
                                  8 * s0.din + cs.x.p, St { out: ov(pre, self.out@, cs.n as int), ring: rseq(cs.ring),
                                                            google: cs.google }, None, s0.limit as nat),
                done ==> promise(s0.dict@, s0.fed@, s0.window as nat, if last { Ph::Fill } else { Ph::Mb },
                                 8 * s0.din + cs.x.p, St { out: ov(pre, self.out@, cs.n as int), ring: rseq(cs.ring),
                                                           google: cs.google }, None, s0.limit as nat),
                !done ==> meas_le((8 * s0.inp@.len() - cs.x.p, s0.limit - (s0.base + cs.n), cs.bi.left as int, 0), m0),
                done ==> meas_lt((8 * s0.inp@.len() - cs.x.p, s0.limit - (s0.base + cs.n), 0, 0), m0),
            decreases 8 * s0.inp@.len() - cs.x.p, end_l - cs.n, cs.bi.left, if go { 1int } else { 0int },
        {
            let (sw, sk, sp) = (cs.x.w, cs.x.k, cs.x.p);
            let (sn, sring, sg, sbl, sbi, sbd) = (cs.n, cs.ring, cs.google, cs.bl, cs.bi, cs.bd);
            let ghost o0 = self.out@;
            let ghost st0 = St { out: ov(pre, o0, sn as int), ring: rseq(sring), google: sg };
            match command_x(dict, self.window, hd, Ghost(sh), &self.inp, end_l, &mut self.out, &mut cs, Ghost(pre),
                            self.base) {
                None => {
                    proof { assert(ov(pre, self.out@, sn as int) =~= ov(pre, o0, sn as int)); }
                    cs = CState { x: Br { w: sw, k: sk, p: sp }, n: sn, ring: sring, google: sg, bl: sbl, bi: sbi, bd: sbd };
                    go = false;
                }
                Some(d) => {
                    let ghost st2 = St { out: ov(pre, self.out@, cs.n as int), ring: rseq(cs.ring), google: cs.google };
                    proof {
                        let rr = if d { Step::Done(st2, cs.x.p as int) }
                                 else { Step::Next(st2, blk(cs.bl), blk(cs.bi), blk(cs.bd), cs.x.p as int) };
                        assert(st0 == crate::cmd::cs_st(&CState { x: Br { w: sw, k: sk, p: sp }, n: sn, ring: sring,
                                                                   google: sg, bl: sbl, bi: sbi, bd: sbd }, pre, o0));
                        lemma_step_advance(s0.dict@, s0.window as nat, s0.fed@, s0.din as int, s0.inp@, sp as int, st0, sh,
                                           end as nat, last, s0.mbp as int, blk(sbl), blk(sbi), blk(sbd), s0.limit as nat, rr);
                        lemma_ext_trans(w0, st0.out, st2.out);
                    }
                    if d {
                        done = true;
                        go = false;
                    } else if !((cs.n > sn) || (cs.n == sn && sp < cs.x.p) || (cs.n == sn && cs.x.p == sp && cs.bi.left < sbi.left)) {
                        proof { assert(ov(pre, self.out@, sn as int) =~= st2.out.take(st0.out.len() as int)); }
                        cs = CState { x: Br { w: sw, k: sk, p: sp }, n: sn, ring: sring, google: sg, bl: sbl, bi: sbi, bd: sbd };
                        go = false;
                    }
                }
            }
        }
        self.n = cs.n;
        self.ring = cs.ring;
        self.google = cs.google;
        self.pin = cs.x.p;
        *x = Br { w: cs.x.w, k: cs.x.k, p: cs.x.p };
        if done {
            *ph = if last { XPh::Fill } else { XPh::Mb };
            proof { assert(self.st() == St { out: ov(pre, self.out@, cs.n as int), ring: rseq(cs.ring), google: cs.google }); }
            2
        } else {
            *ph = XPh::Cmd { end, last, bl: cs.bl, bi: cs.bi, bd: cs.bd };
            proof {
                assert(self.st() == St { out: ov(pre, self.out@, cs.n as int), ring: rseq(cs.ring), google: cs.google });
                assert(*hd == self.xh());
            }
            1
        }
    }

    /// Commands one after another from one bit window, as long as each is
    /// there whole: the `Lits` and `Cmd` steps without the step loop between
    /// them, the phase kept in a local. It stops, in a state the steps go on
    /// from, at anything else.
    fn run_cmds(&mut self, dict: &[u8])
        requires old(self).inv(), old(self).ph is Lits, dict@ == old(self).dict@,
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, ext(old(self).whole(), final(self).whole()),
            final(self).sent == old(self).sent, final(self).inp == old(self).inp,
            meas_le(final(self).meas(), old(self).meas()),
            !(final(self).ph is Failed) && !(final(self).ph is Done),
    {
        let ghost m0 = self.meas();
        let ghost w0 = self.whole();
        let mut ph = self.ph;
        let mut x = br_at(&self.inp, self.pin);
        proof { assert(ext(w0, w0)) by { assert(w0.take(w0.len() as int) =~= w0); } }
        loop
            invariant
                self.inv_with(ph), ph is Lits, dict@ == self.dict@, br_wf(self.inp@, x), x.p == self.pin,
                self.fed == old(self).fed, self.dict == old(self).dict, self.limit == old(self).limit,
                self.sent == old(self).sent, self.inp == old(self).inp, w0 == old(self).whole(), ext(w0, self.whole()),
                meas_le(self.meas_with(ph), m0), m0 == old(self).meas(),
            decreases self.m_r(), self.m_o(), m_b_of(ph), m_s_of(ph),
        {
            let ghost mb = self.meas_with(ph);
            let more = match ph { XPh::Lits { n, .. } => n > 0, _ => false };
            if more {
                let ghost wl = self.whole();
                let ok = self.run_lits(&mut ph, &mut x);
                proof {
                    lemma_ext_trans(w0, wl, self.whole());
                    lemma_meas_trans(self.meas_with(ph), mb, m0);
                }
                if !ok {
                    self.ph = ph;
                    return;
                }
            }
            let ghost wt = self.whole();
            let ghost mt = self.meas_with(ph);
            let ghost pt = ph;
            proof { assert(meas_le(mt, m0)); assert(pt is Lits); }
            let r = self.run_tail(dict, &mut ph, &mut x);
            proof {
                lemma_ext_trans(w0, wt, self.whole());
                if r == 0 { assert(self.meas_with(ph) == mt); assert(ph == pt); }
                else if r == 2 { assert(meas_lt(self.meas_with(ph), mt)); assert(ph is Mb || ph is Fill); }
                else { assert(meas_lt(self.meas_with(ph), mt)); }
                lemma_meas_trans(self.meas_with(ph), mt, m0);
                assert(!(ph is Failed) && !(ph is Done));
            }
            if r != 1 {
                self.ph = ph;
                return;
            }
            // whole commands in locals, as long as they are all there
            let ghost mf = self.meas_with(ph);
            let ghost wf = self.whole();
            let rf = self.run_fast(dict, &mut ph, &mut x);
            proof {
                lemma_ext_trans(w0, wf, self.whole());
                assert(meas_lt(mf, mt));
                if rf == 2 { assert(meas_lt(self.meas_with(ph), mf)); } else { assert(meas_le(self.meas_with(ph), mf)); }
                assert(meas_lt(self.meas_with(ph), mt));
                lemma_meas_trans(self.meas_with(ph), mt, m0);
            }
            if rf == 2 {
                self.ph = ph;
                return;
            }
            let ghost mh = self.meas_with(ph);
            let ok = self.run_head(&mut ph, &mut x);
            proof { lemma_meas_trans(self.meas_with(ph), mh, m0); }
            if !ok {
                self.ph = ph;
                return;
            }
            proof {
                assert(meas_lt(self.meas_with(ph), mh) && meas_lt(mh, mt));
                assert(meas_lt(mt, mb) || mt == mb);
                assert(meas_lt(self.meas_with(ph), mb));
            }
        }
    }
}

// ------------------------------------------------------------ feeding

pub proof fn lemma_prefix_ext(fed: Seq<u8>, chunk: Seq<u8>, f: Seq<bool>)
    requires is_prefix(lbits(fed + chunk), f),
    ensures is_prefix(lbits(fed), f),
{
    assert forall|i: int| 0 <= i < lbits(fed).len() implies #[trigger] lbits(fed)[i] == f[i] by {
        assert(lbits(fed + chunk)[i] == f[i]);
        assert((fed + chunk)[i / 8] == fed[i / 8]);
    }
}

/// More input keeps the promise.
pub proof fn lemma_promise_extend(dict: Seq<u8>, fed: Seq<u8>, chunk: Seq<u8>, window: nat, ph: Ph, pos: int, st: St,
                                  fail: Option<Error>, limit: nat)
    requires promise(dict, fed, window, ph, pos, st, fail, limit),
    ensures promise(dict, fed + chunk, window, ph, pos, st, fail, limit),
{
    reveal(promise);
    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed + chunk), f) implies is_prefix(lbits(fed), f) by {
        lemma_prefix_ext(fed, chunk, f);
    }
}

/// What a piece of input leaves, for every stream that starts with the
/// input so far (`fed`): its output is exactly the output sent (`Done`), or
/// starts with it (`NeedMore`); there is none (`Bad`); or it is longer than
/// the limit (`TooBig`).
pub open spec fn verdict(dict: Seq<u8>, fed: Seq<u8>, sent: Seq<u8>, limit: nat, r: Result<Status, Error>) -> bool {
    match r {
        Ok(Status::Done { bits }) => forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==>
            (brotli(dict, f) matches Some((o, q, g)) && o == sent && q == bits),
        Ok(Status::NeedMore) => forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==>
            (brotli(dict, f) matches Some((o, q, g)) ==> ext(sent, o)),
        Err(Error::Bad) => forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==> brotli(dict, f) is None,
        Err(Error::TooBig) => forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==>
            (brotli(dict, f) matches Some((o, q, g)) ==> o.len() > limit),
    }
}

impl Decoder {
    /// Send the output not sent yet.
    fn send(&mut self, sink: &mut Vec<u8>)
        requires old(self).inv(),
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, final(self).whole() == old(self).whole(),
            final(self).sent == final(self).whole().len(), final(self).ph == old(self).ph,
            final(self).pos() == old(self).pos(), final(self).inp == old(self).inp, final(self).pin == old(self).pin,
            final(sink)@ == old(sink)@ + old(self).whole().skip(old(self).sent as int),
    {
        let ghost w0 = self.whole();
        let ghost s0 = sink@;
        let from = self.sent - self.base;
        append(sink, vstd::slice::slice_subrange(self.out.as_slice(), from, self.n));
        proof {
            assert(self.out@.subrange(from as int, self.n as int) =~= w0.skip(self.sent as int));
        }
        self.sent = self.base + self.n;
    }

    /// Drop the input bytes already used.
    fn drop_used(&mut self)
        requires old(self).inv(),
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, final(self).whole() == old(self).whole(),
            final(self).sent == old(self).sent, final(self).ph == old(self).ph, final(self).pos() == old(self).pos(),
            final(self).pin < 8,
    {
        let d = self.pin / 8;
        let len = self.inp.len();
        let ghost i0 = self.inp@;
        self.inp.as_mut_slice().copy_within(d..len, 0);
        self.inp.truncate(len - d);
        proof { assert(self.inp@ =~= i0.skip(d as int)); }
        self.din = self.din + d;
        self.pin = self.pin - 8 * d;
        proof {
            assert(self.fed@.skip(self.din as int) =~= i0.skip(d as int));
        }
    }

    /// The step for the current phase.
    fn step(&mut self, dict: &[u8], sink: &mut Vec<u8>) -> (r: StepR)
        requires old(self).inv(), dict@ == old(self).dict@, !(old(self).ph is Failed), !(old(self).ph is Done),
            old(sink)@ == old(sink)@,
        ensures
            final(self).inv(), final(self).fed == old(self).fed, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, ext(old(self).whole(), final(self).whole()),
            final(self).inp == old(self).inp,
            final(sink)@ == old(sink)@ + final(self).whole().subrange(old(self).sent as int, final(self).sent as int),
            old(self).sent <= final(self).sent <= final(self).whole().len(),
            r is Go ==> below(final(self), old(self)),
            r is More ==> final(self).whole() == old(self).whole() && !(final(self).ph is Failed) && !(final(self).ph is Done),
    {
        let ghost w0 = self.whole();
        let ghost s0 = sink@;
        proof { assert(w0.take(w0.len() as int) =~= w0); }
        let r = match self.ph {
            XPh::Start => self.step_start(),
            XPh::Mb => {
                self.flush(sink);
                self.step_mb()
            }
            XPh::Skip { .. } => self.step_skip(),
            XPh::Raw { .. } => self.step_raw(),
            XPh::Hdr { .. } => self.step_hdr(),
            XPh::Cmd { .. } => {
                let r = self.step_cmd();
                match r {
                    StepR::Go => {
                        // whole commands without coming back here, as far as they go
                        match self.ph {
                            XPh::Lits { .. } => {
                                let ghost d1 = self.meas();
                                let ghost w1 = self.whole();
                                self.run_cmds(dict);
                                proof { lemma_ext_trans(w0, w1, self.whole()); }
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
                r
            }
            XPh::Lits { n, .. } => if n > 0 { self.step_lits() } else { self.step_tail(dict) },
            XPh::Fill => self.step_fill(),
            _ => { assert(false); StepR::Stop }
        };
        proof {
            let w1 = self.whole();
            assert(w1.subrange(old(self).sent as int, self.sent as int) =~= w0.skip(old(self).sent as int)
                   || self.sent == old(self).sent);
        }
        r
    }
}

impl Decoder {
    /// Take the next piece of input.
    fn take_piece(&mut self, chunk: &[u8])
        requires old(self).inv(), old(self).fed@.len() + chunk@.len() < big(),
        ensures
            final(self).inv(), final(self).fed@ == old(self).fed@ + chunk@, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, final(self).whole() == old(self).whole(),
            final(self).sent == old(self).sent, final(self).ph == old(self).ph,
    {
        let ghost i0 = self.inp@;
        append(&mut self.inp, chunk);
        proof {
            let fed0 = self.fed@;
            assert((fed0 + chunk@).skip(self.din as int) =~= i0 + chunk@);
            lemma_promise_extend(self.dict@, fed0, chunk@, self.window as nat, self.gph(), self.pos(), self.st(),
                                 self.gfail(), self.limit as nat);
        }
        self.fed = Ghost(self.fed@ + chunk@);
    }

    /// Decode the next piece of input: the output it decides goes to
    /// `sink`, and the verdict holds for every stream that starts with all
    /// the input so far.
    #[verifier::spinoff_prover]
    pub fn feed(&mut self, dict: &[u8], chunk: &[u8], sink: &mut Vec<u8>) -> (r: Result<Status, Error>)
        requires old(self).inv(), dict@ == old(self).dict@, old(self).sent == old(self).whole().len(),
            old(self).fed@.len() + chunk@.len() < big(),
        ensures
            final(self).inv(), final(self).fed@ == old(self).fed@ + chunk@, final(self).dict == old(self).dict,
            final(self).limit == old(self).limit, final(self).sent == final(self).whole().len(),
            ext(old(self).whole(), final(self).whole()),
            final(sink)@ == old(sink)@ + final(self).whole().skip(old(self).whole().len() as int),
            verdict(final(self).dict@, final(self).fed@, final(self).whole(), final(self).limit as nat, r),
    {
        let ghost w0 = self.whole();
        let ghost s0 = sink@;
        self.take_piece(chunk);
        proof { assert(w0.take(w0.len() as int) =~= w0); assert(w0.subrange(w0.len() as int, w0.len() as int) =~= Seq::<u8>::empty()); }
        loop
            invariant
                self.inv(), dict@ == self.dict@, self.fed@ == old(self).fed@ + chunk@, self.limit == old(self).limit,
                ext(w0, self.whole()), w0.len() <= self.sent <= self.whole().len(),
                sink@ == s0 + self.whole().subrange(w0.len() as int, self.sent as int),
            decreases self.m_r(), self.m_o(), self.m_b(), self.m_s(),
        {
            match self.ph {
                XPh::Failed { .. } | XPh::Done { .. } => break,
                _ => {}
            }
            let ghost wb = self.whole();
            let ghost sb = sink@;
            let ghost sent_b = self.sent;
            let r = self.step(dict, sink);
            proof {
                lemma_ext_trans(w0, wb, self.whole());
                assert(self.whole().take(wb.len() as int) == wb);
                assert(self.whole().subrange(w0.len() as int, sent_b as int) =~= wb.subrange(w0.len() as int, sent_b as int));
                assert(sink@ =~= s0 + self.whole().subrange(w0.len() as int, self.sent as int));
            }
            match r {
                StepR::Go => {}
                _ => break,
            }
        }
        let ghost sb = sink@;
        let ghost sent_b = self.sent;
        self.send(sink);
        proof {
            assert(sink@ =~= s0 + self.whole().skip(w0.len() as int));
        }
        self.drop_used();
        proof { reveal(promise); }
        match self.ph {
            XPh::Done { bits } => {
                proof {
                    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(self.fed@), f) implies
                        (brotli(self.dict@, f) matches Some((o, q, g)) && o == self.whole() && q == bits) by {
                        lemma_cont_done(self.dict@, self.window as nat, f, self.pos(), self.st(), bits as nat);
                    }
                }
                Ok(Status::Done { bits })
            }
            XPh::Failed { e } => Err(e),
            _ => {
                proof {
                    assert forall|f: Seq<bool>| #[trigger] is_prefix(lbits(self.fed@), f) implies
                        (brotli(self.dict@, f) matches Some((o, q, g)) ==> ext(self.whole(), o)) by {
                        if self.ph is Start { assert(self.whole() =~= Seq::<u8>::empty()); }
                        lemma_cont_ext(self.dict@, self.window as nat, self.gph(), f, self.pos(), self.st());
                    }
                }
                Ok(Status::NeedMore)
            }
        }
    }
}

} // verus!
