//! Streaming zlib and gzip decoding: the header, then the DEFLATE stream
//! through the bounded-memory `Inflater`, then the trailer, checked against
//! Adler-32 or CRC-32 carried along the output.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::spec::*;
use crate::step::*;
use crate::stream::*;
use crate::wrap::*;
use crate::inflate::Error;
#[cfg(verus_keep_ghost)]
use vbits::lsb::*;
#[cfg(verus_keep_ghost)]
use crate::huff::max_input;

verus! {

/// `a` starts `s`.
pub open spec fn pfx(a: Seq<u8>, s: Seq<u8>) -> bool {
    a.len() <= s.len() && s.take(a.len() as int) == a
}

pub open spec fn zdec(gz: bool, s: Seq<u8>) -> Option<(Seq<u8>, int, bool)> {
    if gz { gzip_decode(s) } else { zlib_decode(s) }
}

pub open spec fn zlib_hdr_ok(s: Seq<u8>) -> bool {
    let cmf = s[0] as nat;
    let flg = s[1] as nat;
    !(cmf % 16 != 8 || cmf / 16 > 7 || (cmf * 256 + flg) % 31 != 0 || (flg / 32) % 2 == 1)
}

/// Where the header ends.
pub open spec fn zhdr(gz: bool, s: Seq<u8>) -> Option<int> {
    if gz { gzip_header(s) } else if s.len() >= 2 && zlib_hdr_ok(s) { Some(2) } else { None }
}

/// A header no more input can mend.
pub open spec fn hdr_bad(gz: bool, s: Seq<u8>) -> bool {
    if gz {
        (s.len() >= 1 && s[0] != 0x1f) || (s.len() >= 2 && s[1] != 0x8b) || (s.len() >= 3 && s[2] != 8)
            || (s.len() >= 4 && s[3] / 32 != 0)
    } else {
        s.len() >= 2 && !zlib_hdr_ok(s)
    }
}

pub open spec fn tl(gz: bool) -> int { if gz { 8 } else { 4 } }

pub open spec fn trail_ok(gz: bool, s: Seq<u8>, a: int, o: Seq<u8>) -> bool {
    if gz {
        ((s[a + 3] as nat * 256 + s[a + 2] as nat) * 256 + s[a + 1] as nat) * 256 + s[a] as nat == crc32(o) as nat
        && ((s[a + 7] as nat * 256 + s[a + 6] as nat) * 256 + s[a + 5] as nat) * 256 + s[a + 4] as nat
            == o.len() % 0x1_0000_0000
    } else {
        ((s[a] as nat * 256 + s[a + 1] as nat) * 256 + s[a + 2] as nat) * 256 + s[a + 3] as nat == adler32(o)
    }
}

/// zlib or gzip after a header that ends at `h`.
pub open spec fn zdec_from(gz: bool, s: Seq<u8>, h: int) -> Option<(Seq<u8>, int, bool)> {
    match inflate(lbits(s.skip(h))) {
        None => None,
        Some((o, q, st)) => {
            let a = after_bits(h, q);
            if a + tl(gz) > s.len() { None } else if trail_ok(gz, s, a, o) { Some((o, a + tl(gz), st)) } else { None }
        }
    }
}

pub proof fn lemma_zdec(gz: bool, s: Seq<u8>, h: int)
    requires zhdr(gz, s) == Some(h),
    ensures zdec(gz, s) == zdec_from(gz, s, h),
{
}

pub proof fn lemma_hdr_bad(gz: bool, s: Seq<u8>, s2: Seq<u8>)
    requires hdr_bad(gz, s), pfx(s, s2),
    ensures zdec(gz, s2) is None,
{
    assert forall|k: int| 0 <= k < s.len() implies #[trigger] s2[k] == s[k] by { assert(s2.take(s.len() as int)[k] == s2[k]); }
}

proof fn lemma_zero_at_ext(s: Seq<u8>, s2: Seq<u8>, i: int)
    requires pfx(s, s2), zero_at(s, i) is Some,
    ensures zero_at(s2, i) == zero_at(s, i), i <= zero_at(s, i).unwrap() < s.len(),
    decreases s.len() - i,
{
    assert(s2[i] == s2.take(s.len() as int)[i]);
    if s[i] != 0 { lemma_zero_at_ext(s, s2, i + 1); }
}

/// A gzip header is decided by the bytes it spans.
pub proof fn lemma_gzip_header_ext(s: Seq<u8>, s2: Seq<u8>)
    requires gzip_header(s) is Some, pfx(s, s2),
    ensures gzip_header(s2) == gzip_header(s), gzip_header(s).unwrap() <= s.len(),
{
    assert forall|k: int| 0 <= k < s.len() implies #[trigger] s2[k] == s[k] by { assert(s2.take(s.len() as int)[k] == s2[k]); }
    let flg = s[3] as nat;
    let i1: int = if (flg / 4) % 2 == 1 { 12 + s[10] as int + 256 * s[11] as int } else { 10 };
    assert(i1 <= s.len());
    let i2: int = if (flg / 8) % 2 == 1 {
        lemma_zero_at_ext(s, s2, i1);
        zero_at(s, i1).unwrap() + 1
    } else { i1 };
    assert(i2 <= s.len());
    let i3: int = if (flg / 16) % 2 == 1 {
        lemma_zero_at_ext(s, s2, i2);
        zero_at(s, i2).unwrap() + 1
    } else { i2 };
    assert(i3 <= s.len());
    if (flg / 2) % 2 == 1 {
        assert(i3 + 2 <= s.len());
        assert forall|k: int| 0 <= k < i3 implies #[trigger] s2.take(i3)[k] == s.take(i3)[k] by {
            assert(s2[k] == s[k]);
        }
        assert(s2.take(i3) =~= s.take(i3));
        assert(s2[i3] == s[i3] && s2[i3 + 1] == s[i3 + 1]);
    }
}

pub proof fn lemma_zhdr_ext(gz: bool, s: Seq<u8>, s2: Seq<u8>)
    requires zhdr(gz, s) is Some, pfx(s, s2),
    ensures zhdr(gz, s2) == zhdr(gz, s), zhdr(gz, s).unwrap() <= s.len(),
{
    if gz {
        lemma_gzip_header_ext(s, s2);
    } else {
        assert(s2[0] == s2.take(s.len() as int)[0]);
        assert(s2[1] == s2.take(s.len() as int)[1]);
    }
}

pub proof fn lemma_pfx_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires pfx(a, b), pfx(b, c),
    ensures pfx(a, c),
{
    assert(c.take(a.len() as int) =~= b.take(a.len() as int)) by {
        assert forall|k: int| 0 <= k < a.len() implies #[trigger] c.take(a.len() as int)[k] == b.take(a.len() as int)[k] by {
            assert(c.take(b.len() as int)[k] == c[k]);
        }
    }
}

/// The body of a stream that starts with `fed`, from byte `h`, starts with
/// what of `fed` follows `h`; its bits start with those bits.
pub proof fn lemma_body_pfx(fed: Seq<u8>, s: Seq<u8>, h: int, body: Seq<u8>)
    requires pfx(fed, s), 0 <= h <= fed.len(), pfx(body, fed.skip(h)),
    ensures is_prefix(lbits(body), lbits(s.skip(h))),
{
    assert(pfx(fed.skip(h), s.skip(h))) by {
        assert(s.skip(h).take(fed.len() - h) =~= fed.skip(h)) by {
            assert forall|k: int| 0 <= k < fed.len() - h implies #[trigger] s.skip(h).take(fed.len() - h)[k] == fed.skip(h)[k] by {
                assert(s.take(fed.len() as int)[h + k] == s[h + k]);
            }
        }
    }
    lemma_pfx_trans(body, fed.skip(h), s.skip(h));
    let t = s.skip(h);
    assert(t =~= body + t.skip(body.len() as int)) by {
        assert forall|k: int| 0 <= k < body.len() implies #[trigger] t[k] == body[k] by {
            assert(t.take(body.len() as int)[k] == t[k]);
        }
    }
    crate::stream::lemma_lbits_prefix(body, t.skip(body.len() as int));
}

// ------------------------------------------------------------- the decoder

pub enum ZStatus {
    NeedMore,
    /// The member took `n` bytes.
    Done { n: usize, zlib: bool },
}

#[derive(Clone, Copy)]
pub enum ZPhase {
    Hdr,
    Body { h: usize },
    Trail { h: usize, a: usize, bits: usize, st: bool },
    Fin { n: usize, st: bool },
    Failed { e: Error },
}

/// What a verdict says of every stream that starts with the input so far.
pub open spec fn zres_ok(gz: bool, fed: Seq<u8>, out: Seq<u8>, limit: nat, r: Result<ZStatus, Error>) -> bool {
    match r {
        Ok(ZStatus::Done { n, zlib }) => forall|s: Seq<u8>| #[trigger] pfx(fed, s) ==> zdec(gz, s) == Some((out, n as int, zlib)),
        Ok(ZStatus::NeedMore) => zdec(gz, fed) is None,
        Err(Error::Bad) => forall|s: Seq<u8>| #[trigger] pfx(fed, s) ==> zdec(gz, s) is None,
        Err(Error::TooBig) => forall|s: Seq<u8>| #[trigger] pfx(fed, s) ==>
            (zdec(gz, s) matches Some((o, _, _)) ==> o.len() > limit),
    }
}

proof fn lemma_zres_ext(gz: bool, fed: Seq<u8>, fed2: Seq<u8>, out: Seq<u8>, limit: nat, r: Result<ZStatus, Error>)
    requires zres_ok(gz, fed, out, limit, r), pfx(fed, fed2), !(r matches Ok(ZStatus::NeedMore)),
    ensures zres_ok(gz, fed2, out, limit, r),
{
    hide(gzip_decode);
    hide(zlib_decode);
    assert forall|s: Seq<u8>| #[trigger] pfx(fed2, s) implies pfx(fed, s) by { lemma_pfx_trans(fed, fed2, s); }
}

proof fn lemma_pfx_app(a: Seq<u8>, b: Seq<u8>)
    ensures pfx(a, a + b),
{
    assert((a + b).take(a.len() as int) =~= a);
}

pub struct ZInflater {
    pub gz: bool,
    pub ph: ZPhase,
    pub hb: Vec<u8>,
    pub inf: Inflater,
    pub f0: usize,
    pub ca: u32,
    pub cb: u32,
    pub cc: u32,
    pub cn: u32,
    pub tb: [u32; 256],
    pub fed: Ghost<Seq<u8>>,
}

impl ZInflater {
    pub open spec fn out(&self) -> Seq<u8> { self.inf.whole() }

    pub open spec fn ck_ok(&self) -> bool {
        &&& self.cn as nat == self.out().len() % 0x1_0000_0000
        &&& (self.gz ==> self.cc == crc_run(0xFFFF_FFFF, self.out()))
        &&& (!self.gz ==> self.ca as nat == adler_a(self.out()) % 65521 && self.cb as nat == adler_b(self.out()) % 65521)
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.inf.inv() && self.f0 == self.inf.fed().len() && self.inf.fed().len() <= self.fed@.len()
        &&& self.fed@.len() < max_input()
        &&& forall|i: int| 0 <= i < 256 ==> #[trigger] self.tb[i] == crc_byte(0, i as u8)
        &&& self.ck_ok()
        &&& match self.ph {
            ZPhase::Hdr => self.hb@ == self.fed@ && self.inf.fed().len() == 0 && self.inf.whole().len() == 0,
            ZPhase::Body { h } => zhdr(self.gz, self.fed@) == Some(h as int) && h <= self.fed@.len()
                && self.fed@.skip(h as int) == self.inf.fed()
                && inflate_blocks(lbits(self.inf.fed()), 0, Seq::empty(), true) is None,
            ZPhase::Trail { h, a, bits, st } => zhdr(self.gz, self.fed@) == Some(h as int) && h <= self.fed@.len()
                && pfx(self.inf.fed(), self.fed@.skip(h as int))
                && (forall|f: Seq<bool>| #[trigger] is_prefix(lbits(self.inf.fed()), f) ==>
                    inflate_blocks(f, 0, Seq::empty(), true) == Some((self.out(), bits as int, st)))
                && a == h + (bits + 7) / 8 && a <= self.fed@.len()
                && self.hb@ == self.fed@.subrange(a as int, self.fed@.len() as int) && self.hb@.len() < tl(self.gz),
            ZPhase::Fin { n, st } => zres_ok(self.gz, self.fed@, self.out(), self.inf.limit as nat, Ok(ZStatus::Done { n, zlib: st })),
            ZPhase::Failed { e } => zres_ok(self.gz, self.fed@, self.out(), self.inf.limit as nat, Err(e)),
        }
    }

    /// A decoder of a zlib stream (`gz` false) or a gzip member, whose output
    /// may be up to `limit` bytes.
    pub fn new(gz: bool, limit: usize) -> (d: ZInflater)
        requires limit <= crate::inflate::max_len(),
        ensures d.inv(), d.gz == gz, d.fed@.len() == 0, d.out().len() == 0, d.inf.limit == limit,
    {
        let d = ZInflater {
            gz, ph: ZPhase::Hdr, hb: Vec::new(), inf: Inflater::new(limit), f0: 0,
            ca: 1, cb: 0, cc: 0xFFFF_FFFF, cn: 0, tb: crc_table(), fed: Ghost(Seq::empty()),
        };
        proof { assert(d.hb@ =~= d.fed@); }
        d
    }
}

/// Check the trailer (all `tl` bytes of it, in `hb`) against the output.
fn trail_check(gz: bool, hb: &Vec<u8>, ca: u32, cb: u32, cc: u32, cn: u32, Ghost(out): Ghost<Seq<u8>>) -> (ok: bool)
    requires hb@.len() == tl(gz),
        cn as nat == out.len() % 0x1_0000_0000,
        gz ==> cc == crc_run(0xFFFF_FFFF, out),
        !gz ==> ca as nat == adler_a(out) % 65521 && cb as nat == adler_b(out) % 65521,
    ensures ok == trail_ok(gz, hb@, 0, out),
{
    if gz {
        let c = ((hb[3] as u64 * 256 + hb[2] as u64) * 256 + hb[1] as u64) * 256 + hb[0] as u64;
        let z = ((hb[7] as u64 * 256 + hb[6] as u64) * 256 + hb[5] as u64) * 256 + hb[4] as u64;
        c == (cc ^ 0xFFFF_FFFF) as u64 && z == cn as u64
    } else {
        let w = ((hb[0] as u64 * 256 + hb[1] as u64) * 256 + hb[2] as u64) * 256 + hb[3] as u64;
        assert(cb as u64 * 65536 + ca as u64 <= 65520 * 65536 + 65520) by (nonlinear_arith) requires ca < 65521, cb < 65521;
        w == cb as u64 * 65536 + ca as u64
    }
}

proof fn lemma_trail_one(gz: bool, fed: Seq<u8>, h: int, a: int, bits: nat, st: bool, body: Seq<u8>, out: Seq<u8>, t: Seq<u8>, s: Seq<u8>)
    requires
        zhdr(gz, fed) == Some(h), 0 <= h <= fed.len(), pfx(body, fed.skip(h)),
        forall|f: Seq<bool>| #[trigger] is_prefix(lbits(body), f) ==> inflate_blocks(f, 0, Seq::empty(), true) == Some((out, bits as int, st)),
        a == h + (bits + 7) / 8, a + tl(gz) <= fed.len(), t == fed.subrange(a, a + tl(gz)),
        pfx(fed, s),
    ensures zdec(gz, s) == if trail_ok(gz, t, 0, out) { Some((out, a + tl(gz), st)) } else { None },
{
    hide(gzip_decode);
    hide(zlib_decode);
    hide(gzip_header);
    lemma_zhdr_ext(gz, fed, s);
    lemma_zdec(gz, s, h);
    lemma_body_pfx(fed, s, h, body);
    assert(inflate_blocks(lbits(s.skip(h)), 0, Seq::empty(), true) == Some((out, bits as int, st)));
    assert(inflate(lbits(s.skip(h))) == Some((out, bits, st)));
    assert(after_bits(h, bits) == a);
    assert forall|k: int| 0 <= k < tl(gz) implies #[trigger] s[a + k] == t[k] by {
        assert(s.take(fed.len() as int)[a + k] == s[a + k]);
    }
    assert(trail_ok(gz, s, a, out) == trail_ok(gz, t, 0, out)) by {
        assert(s[a] == t[0] && s[a + 1] == t[1] && s[a + 2] == t[2] && s[a + 3] == t[3]);
        if gz { assert(s[a + 4] == t[4] && s[a + 5] == t[5] && s[a + 6] == t[6] && s[a + 7] == t[7]); }
    }
}

/// The verdict once the whole trailer is in: every stream that starts with
/// the input decodes, or none does.
proof fn lemma_trail(gz: bool, fed: Seq<u8>, h: int, a: int, bits: nat, st: bool, body: Seq<u8>, out: Seq<u8>, t: Seq<u8>, ok: bool)
    requires
        zhdr(gz, fed) == Some(h), 0 <= h <= fed.len(), pfx(body, fed.skip(h)),
        forall|f: Seq<bool>| #[trigger] is_prefix(lbits(body), f) ==> inflate_blocks(f, 0, Seq::empty(), true) == Some((out, bits as int, st)),
        a == h + (bits + 7) / 8, a + tl(gz) <= fed.len(), t == fed.subrange(a, a + tl(gz)),
        ok == trail_ok(gz, t, 0, out),
    ensures
        ok ==> forall|s: Seq<u8>| #[trigger] pfx(fed, s) ==> zdec(gz, s) == Some((out, a + tl(gz), st)),
        !ok ==> forall|s: Seq<u8>| #[trigger] pfx(fed, s) ==> zdec(gz, s) is None,
{
    hide(gzip_decode);
    hide(zlib_decode);
    hide(gzip_header);
    hide(trail_ok);
    assert forall|s: Seq<u8>| #[trigger] pfx(fed, s) implies
        (ok ==> zdec(gz, s) == Some((out, a + tl(gz), st))) && (!ok ==> zdec(gz, s) is None) by {
        lemma_trail_one(gz, fed, h, a, bits, st, body, out, t, s);
    }
}

pub proof fn lemma_pfx_skip(x: Seq<u8>, fed: Seq<u8>, fed2: Seq<u8>, h: int)
    requires pfx(x, fed.skip(h)), pfx(fed, fed2), 0 <= h <= fed.len(),
    ensures pfx(x, fed2.skip(h)),
{
    assert(pfx(fed.skip(h), fed2.skip(h))) by {
        assert(fed2.skip(h).take(fed.len() - h) =~= fed.skip(h)) by {
            assert forall|k: int| 0 <= k < fed.len() - h implies #[trigger] fed2.skip(h).take(fed.len() - h)[k] == fed.skip(h)[k] by {
                assert(fed2.take(fed.len() as int)[h + k] == fed2[h + k]);
            }
        }
    }
    lemma_pfx_trans(x, fed.skip(h), fed2.skip(h));
}

/// Not yet a whole member: no header yet.
proof fn lemma_hdr_need(gz: bool, fed: Seq<u8>)
    requires zhdr(gz, fed) is None,
    ensures zdec(gz, fed) is None,
{
}

/// Not yet a whole member: the DEFLATE stream is not whole.
proof fn lemma_body_need(gz: bool, fed: Seq<u8>, h: int)
    requires zhdr(gz, fed) == Some(h), 0 <= h <= fed.len(), inflate_blocks(lbits(fed.skip(h)), 0, Seq::empty(), true) is None,
    ensures zdec(gz, fed) is None,
{
    hide(gzip_decode);
    hide(zlib_decode);
    hide(gzip_header);
    lemma_zdec(gz, fed, h);
}

/// Not yet a whole member: the trailer is not whole.
proof fn lemma_trail_need(gz: bool, fed: Seq<u8>, h: int, a: int, bits: nat, st: bool, body: Seq<u8>, out: Seq<u8>)
    requires
        zhdr(gz, fed) == Some(h), 0 <= h <= fed.len(), pfx(body, fed.skip(h)),
        forall|f: Seq<bool>| #[trigger] is_prefix(lbits(body), f) ==> inflate_blocks(f, 0, Seq::empty(), true) == Some((out, bits as int, st)),
        a == h + (bits + 7) / 8, a + tl(gz) > fed.len(),
    ensures zdec(gz, fed) is None,
{
    hide(gzip_decode);
    hide(zlib_decode);
    hide(gzip_header);
    lemma_zdec(gz, fed, h);
    assert(pfx(fed, fed)) by { assert(fed.take(fed.len() as int) =~= fed); }
    lemma_body_pfx(fed, fed, h, body);
}

/// The body decoder's failures are the whole stream's.
proof fn lemma_body_err(gz: bool, fed: Seq<u8>, h: int, body: Seq<u8>, limit: nat, e: Error, out: Seq<u8>)
    requires
        zhdr(gz, fed) == Some(h), 0 <= h <= fed.len(), pfx(body, fed.skip(h)),
        e == Error::Bad ==> forall|f: Seq<bool>| #[trigger] is_prefix(lbits(body), f) ==> inflate_blocks(f, 0, Seq::empty(), true) is None,
        e == Error::TooBig ==> forall|f: Seq<bool>| #[trigger] is_prefix(lbits(body), f) ==>
            (inflate_blocks(f, 0, Seq::empty(), true) matches Some((o, _, _)) ==> o.len() > limit),
    ensures zres_ok(gz, fed, out, limit, Err::<ZStatus, Error>(e)),
{
    hide(gzip_decode);
    hide(zlib_decode);
    hide(gzip_header);
    assert forall|s: Seq<u8>| #[trigger] pfx(fed, s) implies
        (e == Error::Bad ==> zdec(gz, s) is None)
        && (e == Error::TooBig ==> (zdec(gz, s) matches Some((o, _, _)) ==> o.len() > limit)) by {
        lemma_zhdr_ext(gz, fed, s);
        lemma_zdec(gz, s, h);
        lemma_body_pfx(fed, s, h, body);
    }
}


/// The checksums, continued over `sl`.
fn ck_update(gz: bool, tb: &[u32; 256], ca: u32, cb: u32, cc: u32, cn: u32, sl: &[u8], Ghost(w0): Ghost<Seq<u8>>)
    -> (r: (u32, u32, u32, u32))
    requires
        forall|i: int| 0 <= i < 256 ==> #[trigger] tb[i] == crc_byte(0, i as u8),
        cn as nat == w0.len() % 0x1_0000_0000,
        gz ==> cc == crc_run(0xFFFF_FFFF, w0),
        !gz ==> ca as nat == adler_a(w0) % 65521 && cb as nat == adler_b(w0) % 65521,
    ensures
        r.3 as nat == (w0 + sl@).len() % 0x1_0000_0000,
        gz ==> r.2 == crc_run(0xFFFF_FFFF, w0 + sl@),
        !gz ==> r.0 as nat == adler_a(w0 + sl@) % 65521 && r.1 as nat == adler_b(w0 + sl@) % 65521,
{
    let mut ca = ca;
    let mut cb = cb;
    let mut cc = cc;
    if gz {
        cc = crc_run_x(tb, cc, sl);
        proof { lemma_crc_run_append(0xFFFF_FFFF, w0, sl@); }
    } else {
        let (a2, b2) = adler_run_x(ca, cb, sl, Ghost(w0));
        ca = a2;
        cb = b2;
    }
    let k = (sl.len() as u64 % 0x1_0000_0000) as u32;
    let cn = ((cn as u64 + k as u64) % 0x1_0000_0000) as u32;
    proof { vstd::arithmetic::div_mod::lemma_add_mod_noop(w0.len() as int, sl@.len() as int, 0x1_0000_0000); }
    (ca, cb, cc, cn)
}

/// A stream that decodes from every extension of `fed`, but not from its
/// first `f0` bytes, ends in the bytes after them.
proof fn lemma_end_in_piece(fed: Seq<u8>, f0: nat, bits: nat, zlib: bool, w: Seq<u8>)
    requires
        f0 <= fed.len(),
        forall|f: Seq<bool>| #[trigger] is_prefix(lbits(fed), f) ==>
            inflate_blocks(f, 0, Seq::empty(), true) == Some((w, bits as int, zlib)),
        inflate_blocks(lbits(fed.take(f0 as int)), 0, Seq::empty(), true) is None,
    ensures f0 < (bits + 7) / 8 <= fed.len(),
{
    let g = lbits(fed);
    assert(is_prefix(g, g));
    crate::agree::lemma_blocks_pos(g, 0, Seq::empty(), true);
    assert(g.len() == 8 * fed.len());
    if (bits + 7) / 8 <= f0 {
        let t = fed.take(f0 as int);
        let g0 = lbits(t);
        assert(fed =~= t + fed.skip(f0 as int));
        crate::stream::lemma_lbits_prefix(t, fed.skip(f0 as int));
        assert(g0.len() == 8 * f0);
        lemma_prefix_agree(g0, g, 0, bits as int);
        crate::agree::lemma_blocks_agree(g0, g, 0, Seq::empty(), true);
    }
}

/// The DEFLATE stream has ended: take the trailer bytes that `piece` has.
#[verifier::spinoff_prover]
/// `run_body`'s end when the DEFLATE stream is not done: more input
/// wanted, or an error.
fn body_more(gz: bool, h: usize, inf2: Inflater, f1: usize, ca: u32, cb: u32, cc: u32, cn: u32, tb: [u32; 256],
             Ghost(fed): Ghost<Seq<u8>>, res: Result<Status, Error>) -> (r: (ZInflater, Result<ZStatus, Error>))
    requires
        inf2.inv(), f1 == inf2.fed().len(), fed.len() < max_input(),
        forall|i: int| 0 <= i < 256 ==> #[trigger] tb[i] == crc_byte(0, i as u8),
        cn as nat == inf2.whole().len() % 0x1_0000_0000,
        gz ==> cc == crc_run(0xFFFF_FFFF, inf2.whole()),
        !gz ==> ca as nat == adler_a(inf2.whole()) % 65521 && cb as nat == adler_b(inf2.whole()) % 65521,
        zhdr(gz, fed) == Some(h as int), h <= fed.len(), pfx(inf2.fed(), fed.skip(h as int)),
        res == Ok::<Status, Error>(Status::NeedMore) ==> fed.skip(h as int) == inf2.fed(),
        global_ok(&inf2, res), !(res matches Ok(Status::Done { .. })),
    ensures r.0.inv(), r.0.gz == gz, r.0.inf == inf2, r.0.fed@ == fed,
        zres_ok(gz, fed, inf2.whole(), inf2.limit as nat, r.1),
{
    hide(Inflater::inv);
    hide(gzip_decode);
    hide(zlib_decode);
    hide(gzip_header);
    let fed = Ghost(fed);
    match res {
        Ok(Status::NeedMore) => {
            proof { lemma_body_need(gz, fed@, h as int); }
            let d = ZInflater { gz, ph: ZPhase::Body { h }, hb: Vec::new(), inf: inf2, f0: f1, ca, cb, cc, cn, tb, fed };
            (d, Ok(ZStatus::NeedMore))
        }
        Err(e) => {
            proof { lemma_body_err(gz, fed@, h as int, inf2.fed(), inf2.limit as nat, e, inf2.whole()); }
            let d = ZInflater { gz, ph: ZPhase::Failed { e }, hb: Vec::new(), inf: inf2, f0: f1, ca, cb, cc, cn, tb, fed };
            (d, Err(e))
        }
        Ok(Status::Done { .. }) => {
            proof { assert(false); }
            let d = ZInflater { gz, ph: ZPhase::Failed { e: Error::Bad }, hb: Vec::new(), inf: inf2, f0: f1, ca, cb, cc, cn, tb, fed };
            (d, Err(Error::Bad))
        }
    }
}

fn body_done(gz: bool, h: usize, piece: &[u8], bits: usize, zlib: bool, inf2: Inflater, f0: usize,
             ca: u32, cb: u32, cc: u32, cn: u32, tb: [u32; 256], Ghost(fed): Ghost<Seq<u8>>) -> (r: (ZInflater, Result<ZStatus, Error>))
    requires
        inf2.inv(), f0 + piece@.len() == inf2.fed().len(), fed.len() < max_input(),
        forall|i: int| 0 <= i < 256 ==> #[trigger] tb[i] == crc_byte(0, i as u8),
        cn as nat == inf2.whole().len() % 0x1_0000_0000,
        gz ==> cc == crc_run(0xFFFF_FFFF, inf2.whole()),
        !gz ==> ca as nat == adler_a(inf2.whole()) % 65521 && cb as nat == adler_b(inf2.whole()) % 65521,
        zhdr(gz, fed) == Some(h as int), h <= fed.len(), fed.skip(h as int) == inf2.fed(),
        forall|f: Seq<bool>| #[trigger] is_prefix(lbits(inf2.fed()), f) ==>
            inflate_blocks(f, 0, Seq::empty(), true) == Some((inf2.whole(), bits as int, zlib)),
        inf2.fed().skip(f0 as int) == piece@,
        inflate_blocks(lbits(inf2.fed().take(f0 as int)), 0, Seq::empty(), true) is None,
    ensures r.0.inv(), r.0.gz == gz, r.0.inf == inf2, r.0.fed@ == fed,
        zres_ok(gz, fed, inf2.whole(), inf2.limit as nat, r.1),
{
    hide(Inflater::inv);
    hide(gzip_decode);
    hide(zlib_decode);
    hide(gzip_header);
    let f1 = f0 + piece.len();
    let fed = Ghost(fed);
    let ghost w1 = inf2.whole();
    proof { assert(pfx(inf2.fed(), fed@.skip(h as int))) by { assert(fed@.skip(h as int).take(inf2.fed().len() as int) =~= inf2.fed()); } }
    let len = bits / 8 + if bits % 8 != 0 { 1 } else { 0 };
    proof { assert(len == (bits + 7) / 8); }
    proof { lemma_end_in_piece(inf2.fed(), f0 as nat, bits as nat, zlib, inf2.whole()); }
    if len < f0 || len > f1 {
        proof { assert(false); }
        let d = ZInflater { gz, ph: ZPhase::Failed { e: Error::Bad }, hb: Vec::new(), inf: inf2, f0: f1, ca, cb, cc, cn, tb, fed };
        return (d, Err(Error::Bad));
    }
    let off = len - f0;
    let a = h + len;
    let tln: usize = if gz { 8 } else { 4 };
    let rem = piece.len() - off;
    let e = if rem >= tln { off + tln } else { piece.len() };
    let mut t: Vec<u8> = Vec::new();
    let mut j = off;
    while j < e
        invariant off <= j <= e, e <= piece@.len(), t@ == piece@.subrange(off as int, j as int),
        decreases e - j,
    {
        t.push(piece[j]);
        j = j + 1;
        proof { assert(t@ =~= piece@.subrange(off as int, j as int)); }
    }
    proof {
        assert forall|q: int| 0 <= q < t@.len() implies #[trigger] t@[q] == fed@[a + q] by {
            assert(fed@.skip(h as int)[f0 + off + q] == piece@[off + q]);
        }
        assert(fed@.len() == h + f1);
    }
    if rem >= tln {
        let ok = trail_check(gz, &t, ca, cb, cc, cn, Ghost(w1));
        proof {
            assert(t@ =~= fed@.subrange(a as int, a + tl(gz)));
            lemma_trail(gz, fed@, h as int, a as int, bits as nat, zlib, inf2.fed(), w1, t@, ok);
        }
        if ok {
            let n = a + tln;
            let d = ZInflater { gz, ph: ZPhase::Fin { n, st: zlib }, hb: Vec::new(), inf: inf2, f0: f1, ca, cb, cc, cn, tb, fed };
            (d, Ok(ZStatus::Done { n, zlib }))
        } else {
            let d = ZInflater { gz, ph: ZPhase::Failed { e: Error::Bad }, hb: Vec::new(), inf: inf2, f0: f1, ca, cb, cc, cn, tb, fed };
            (d, Err(Error::Bad))
        }
    } else {
        proof {
            assert(t@ =~= fed@.subrange(a as int, fed@.len() as int));
            lemma_trail_need(gz, fed@, h as int, a as int, bits as nat, zlib, inf2.fed(), w1);
        }
        let d = ZInflater { gz, ph: ZPhase::Trail { h, a, bits, st: zlib }, hb: t, inf: inf2, f0: f1, ca, cb, cc, cn, tb, fed };
        (d, Ok(ZStatus::NeedMore))
    }
}

impl ZInflater {
    pub open spec fn post(&self, d: &ZInflater, s0: Seq<u8>, s1: Seq<u8>, fed: Seq<u8>, r: Result<ZStatus, Error>) -> bool {
        &&& d.inv() && d.gz == self.gz && d.inf.limit == self.inf.limit && d.fed@ == fed
        &&& d.out().len() >= self.out().len() && d.out().take(self.out().len() as int) == self.out()
        &&& s1 == s0 + d.out().skip(self.out().len() as int)
        &&& zres_ok(d.gz, d.fed@, d.out(), d.inf.limit as nat, r)
    }

    /// Decode `piece`, the next of the DEFLATE stream after a header of `h`
    /// bytes; `fed` already has it.
    #[verifier::spinoff_prover]
    fn run_body(self, h: usize, piece: &[u8], sink: &mut Vec<u8>) -> (r: (ZInflater, Result<ZStatus, Error>))
        requires
            self.inf.inv(), self.f0 == self.inf.fed().len(), self.fed@.len() < max_input(),
            forall|i: int| 0 <= i < 256 ==> #[trigger] self.tb[i] == crc_byte(0, i as u8),
            self.ck_ok(), zhdr(self.gz, self.fed@) == Some(h as int), h <= self.fed@.len(),
            self.fed@.skip(h as int) == self.inf.fed() + piece@,
            inflate_blocks(lbits(self.inf.fed()), 0, Seq::empty(), true) is None,
        ensures self.post(&r.0, old(sink)@, final(sink)@, self.fed@, r.1),
    {
        hide(Inflater::inv);
        hide(gzip_decode);
        hide(zlib_decode);
        hide(gzip_header);
        let ghost s0 = self;
        proof { lemma_inv_len(&self.inf); }
        let ZInflater { gz, ph: _, hb: _, inf, f0, ca, cb, cc, cn, tb, fed } = self;
        let ghost w0 = inf.whole();
        let ghost bf0 = inf.fed();
        let ol = sink.len();
        proof { assert(inf.fed().len() + piece@.len() == fed@.skip(h as int).len()); }
        let (inf2, r) = inf.feed(piece, sink);
        let ghost w1 = inf2.whole();
        let sl = vstd::slice::slice_subrange(sink.as_slice(), ol, sink.len());
        proof {
            assert(sl@ =~= w1.skip(w0.len() as int));
            assert(w1 =~= w0 + sl@) by { assert(w1 =~= w1.take(w0.len() as int) + w1.skip(w0.len() as int)); }
        }
        let (ca, cb, cc, cn) = ck_update(gz, &tb, ca, cb, cc, cn, sl, Ghost(w0));
        let f1 = f0 + piece.len();
        proof {
            assert(inf2.fed() == bf0 + piece@);
            assert(inf2.fed().skip(f0 as int) =~= piece@);
            assert(pfx(inf2.fed(), fed@.skip(h as int))) by { assert(fed@.skip(h as int).take(inf2.fed().len() as int) =~= inf2.fed()); }
        }
        match r {
            Ok(Status::Done { bits, zlib }) => {
                proof { assert(inf2.fed().take(f0 as int) =~= bf0); }
                body_done(gz, h, piece, bits, zlib, inf2, f0, ca, cb, cc, cn, tb, Ghost(fed@))
            }
            _ => {
                proof { if r == Ok::<Status, Error>(Status::NeedMore) { assert(fed@.skip(h as int) == inf2.fed()); } }
                body_more(gz, h, inf2, f1, ca, cb, cc, cn, tb, Ghost(fed@), r)
            }
        }
    }
}

fn zlib_hdr_x(hb: &Vec<u8>) -> (r: Option<usize>)
    ensures match r { Some(h) => zhdr(false, hb@) == Some(h as int) && h <= hb@.len(), None => zhdr(false, hb@) is None },
{
    if hb.len() < 2 { return None; }
    let c = hb[0] as u64;
    let f = hb[1] as u64;
    if c % 16 != 8 || c / 16 > 7 || (c * 256 + f) % 31 != 0 || (f / 32) % 2 == 1 { None } else { Some(2) }
}

fn hdr_bad_x(gz: bool, hb: &Vec<u8>) -> (r: bool)
    ensures r == hdr_bad(gz, hb@),
{
    let n = hb.len();
    if gz {
        (n >= 1 && hb[0] != 0x1f) || (n >= 2 && hb[1] != 0x8b) || (n >= 3 && hb[2] != 8) || (n >= 4 && hb[3] / 32 != 0)
    } else {
        if n < 2 { return false; }
        let c = hb[0] as u64;
        let f = hb[1] as u64;
        c % 16 != 8 || c / 16 > 7 || (c * 256 + f) % 31 != 0 || (f / 32) % 2 == 1
    }
}

impl ZInflater {
    #[verifier::spinoff_prover]
    fn hdr_feed(self, chunk: &[u8], sink: &mut Vec<u8>) -> (r: (ZInflater, Result<ZStatus, Error>))
        requires self.inv(), self.ph == ZPhase::Hdr, self.fed@.len() + chunk@.len() < max_input(),
        ensures self.post(&r.0, old(sink)@, final(sink)@, self.fed@ + chunk@, r.1),
    {
        hide(Inflater::inv);
        hide(gzip_decode);
        hide(zlib_decode);
        let ghost s0 = self;
        let ZInflater { gz, ph: _, hb, inf, f0, ca, cb, cc, cn, tb, fed } = self;
        let ghost fed2 = fed@ + chunk@;
        let mut hb = hb;
        let mut i: usize = 0;
        while i < chunk.len()
            invariant i <= chunk@.len(), hb@ == fed@ + chunk@.take(i as int),
            decreases chunk@.len() - i,
        {
            hb.push(chunk[i]);
            i = i + 1;
            proof { assert(hb@ =~= fed@ + chunk@.take(i as int)); }
        }
        proof { assert(chunk@.take(chunk@.len() as int) =~= chunk@); }
        let hopt = if gz { gzip_header_x(&tb, hb.as_slice()) } else { zlib_hdr_x(&hb) };
        match hopt {
            Some(h) => {
                let piece = vstd::slice::slice_subrange(hb.as_slice(), h, hb.len());
                let d0 = ZInflater { gz, ph: ZPhase::Hdr, hb: Vec::new(), inf, f0, ca, cb, cc, cn, tb, fed: Ghost(fed2) };
                proof {
                    assert(inf.fed().len() == 0);
                    assert(fed2.skip(h as int) =~= d0.inf.fed() + piece@);
                    assert(lbits(d0.inf.fed()) =~= Seq::<bool>::empty());
                }
                d0.run_body(h, piece, sink)
            }
            None => {
                if hdr_bad_x(gz, &hb) {
                    proof {
                        assert forall|s: Seq<u8>| #[trigger] pfx(fed2, s) implies zdec(gz, s) is None by {
                            lemma_hdr_bad(gz, fed2, s);
                        }
                    }
                    let d = ZInflater { gz, ph: ZPhase::Failed { e: Error::Bad }, hb, inf, f0, ca, cb, cc, cn, tb, fed: Ghost(fed2) };
                    proof { assert(d.out().take(s0.out().len() as int) =~= s0.out()); assert(d.out().skip(s0.out().len() as int) =~= Seq::<u8>::empty()); }
                    (d, Err(Error::Bad))
                } else {
                    proof { lemma_hdr_need(gz, fed2); }
                    let d = ZInflater { gz, ph: ZPhase::Hdr, hb, inf, f0, ca, cb, cc, cn, tb, fed: Ghost(fed2) };
                    proof { assert(d.out().take(s0.out().len() as int) =~= s0.out()); assert(d.out().skip(s0.out().len() as int) =~= Seq::<u8>::empty()); }
                    (d, Ok(ZStatus::NeedMore))
                }
            }
        }
    }

    #[verifier::spinoff_prover]
    fn trail_feed(self, chunk: &[u8], h: usize, a: usize, bits: usize, st: bool) -> (r: (ZInflater, Result<ZStatus, Error>))
        requires self.inv(), self.ph == (ZPhase::Trail { h, a, bits, st }), self.fed@.len() + chunk@.len() < max_input(),
        ensures r.0.inf == self.inf, self.post(&r.0, Seq::empty(), Seq::empty(), self.fed@ + chunk@, r.1),
    {
        hide(Inflater::inv);
        hide(gzip_decode);
        hide(zlib_decode);
        hide(gzip_header);
        let ghost s0 = self;
        let ZInflater { gz, ph: _, hb, inf, f0, ca, cb, cc, cn, tb, fed } = self;
        let ghost fed2 = fed@ + chunk@;
        proof {
            lemma_pfx_app(fed@, chunk@);
            lemma_zhdr_ext(gz, fed@, fed2);
            lemma_pfx_skip(inf.fed(), fed@, fed2, h as int);
        }
        let tln: usize = if gz { 8 } else { 4 };
        let need = tln - hb.len();
        let take = if chunk.len() < need { chunk.len() } else { need };
        let mut hb = hb;
        let ghost hb0 = hb@;
        let mut i: usize = 0;
        while i < take
            invariant i <= take, take <= chunk@.len(), hb@ == hb0 + chunk@.take(i as int),
            decreases take - i,
        {
            hb.push(chunk[i]);
            i = i + 1;
            proof { assert(hb@ =~= hb0 + chunk@.take(i as int)); }
        }
        proof {
            assert(hb@ =~= fed2.subrange(a as int, a + hb@.len())) by {
                assert forall|q: int| 0 <= q < hb@.len() implies #[trigger] hb@[q] == fed2[a + q] by {
                    if q < hb0.len() { assert(hb0[q] == fed@[a + q]); } else { assert(chunk@[q - hb0.len()] == fed2[fed@.len() + (q - hb0.len())]); }
                }
            }
        }
        let d_out = Ghost(inf.whole());
        // the phase and verdict first, then one decoder state for all three
        let (ph, res) = if hb.len() == tln {
            let ok = trail_check(gz, &hb, ca, cb, cc, cn, d_out);
            proof { lemma_trail(gz, fed2, h as int, a as int, bits as nat, st, inf.fed(), inf.whole(), hb@, ok); }
            if ok {
                let n = a + tln;
                (ZPhase::Fin { n, st }, Ok(ZStatus::Done { n, zlib: st }))
            } else {
                (ZPhase::Failed { e: Error::Bad }, Err(Error::Bad))
            }
        } else {
            proof {
                assert(hb@ =~= fed2.subrange(a as int, fed2.len() as int));
                lemma_trail_need(gz, fed2, h as int, a as int, bits as nat, st, inf.fed(), inf.whole());
            }
            (ZPhase::Trail { h, a, bits, st }, Ok(ZStatus::NeedMore))
        };
        let d = ZInflater { gz, ph, hb, inf, f0, ca, cb, cc, cn, tb, fed: Ghost(fed2) };
        proof { assert(d.out().take(s0.out().len() as int) =~= s0.out()); assert(d.out().skip(s0.out().len() as int) =~= Seq::<u8>::empty()); }
        (d, res)
    }

    /// Take the next piece of input, sending the output it finishes to
    /// `sink`. The verdict is on every stream that starts with all the input
    /// so far: `Done { n }`, each is a zlib stream (gzip member) of all the
    /// output, `n` bytes long; `Bad`, none is; `TooBig`, each that is has more
    /// output than the limit; `NeedMore`, nothing yet.
    pub fn feed(self, chunk: &[u8], sink: &mut Vec<u8>) -> (r: (ZInflater, Result<ZStatus, Error>))
        requires self.inv(), self.fed@.len() + chunk@.len() < max_input(),
        ensures self.post(&r.0, old(sink)@, final(sink)@, self.fed@ + chunk@, r.1),
    {
        hide(Inflater::inv);
        hide(gzip_decode);
        hide(zlib_decode);
        hide(gzip_header);
        let ghost fed2 = self.fed@ + chunk@;
        proof { lemma_pfx_app(self.fed@, chunk@); }
        let ph = self.ph;
        match ph {
            ZPhase::Hdr => self.hdr_feed(chunk, sink),
            ZPhase::Body { h } => {
                let mut d = self;
                proof {
                    lemma_zhdr_ext(d.gz, d.fed@, fed2);
                    assert(fed2.skip(h as int) =~= d.fed@.skip(h as int) + chunk@);
                }
                d.fed = Ghost(fed2);
                d.run_body(h, chunk, sink)
            }
            ZPhase::Trail { h, a, bits, st } => {
                let ghost s1 = sink@;
                let (d, r) = self.trail_feed(chunk, h, a, bits, st);
                proof { assert(sink@ =~= sink@ + d.out().skip(self.out().len() as int)); }
                (d, r)
            }
            _ => {
                let mut d = self;
                let ghost g0 = d.fed@;
                d.fed = Ghost(fed2);
                let r = match ph {
                    ZPhase::Fin { n, st } => Ok(ZStatus::Done { n, zlib: st }),
                    ZPhase::Failed { e } => Err(e),
                    _ => Err(Error::Bad),  // (not reached)
                };
                proof {
                    lemma_zres_ext(d.gz, g0, fed2, d.out(), d.inf.limit as nat, r);
                    assert(d.out().take(self.out().len() as int) =~= self.out());
                    assert(sink@ =~= sink@ + d.out().skip(self.out().len() as int));
                }
                (d, r)
            }
        }
    }
}

} // verus!
