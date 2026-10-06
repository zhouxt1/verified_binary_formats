//! Streaming compression in bounded memory.
//!
//! `Deflater::feed` takes the input a piece at a time and returns the output
//! it has finished; `finish` ends the stream. Between calls it keeps the last
//! 32K to 64K of input it has compressed (as far back as a match reaches, and
//! a little more so that it slides seldom), what it has not compressed yet
//! (at most 64K and a match's length), the hash chains, and less than a byte
//! of output. The theorem: all the output, in order, is a DEFLATE stream of
//! all the input, as `deflate` gives (`deflate_ok`).
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // spec-only: erased from a plain build
use crate::spec::*;
use crate::step::*;
use crate::inflate::*;
use crate::enc::*;
use crate::enc2::*;
use crate::wrap::*;
#[cfg(verus_keep_ghost)]
use vbits::lsb::*;

verus! {

/// Input taken before a block is compressed, beyond the block's lookahead.
pub open spec fn blk_in() -> nat { 65536 }

/// The most input kept between calls.
pub open spec fn win_max() -> nat { 2 * 65536 + 258 }

pub struct Deflater {
    win: Vec<u8>,
    cur: usize,
    ch: Box<Chains>,
    w: BitW,
    lv: Level,
    tabs: SymTabs,
    fl: EncCode,
    fd: EncCode,
    base: Ghost<int>,
    all: Ghost<Seq<u8>>,
    st: Ghost<bool>,
}

/// A token right for the window is right for the whole input.
proof fn lemma_tok_lift(win: Seq<u8>, all: Seq<u8>, base: int, i: int, t: Tok)
    requires 0 <= base <= all.len(), win == all.subrange(base, all.len() as int), tok_ok(win, i, t),
    ensures tok_ok(all, base + i, t),
{
    if t.len != 0 {
        assert forall|j: int| 0 <= j < t.len implies #[trigger] all[base + i + j] == all[base + i + j - t.dist] by {
            assert(win[i + j] == win[i + j - t.dist]);
            assert(all[base + (i + j)] == win[i + j]);
            assert(all[base + (i + j - t.dist)] == win[i + j - t.dist]);
        }
    }
}

proof fn lemma_toks_lift(win: Seq<u8>, all: Seq<u8>, base: int, toks: Seq<Tok>, pos: Seq<int>)
    requires 0 <= base <= all.len(), win == all.subrange(base, all.len() as int), toks_ok(win, toks, pos),
    ensures toks_ok(all, toks, Seq::new(pos.len(), |k: int| pos[k] + base)),
{
    let pa = Seq::new(pos.len(), |k: int| pos[k] + base);
    assert forall|k: int| 0 <= k < toks.len() implies
        tok_ok(all, pa[k], #[trigger] toks[k]) && pa[k + 1] == pa[k] + tok_len(toks[k]) by {
        assert(tok_ok(win, pos[k], toks[k]));
        lemma_tok_lift(win, all, base, pos[k], toks[k]);
    }
}

/// The input so far decodes up to `i` from where the bits are.
proof fn lemma_str_inv_ext(w: Seq<bool>, a: Seq<u8>, a2: Seq<u8>, i: int, st: bool)
    requires str_inv(w, a, i, st), 0 <= i <= a.len(), a.len() <= a2.len(), a2.take(a.len() as int) == a,
    ensures str_inv(w, a2, i, st),
{
    assert forall|j: int| 0 <= j < i implies #[trigger] a2.take(i)[j] == a.take(i)[j] by {
        assert(a2.take(a.len() as int)[j] == a[j]);
    }
    assert(a2.take(i) =~= a.take(i));
}

impl Deflater {
    /// The input so far.
    pub closed spec fn input(&self) -> Seq<u8> { self.all@ }

    /// The output so far.
    pub closed spec fn output(&self) -> Seq<u8> { self.w.pre@ }

    /// The input kept.
    pub closed spec fn kept(&self) -> nat { self.win@.len() }

    pub closed spec fn inv(&self) -> bool {
        self.inv_at(win_max(), 65536)
    }

    /// The window holds at most `wmax` bytes, `cur` is at most `cmax`.
    closed spec fn inv_at(&self, wmax: nat, cmax: nat) -> bool {
        &&& 0 <= self.base@ <= self.all@.len()
        &&& self.win@ == self.all@.subrange(self.base@, self.all@.len() as int)
        &&& self.cur <= self.win@.len() <= wmax && self.cur <= cmax && wmax <= 0x100_0000
        &&& self.w.wf() && self.w.buf@.len() == 0
        &&& str_inv(self.w.bits(), self.all@, self.base@ + self.cur, self.st@) && self.st@
        &&& level_ok(self.lv) && tabs_wf(&self.tabs)
        &&& enc_ok(&self.fl, fixed_lit()) && enc_ok(&self.fd, fixed_dist())
    }

    /// The input kept, in bytes.
    pub fn kept_bytes(&self) -> (n: usize)
        ensures n == self.kept(),
    {
        self.win.len()
    }

    /// A compressor at `lv` (see `level`).
    pub fn new(lv: Level) -> (r: Option<Deflater>)
        requires level_ok(lv),
        ensures r matches Some(d) ==> d.inv() && d.input().len() == 0 && d.output().len() == 0,
    {
        let fl = match enc_code(fixed_lit_x()) { None => return None, Some(c) => c };
        let fd = match enc_code(fixed_dist_x()) { None => return None, Some(c) => c };
        let w = bw_new();
        let d = Deflater {
            win: Vec::new(), cur: 0, ch: chains_new(), w, lv,
            tabs: sym_tabs(), fl, fd, base: Ghost(0), all: Ghost(Seq::empty()), st: Ghost(true),
        };
        proof {
            assert(d.win@ =~= d.all@.subrange(0, 0));
            assert forall|b: Seq<bool>| #[trigger] is_prefix(d.w.bits(), b) implies
                inflate_blocks(b, 0, Seq::empty(), true) == inflate_blocks(b, d.w.bits().len() as int, d.all@.take(0), true) by {
                assert(d.all@.take(0) =~= Seq::<u8>::empty());
            }
        }
        Some(d)
    }

    /// Compress blocks while a whole one and its lookahead are there, sending
    /// the bytes they finish to `out`; slide the window as it goes.
    fn run(&mut self, out: &mut Vec<u8>)
        requires old(self).inv_at(win_max() + 65536, 65536),
        ensures final(self).inv(), final(self).all@ == old(self).all@,
            old(self).w.pre@ + final(out)@.skip(old(out)@.len() as int) == final(self).w.pre@,
            final(out)@.len() >= old(out)@.len(), final(out)@.take(old(out)@.len() as int) == old(out)@,
    {
        let ghost pre0 = self.w.pre@;
        let ghost out0 = out@;
        while self.win.len() - self.cur > 65536 + 258
            invariant
                self.inv_at(win_max() + 65536, 65536), self.all@ == old(self).all@,
                pre0 == old(self).w.pre@, out0 == old(out)@,
                out@.len() >= out0.len(), out@.take(out0.len() as int) == out0,
                pre0 + out@.skip(out0.len() as int) == self.w.pre@,
            decreases self.all@.len() - self.base@ - self.cur,
        {
            let end = self.win.len() - 258;
            let ghost win = self.win@;
            let ghost all = self.all@;
            let ghost base = self.base@;
            let ghost i0 = base + self.cur;
            let (toks, i1, Ghost(pos)) = tokenize(&self.win, self.cur, end, &mut self.ch, self.lv, &self.tabs);
            proof { lemma_toks_lift(win, all, base, toks@, pos); }
            let ghost pa = Seq::new(pos.len(), |k: int| pos[k] + base);
            let src = vstd::slice::slice_subrange(self.win.as_slice(), self.cur, i1);
            proof { assert(src@ =~= all.subrange(i0, i1 + base)); }
            let g = put_block(&mut self.w, &self.fl, &self.fd, &toks, Ghost(pa), src, Ghost(all), Ghost(i0), false, Ghost(self.st@));
            self.st = g;
            self.cur = i1;
            let ghost pw = self.w.pre@;
            let mut bytes = flush(&mut self.w);
            let ghost ob = out@;
            let ghost bb = bytes@;
            out.append(&mut bytes);
            proof {
                assert(out@ == ob + bb);
                assert(out@.take(out0.len() as int) =~= out0) by { assert(ob.take(out0.len() as int) == out0); }
                assert(out@.skip(out0.len() as int) =~= ob.skip(out0.len() as int) + bb);
                assert(pw == pre0 + ob.skip(out0.len() as int));
                assert(self.w.pre@ == pw + bb);
                assert(pre0 + out@.skip(out0.len() as int) =~= self.w.pre@);
            }
            if self.cur > 65536 {
                self.slide();
            }
        }
    }

    /// Drop input from the front of the window, a multiple of 32K, keeping
    /// at least 32K before `cur`; the chains move with it.
    fn slide(&mut self)
        requires old(self).inv_at(win_max() + 65536, win_max() + 65536), old(self).cur > 65536,
        ensures final(self).inv_at(win_max() + 65536, 65536), final(self).all@ == old(self).all@,
            final(self).w == old(self).w, final(self).st == old(self).st,
            final(self).base@ + final(self).cur == old(self).base@ + old(self).cur,
    {
        let mut sh: usize = 0;
        while self.cur - sh > 65536
            invariant sh + 65536 < self.cur + 32768, self.cur <= 0x100_0000,
            decreases self.cur - sh,
        {
            sh = sh + 32768;
        }
        let n = self.win.len();
        let mut nw: Vec<u8> = Vec::with_capacity(n - sh);
        let mut k: usize = sh;
        while k < n
            invariant sh <= k <= n, n == self.win@.len(), nw@ == self.win@.subrange(sh as int, k as int),
            decreases n - k,
        {
            nw.push(self.win[k]);
            k = k + 1;
            proof { assert(nw@ =~= self.win@.subrange(sh as int, k as int)); }
        }
        let mut j: usize = 0;
        while j < 32768
            invariant j <= 32768, sh < 0x1_0000_0000,
            decreases 32768 - j,
        {
            let h = self.ch.head[j] as usize;
            self.ch.head[j] = if h > sh { (h - sh) as u32 } else { 0 };
            let p = self.ch.prev[j] as usize;
            self.ch.prev[j] = if p > sh { (p - sh) as u32 } else { 0 };
            let t = self.ch.head3[j] as usize;
            self.ch.head3[j] = if t > sh { (t - sh) as u32 } else { 0 };
            j = j + 1;
        }
        proof {
            assert(nw@ =~= self.all@.subrange(self.base@ + sh, self.all@.len() as int));
        }
        self.win = nw;
        self.base = Ghost(self.base@ + sh);
        self.cur = self.cur - sh;
    }

    /// Take the next piece of input; the bytes returned continue the output.
    pub fn feed(&mut self, chunk: &[u8]) -> (out: Vec<u8>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).input() == old(self).input() + chunk@,
            final(self).output() == old(self).output() + out@, final(self).kept() <= win_max(),
    {
        let mut out: Vec<u8> = Vec::new();
        let mut k: usize = 0;
        let ghost all0 = self.all@;
        let ghost pre0 = self.w.pre@;
        while k < chunk.len()
            invariant
                k <= chunk@.len(), self.inv(), self.all@ == all0 + chunk@.take(k as int),
                pre0 + out@ == self.w.pre@,
            decreases chunk@.len() - k,
        {
            // up to 64K at a time, so that the window stays bounded
            let e = if chunk.len() - k > 65536 { k + 65536 } else { chunk.len() };
            let ghost k0 = k;
            while k < e
                invariant
                    k0 <= k <= e, e <= chunk@.len(), e - k0 <= 65536, self.all@ == all0 + chunk@.take(k as int),
                    self.inv_at((win_max() + (k - k0)) as nat, 65536),
                decreases e - k,
            {
                let ghost aw = self.all@;
                self.win.push(chunk[k]);
                self.all = Ghost(self.all@.push(chunk[k as int]));
                k = k + 1;
                proof {
                    assert(self.all@ =~= all0 + chunk@.take(k as int));
                    assert(self.win@ =~= self.all@.subrange(self.base@, self.all@.len() as int));
                    assert(self.all@.take(aw.len() as int) =~= aw);
                    lemma_str_inv_ext(self.w.bits(), aw, self.all@, self.base@ + self.cur, self.st@);
                }
            }
            let ghost ol = out@.len();
            let ghost ob = out@;
            self.run(&mut out);
            proof {
                assert(out@ =~= ob + out@.skip(ol as int)) by {
                    assert(out@.take(ol as int) == ob);
                    assert(out@ =~= out@.take(ol as int) + out@.skip(ol as int));
                }
                assert(pre0 + out@ =~= self.w.pre@);
            }
        }
        proof {
            assert(chunk@.take(chunk@.len() as int) =~= chunk@);
        }
        out
    }

    /// End the stream: the bytes returned end the output.
    pub fn finish(self) -> (out: Vec<u8>)
        requires self.inv(),
        ensures deflate_ok(self.input(), self.output() + out@),
    {
        let mut s = self;
        let ghost all = s.all@;
        let ghost base = s.base@;
        let ghost win = s.win@;
        let ghost pre = s.w.pre@;
        let n = s.win.len();
        let mut done = false;
        while !done
            invariant
                s.win@ == win, win == all.subrange(base, all.len() as int), 0 <= base <= all.len(), n == win.len(),
                n <= win_max(), s.cur <= n, s.w.wf(), s.w.pre@ == pre,
                s.w.buf@.len() <= 3500 * s.cur + (if done { 3500int } else { 0int }),
                level_ok(s.lv) && tabs_wf(&s.tabs),
                enc_ok(&s.fl, fixed_lit()) && enc_ok(&s.fd, fixed_dist()),
                !done ==> str_inv(s.w.bits(), all, base + s.cur, s.st@), s.st@,
                done ==> str_after(s.w.bits(), all, all.len() as int, s.st@, true),
            decreases 2 * (n - s.cur) + if done { 0int } else { 1int },
        {
            if s.cur == n {
                let toks: Vec<Tok> = Vec::new();
                let ghost p0: Seq<int> = seq![base + s.cur];
                let src = vstd::slice::slice_subrange(s.win.as_slice(), s.cur, s.cur);
                proof { assert(src@ =~= all.subrange(base + s.cur, base + s.cur)); }
                let g = put_block(&mut s.w, &s.fl, &s.fd, &toks, Ghost(p0), src, Ghost(all), Ghost(base + s.cur), true, Ghost(s.st@));
                s.st = g;
                done = true;
            } else {
                let ghost i0 = base + s.cur;
                let (toks, i1, Ghost(pos)) = tokenize(&s.win, s.cur, n, &mut s.ch, s.lv, &s.tabs);
                proof {
                    lemma_toks_lift(win, all, base, toks@, pos);
                    lemma_toks_len(win, toks@, pos, toks@.len() as int);
                }
                let ghost pa = Seq::new(pos.len(), |k: int| pos[k] + base);
                let last = i1 == n;
                let src = vstd::slice::slice_subrange(s.win.as_slice(), s.cur, i1);
                proof { assert(src@ =~= all.subrange(i0, i1 + base)); }
                let g = put_block(&mut s.w, &s.fl, &s.fd, &toks, Ghost(pa), src, Ghost(all), Ghost(i0), last, Ghost(s.st@));
                s.st = g;
                s.cur = i1;
                if last {
                    done = true;
                }
            }
        }
        let ghost wf = s.w.bits();
        let ghost st = s.st@;
        let out = finish(s.w);
        proof {
            let o = pre + out@;
            assert(all.take(all.len() as int) =~= all);
            let q = wf.len();
            assert forall|b: Seq<bool>| #[trigger] is_prefix(lbits(o), b) implies inflate(b) == Some((all, q, st)) by {
                lemma_prefix_trans_b(wf, lbits(o), b);
                assert(inflate_blocks(b, 0, Seq::empty(), true) == Some((all.take(all.len() as int), wf.len() as int, st)));
            }
            assert(inflate_q(o, q, st));
        }
        out
    }
}

/// Streaming compression into a zlib stream (`gz` false) or a gzip member.
pub struct ZDeflater {
    d: Deflater,
    gz: bool,
    a: u32,
    b: u32,
    c: u32,
    n: u32,
    tb: [u32; 256],
    hdr: Ghost<Seq<u8>>,
}

pub open spec fn zl_hdr() -> Seq<u8> { seq![0x78u8, 0x01u8] }

fn push_gz_tail(out: &mut Vec<u8>, c: u32, z: u32)
    ensures final(out)@ == old(out)@ + gz_tail(c, z),
{
    out.push(c as u8); out.push((c >> 8) as u8); out.push((c >> 16) as u8); out.push((c >> 24) as u8);
    out.push(z as u8); out.push((z >> 8) as u8); out.push((z >> 16) as u8); out.push((z >> 24) as u8);
    proof { assert(final(out)@ =~= old(out)@ + gz_tail(c, z)); }
}

fn push_zl_tail(out: &mut Vec<u8>, a: u32)
    ensures final(out)@ == old(out)@ + zl_tail(a),
{
    out.push((a >> 24) as u8); out.push((a >> 16) as u8); out.push((a >> 8) as u8); out.push(a as u8);
    proof { assert(final(out)@ =~= old(out)@ + zl_tail(a)); }
}

/// The Adler-32 word from its two reduced sums.
fn adler_word(a: u32, b: u32, Ghost(data): Ghost<Seq<u8>>) -> (r: u32)
    requires a as nat == adler_a(data) % 65521, b as nat == adler_b(data) % 65521,
    ensures r as nat == adler32(data),
{
    assert(b as u64 * 65536 + a as u64 <= 65520 * 65536 + 65520) by (nonlinear_arith) requires a < 65521, b < 65521;
    (b as u64 * 65536 + a as u64) as u32
}

impl ZDeflater {
    pub closed spec fn input(&self) -> Seq<u8> { self.d.input() }

    pub closed spec fn output(&self) -> Seq<u8> { self.hdr@ + self.d.output() }

    pub closed spec fn is_gzip(&self) -> bool { self.gz }

    pub closed spec fn inv(&self) -> bool {
        &&& self.d.inv()
        &&& self.a as nat == adler_a(self.d.input()) % 65521 && self.b as nat == adler_b(self.d.input()) % 65521
        &&& self.c == crc_run(0xFFFF_FFFF, self.d.input())
        &&& self.n as nat == self.d.input().len() % 0x1_0000_0000
        &&& forall|i: int| 0 <= i < 256 ==> #[trigger] self.tb[i] == crc_byte(0, i as u8)
        &&& self.hdr@ == if self.gz { gz_hdr() } else { zl_hdr() }
    }

    /// A compressor at `lv`, and the header bytes that start the output.
    pub fn new(lv: Level, gz: bool) -> (r: Option<(ZDeflater, Vec<u8>)>)
        requires level_ok(lv),
        ensures r matches Some((z, h)) ==> z.inv() && z.input().len() == 0 && z.output() == h@ && z.is_gzip() == gz,
    {
        let d = match Deflater::new(lv) { None => return None, Some(d) => d };
        let mut h: Vec<u8> = Vec::new();
        if gz {
            h.push(0x1f); h.push(0x8b); h.push(8); h.push(0); h.push(0);
            h.push(0); h.push(0); h.push(0); h.push(0); h.push(0xff);
        } else {
            h.push(0x78); h.push(0x01);
        }
        let ghost hs = h@;
        let z = ZDeflater { d, gz, a: 1, b: 0, c: 0xFFFF_FFFF, n: 0, tb: crc_table(), hdr: Ghost(hs) };
        proof {
            if gz { assert(h@ =~= gz_hdr()); } else { assert(h@ =~= zl_hdr()); }
            assert(z.d.output() =~= Seq::<u8>::empty());
            assert(z.output() =~= h@);
        }
        Some((z, h))
    }

    /// Take the next piece of input; the bytes returned continue the output.
    pub fn feed(&mut self, chunk: &[u8]) -> (out: Vec<u8>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).input() == old(self).input() + chunk@,
            final(self).output() == old(self).output() + out@, final(self).is_gzip() == old(self).is_gzip(),
    {
        let ghost p = self.d.input();
        let (a, b) = adler_run_x(self.a, self.b, chunk, Ghost(p));
        self.a = a;
        self.b = b;
        let c = crc_run_x(&self.tb, self.c, chunk);
        proof { lemma_crc_run_append(0xFFFF_FFFF, p, chunk@); }
        self.c = c;
        let k = (chunk.len() as u64 % 0x1_0000_0000) as u32;
        let n2 = ((self.n as u64 + k as u64) % 0x1_0000_0000) as u32;
        proof {
            vstd::arithmetic::div_mod::lemma_add_mod_noop(p.len() as int, chunk@.len() as int, 0x1_0000_0000);
        }
        self.n = n2;
        let out = self.d.feed(chunk);
        proof {
            assert(self.hdr@ + self.d.output() =~= (self.hdr@ + old(self).d.output()) + out@);
        }
        out
    }

    /// End the stream: the bytes returned end the output, a zlib stream (or
    /// gzip member) of all the input that takes all of the output.
    #[verifier::spinoff_prover]
    pub fn finish(self) -> (out: Vec<u8>)
        requires self.inv(),
        ensures
            self.is_gzip() ==> (gzip_decode(self.output() + out@) matches Some((d, n, z))
                && d == self.input() && n == (self.output() + out@).len() && z),
            !self.is_gzip() ==> (zlib_decode(self.output() + out@) matches Some((d, n, z))
                && d == self.input() && n == (self.output() + out@).len() && z),
    {
        hide(zlib_decode);
        hide(gzip_decode);
        hide(inflate);
        let ghost data = self.d.input();
        let ghost pre = self.d.output();
        let ghost hdr = self.hdr@;
        let gz = self.gz;
        let ad = adler_word(self.a, self.b, Ghost(data));
        let c = self.c ^ 0xFFFF_FFFF;
        let z = self.n;
        let mut out = self.d.finish();
        let ghost body = pre + out@;
        if gz {
            push_gz_tail(&mut out, c, z);
            proof {
                let o = hdr + (pre + out@);
                assert(pre + out@ =~= body + gz_tail(c, z));
                lemma_gzip_out(data, body, c, z, o);
                assert(hdr + pre + out@ =~= o);
            }
        } else {
            push_zl_tail(&mut out, ad);
            proof {
                let o = hdr + (pre + out@);
                assert(pre + out@ =~= body + zl_tail(ad));
                assert(o =~= seq![0x78u8, 0x01u8] + (body + seq![(ad >> 24) as u8, (ad >> 16) as u8, (ad >> 8) as u8, ad as u8]));
                lemma_zlib_out(data, body, ad, o);
                assert(hdr + pre + out@ =~= o);
            }
        }
        out
    }
}

} // verus!
