//! Decoding a stream NAL unit by NAL unit, each against the parameter sets
//! before it. The NAL unit itself is decoded by vh26x's verified functions
//! (`decode_nal_x`, `decode_rbsp_x`, `decode_pre`); this keeps the parameter
//! sets, and chooses the program and its context for each NAL unit.
use vh26x::raw::RawProg;
use vh26x::xir::ProgX;
use vh26x::xdec::{decode_all, decode_pre, ParsedX};
use vh26x::xenc::encode_pre;
use vh26x::nal::{decode_nal_x, decode_rbsp_x, encode_nal_x, encode_rbsp_x};
use crate::names;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Kind {
    /// Decoded by a program: a whole RBSP, or a slice header before its data.
    Parsed,
    /// A NAL unit type vh26x keeps as bytes (reserved, unspecified, or an
    /// extension it does not decode).
    Raw,
    Rejected,
    /// A PPS whose SPS has not arrived: it is decoded when a slice
    /// activates it, against the SPS then (H.264 7.4.1.2.1, H.265 7.4.2.4.2).
    Deferred,
}

pub struct Unit {
    pub nal_type: u32,
    pub kind: Kind,
    pub why: &'static str,
    pub prog: Option<&'static RawProg>,
    pub px: Option<ParsedX>,
    pub ctx: Vec<Vec<i64>>,
    /// For a slice: how many bits of the RBSP the header took.
    pub hdr_bits: Option<usize>,
    pub hdr: Vec<u8>,
    pub rbsp: Vec<u8>,
}

impl Unit {
    fn new(nal_type: u32) -> Unit {
        Unit { nal_type, kind: Kind::Rejected, why: "", prog: None, px: None, ctx: vec![], hdr_bits: None, hdr: vec![], rbsp: vec![] }
    }
    fn reject(mut self, why: &'static str) -> Unit { self.kind = Kind::Rejected; self.why = why; self }

    pub fn conf(&self) -> bool { self.px.as_ref().map(|p| p.conf).unwrap_or(true) }
}

/// A PPS as received: decoded against its SPS when it is activated.
#[derive(Clone)]
pub struct PpsEntry {
    pub rbsp: Vec<u8>,
    pub nal: Vec<i64>,
    pub sps_id: usize,
    /// The SPS generation it was last decoded against, and the result.
    cache: Option<(u64, Option<Vec<i64>>)>,
}

impl PpsEntry {
    fn env(&mut self, p: &Prog, sps: &[i64], gen: u64) -> Option<Vec<i64>> {
        if let Some((g, r)) = &self.cache {
            if *g == gen { return r.clone(); }
        }
        let r = rbsp_all(p, &vec![self.nal.clone(), sps.to_vec()], &self.rbsp).map(|px| px.env);
        self.cache = Some((gen, r.clone()));
        r
    }
}

pub struct Prog {
    pub raw: &'static RawProg,
    pub x: ProgX,
}

impl Prog {
    /// A table, checked to have no choices: every value has one code, so
    /// the verified decoder's output re-encodes canonically to the input
    /// (`vsyn::rt::theorem_rigid`).
    pub fn new(raw: &'static RawProg) -> Prog {
        let x = raw.to_prog();
        assert!(vsyn::xir::rigid_x(&x), "{}: a descriptor with choices in an H.26x table", raw.name);
        Prog { raw, x }
    }
    pub fn get(&self, env: &[i64], name: &str) -> i64 { names::get(self.raw, env, name).unwrap_or(-1) }
}

fn rbsp_all(p: &Prog, ctx: &Vec<Vec<i64>>, rbsp: &[u8]) -> Option<ParsedX> {
    decode_rbsp_x(&p.x, ctx, rbsp)
}

fn pre(p: &Prog, ctx: &Vec<Vec<i64>>, rbsp: &[u8]) -> Option<(ParsedX, usize)> {
    decode_pre(&p.x, ctx, rbsp, rbsp.len() * 8)
}

/// Re-encode a decoded NAL unit from its trace and compare it with the
/// original bytes. The theorems say this always succeeds; the check runs
/// the executable encoder and decoder against each other.
pub fn reencode(u: &Unit, p: &Prog, n: &[u8]) -> Result<(), String> {
    let px = u.px.as_ref().ok_or("not decoded")?;
    let rbsp = match u.hdr_bits {
        None => {
            let (r, px2) = encode_rbsp_x(&p.x, &u.ctx, &px.trace).ok_or("encoder refused the trace")?;
            if px2.env != px.env { return Err("environment differs".into()); }
            r
        }
        Some(k) => {
            let (w, _) = encode_pre(&p.x, &u.ctx, &px.trace).ok_or("encoder refused the trace")?;
            if w.pos != k { return Err(format!("header is {} bits, re-encoded {}", k, w.pos)); }
            // the header's bits, then the rest of the RBSP as it was
            let mut out = w.buf.clone();
            let total = u.rbsp.len() * 8;
            let mut bits = k;
            out.resize(u.rbsp.len(), 0);
            while bits < total {
                let bit = (u.rbsp[bits / 8] >> (7 - bits % 8)) & 1;
                if bit == 1 { out[bits / 8] |= 1 << (7 - bits % 8); } else { out[bits / 8] &= !(1 << (7 - bits % 8)); }
                bits += 1;
            }
            out
        }
    };
    if rbsp != u.rbsp { return Err("RBSP differs".into()); }
    let n2 = encode_nal_x(&u.hdr, &rbsp).ok_or("NAL unit not allowed by 7.4.1")?;
    if n2 != n { return Err("NAL unit bytes differ".into()); }
    Ok(())
}

// ------------------------------------------------------------------ H.264

pub struct H264 {
    pub nal: Prog,
    pub sps: Prog,
    pub sps_ext: Prog,
    pub subset_sps: Prog,
    pub pps_ids: Prog,
    pub pps: Prog,
    pub sei: Prog,
    pub aud: Prog,
    pub filler: Prog,
    pub slice_ids: Prog,
    pub slice: Prog,
    pub slice_a: Prog,
    pub slice_bc: Prog,
    sps_env: Vec<Option<Vec<i64>>>,
    pps_env: Vec<Option<PpsEntry>>,
    subset_env: Vec<Option<Vec<i64>>>,
    sps_gen: u64,
    active: Option<(Vec<i64>, Vec<i64>)>,
    primary_idr: bool,
}

impl H264 {
    pub fn new() -> H264 {
        use crate::gen::h264 as g;
        H264 {
            nal: Prog::new(&g::NAL), sps: Prog::new(&g::SPS), sps_ext: Prog::new(&g::SPS_EXT),
            subset_sps: Prog::new(&g::SUBSET_SPS), pps_ids: Prog::new(&g::PPS_IDS), pps: Prog::new(&g::PPS),
            sei: Prog::new(&g::SEI), aud: Prog::new(&g::AUD), filler: Prog::new(&g::FILLER),
            slice_ids: Prog::new(&g::SLICE_IDS), slice: Prog::new(&g::SLICE), slice_a: Prog::new(&g::SLICE_A),
            slice_bc: Prog::new(&g::SLICE_BC),
            sps_env: vec![None; 32], pps_env: vec![None; 256], subset_env: vec![None; 32], sps_gen: 0, active: None, primary_idr: false,
        }
    }

    pub fn prog(&self, raw: &'static RawProg) -> &Prog {
        for p in [&self.nal, &self.sps, &self.sps_ext, &self.subset_sps, &self.pps_ids, &self.pps, &self.sei,
                  &self.aud, &self.filler, &self.slice_ids, &self.slice, &self.slice_a, &self.slice_bc] {
            if std::ptr::eq(p.raw, raw) { return p; }
        }
        unreachable!()
    }

    pub fn parse(&mut self, n: &[u8]) -> Unit {
        let mut u = Unit::new(u32::MAX);
        if n.is_empty() { return u.reject("empty NAL unit"); }
        let hdr = match decode_all(&self.nal.x, &vec![], &n[..1], 8) {
            Some(h) => h,
            None => return u.reject("NAL unit header (forbidden_zero_bit)"),
        };
        let t = self.nal.get(&hdr.env, "nal_unit_type") as u32;
        u.nal_type = t;
        u.hdr = n[..1].to_vec();
        let nalenv = hdr.env;
        match t {
            1..=13 | 15 | 19 => {}
            _ => {
                // kept as bytes, but §7.4.1 still applies
                if decode_nal_x(n, n.len().min(1)).is_none() { return u.reject("7.4.1: emulation prevention"); }
                u.kind = Kind::Raw;
                return u;
            }
        }
        let rbsp = match decode_nal_x(n, 1) {
            Some(r) => r,
            None => return u.reject("7.4.1: emulation prevention"),
        };
        u.rbsp = rbsp.clone();
        let (prog, ctx, prefix): (&Prog, Vec<Vec<i64>>, bool) = match t {
            7 => (&self.sps, vec![nalenv], false),
            13 => (&self.sps_ext, vec![], false),
            15 => (&self.subset_sps, vec![nalenv], false),
            8 => {
                let ids = match pre(&self.pps_ids, &vec![], &rbsp) { Some(x) => x.0, None => return u.reject("PPS ids") };
                let pid = self.pps_ids.get(&ids.env, "pic_parameter_set_id") as usize;
                let sid = self.pps_ids.get(&ids.env, "seq_parameter_set_id") as usize;
                self.pps_env[pid] = Some(PpsEntry { rbsp: rbsp.clone(), nal: nalenv.clone(), sps_id: sid, cache: None });
                // a PPS may refer to an SPS or, for MVC and SVC, a subset SPS
                // (whose seq_parameter_set_data( ) has the same variables)
                // which of the two a PPS is interpreted against is decided when
                // a slice activates it; at receipt, either will do
                let s = match (&self.sps_env[sid], &self.subset_env[sid]) {
                    (Some(s), Some(ss)) => {
                        if rbsp_all(&self.pps, &vec![nalenv.clone(), s.clone()], &rbsp).is_some() { s.clone() } else { ss.clone() }
                    }
                    (Some(s), None) | (None, Some(s)) => s.clone(),
                    (None, None) => { u.kind = Kind::Deferred; u.why = "its SPS has not arrived"; return u; }
                };
                (&self.pps, vec![nalenv, s], false)
            }
            1 | 2 | 5 | 19 => {
                let ids = match pre(&self.slice_ids, &vec![], &rbsp) { Some(x) => x.0, None => return u.reject("slice header ids") };
                let pid = self.slice_ids.get(&ids.env, "pic_parameter_set_id") as usize;
                let sid = match &self.pps_env[pid] { Some(p) => p.sps_id, None => return u.reject("slice refers to a missing PPS") };
                let s = match (&self.sps_env[sid], &self.subset_env[sid]) {
                    (Some(s), _) | (None, Some(s)) => s.clone(),
                    (None, None) => return u.reject("PPS refers to a missing SPS"),
                };
                let gen = self.sps_gen;
                let pe = match self.pps_env[pid].as_mut().unwrap().env(&self.pps, &s, gen) {
                    Some(e) => e,
                    None => return u.reject("its PPS does not decode against its SPS"),
                };
                let mut s = s;
                let mut nalenv = nalenv;
                if t == 19 {
                    // 7.4.2.1.2: an auxiliary coded picture is IDR when its
                    // primary picture is, and has ChromaArrayType 0
                    let slot = self.nal.raw.slot("IdrPicFlag").unwrap();
                    nalenv[slot] = self.primary_idr as i64;
                    for v in ["chroma_format_idc", "ChromaArrayType"] {
                        let slot = self.sps.raw.slot(v).unwrap();
                        s[slot] = 0;
                    }
                } else {
                    self.primary_idr = t == 5;
                    self.active = Some((s.clone(), pe.clone()));
                }
                (if t == 2 { &self.slice_a } else { &self.slice }, vec![nalenv, s, pe], true)
            }
            3 | 4 => {
                let (s, pe) = match &self.active { Some(a) => a.clone(), None => return u.reject("partition without an active PPS") };
                (&self.slice_bc, vec![nalenv, s, pe], true)
            }
            6 => (&self.sei, vec![], false),
            9 => (&self.aud, vec![], false),
            12 => (&self.filler, vec![], false),
            10 | 11 => {
                if !rbsp.is_empty() { return u.reject("end of sequence/stream with data"); }
                u.kind = Kind::Parsed;
                return u;
            }
            _ => unreachable!(),
        };
        u.prog = Some(prog.raw);
        let r = if prefix {
            pre(prog, &ctx, &rbsp).map(|(px, k)| (px, Some(k)))
        } else {
            rbsp_all(prog, &ctx, &rbsp).map(|px| (px, None))
        };
        match r {
            None => { u.ctx = ctx; u.reject("syntax") }
            Some((px, k)) => {
                if let Some(k) = k {
                    // 7.3.2.8-10: slice data, then rbsp_slice_trailing_bits( );
                    // a partition B or C may carry no slice data
                    let cabac = self.pps.get(&ctx[2], "entropy_coding_mode_flag") != 0;
                    if !vh26x::rbsp::slice_tail_ok_x(&rbsp, k, cabac, !matches!(t, 3 | 4)) {
                        u.ctx = ctx;
                        return u.reject("7.3.2.8: no slice data and rbsp_slice_trailing_bits( ) after the header");
                    }
                }
                if t == 7 {
                    let id = self.sps.get(&px.env, "seq_parameter_set_id") as usize;
                    self.sps_env[id] = Some(px.env.clone());
                    self.sps_gen += 1;
                }
                if t == 15 && self.subset_sps.raw.nslots == self.sps.raw.nslots
                    && self.subset_sps.raw.vars.iter().zip(self.sps.raw.vars).all(|(a, b)| a.0 == b.0 && a.1 == b.1) {
                    let id = self.subset_sps.get(&px.env, "seq_parameter_set_id") as usize;
                    self.subset_env[id] = Some(px.env.clone());
                    self.sps_gen += 1;
                }
                u.kind = Kind::Parsed;
                u.px = Some(px);
                u.hdr_bits = k;
                u.ctx = ctx;
                u
            }
        }
    }
}

// ------------------------------------------------------------------ H.265

pub struct H265 {
    pub nal: Prog,
    pub vps: Prog,
    pub sps: Prog,
    pub pps_ids: Prog,
    pub pps: Prog,
    pub sei: Prog,
    pub aud: Prog,
    pub filler: Prog,
    pub slice_ids: Prog,
    pub slice: Prog,
    sps_env: Vec<Option<Vec<i64>>>,
    pps_env: Vec<Option<PpsEntry>>,
    sps_gen: u64,
}

impl H265 {
    pub fn new() -> H265 {
        use crate::gen::h265 as g;
        H265 {
            nal: Prog::new(&g::NAL), vps: Prog::new(&g::VPS), sps: Prog::new(&g::SPS),
            pps_ids: Prog::new(&g::PPS_IDS), pps: Prog::new(&g::PPS), sei: Prog::new(&g::SEI),
            aud: Prog::new(&g::AUD), filler: Prog::new(&g::FILLER), slice_ids: Prog::new(&g::SLICE_IDS),
            slice: Prog::new(&g::SLICE),
            sps_env: vec![None; 16], pps_env: vec![None; 64], sps_gen: 0,
        }
    }

    pub fn prog(&self, raw: &'static RawProg) -> &Prog {
        for p in [&self.nal, &self.vps, &self.sps, &self.pps_ids, &self.pps, &self.sei, &self.aud,
                  &self.filler, &self.slice_ids, &self.slice] {
            if std::ptr::eq(p.raw, raw) { return p; }
        }
        unreachable!()
    }

    pub fn parse(&mut self, n: &[u8]) -> Unit {
        let mut u = Unit::new(u32::MAX);
        if n.len() < 2 { return u.reject("NAL unit shorter than its header"); }
        let hdr = match decode_all(&self.nal.x, &vec![], &n[..2], 16) {
            Some(h) => h,
            None => return u.reject("NAL unit header"),
        };
        let t = self.nal.get(&hdr.env, "nal_unit_type") as u32;
        let layer = self.nal.get(&hdr.env, "nuh_layer_id");
        u.nal_type = t;
        u.hdr = n[..2].to_vec();
        let nalenv = hdr.env;
        let known = matches!(t, 0..=9 | 16..=21 | 32..=40);
        if !known || layer != 0 {
            // reserved and unspecified types, and other layers (Annex F), as bytes
            if decode_nal_x(n, 2).is_none() { return u.reject("7.4.2: emulation prevention"); }
            u.kind = Kind::Raw;
            return u;
        }
        let rbsp = match decode_nal_x(n, 2) {
            Some(r) => r,
            None => return u.reject("7.4.2: emulation prevention"),
        };
        u.rbsp = rbsp.clone();
        let (prog, ctx, prefix): (&Prog, Vec<Vec<i64>>, bool) = match t {
            32 => (&self.vps, vec![nalenv], false),
            33 => (&self.sps, vec![nalenv], false),
            34 => {
                let ids = match pre(&self.pps_ids, &vec![], &rbsp) { Some(x) => x.0, None => return u.reject("PPS ids") };
                let pid = self.pps_ids.get(&ids.env, "pps_pic_parameter_set_id") as usize;
                let sid = self.pps_ids.get(&ids.env, "pps_seq_parameter_set_id") as usize;
                self.pps_env[pid] = Some(PpsEntry { rbsp: rbsp.clone(), nal: nalenv.clone(), sps_id: sid, cache: None });
                let s = match &self.sps_env[sid] {
                    Some(s) => s.clone(),
                    None => { u.kind = Kind::Deferred; u.why = "its SPS has not arrived"; return u; }
                };
                (&self.pps, vec![nalenv, s], false)
            }
            35 => (&self.aud, vec![], false),
            36 | 37 => {
                if !rbsp.is_empty() { return u.reject("end of sequence/bitstream with data"); }
                u.kind = Kind::Parsed;
                return u;
            }
            38 => (&self.filler, vec![], false),
            39 | 40 => (&self.sei, vec![], false),
            _ => {
                let ids = match pre(&self.slice_ids, &vec![nalenv.clone()], &rbsp) { Some(x) => x.0, None => return u.reject("slice header ids") };
                let pid = self.slice_ids.get(&ids.env, "slice_pic_parameter_set_id") as usize;
                let sid = match &self.pps_env[pid] { Some(p) => p.sps_id, None => return u.reject("slice refers to a missing PPS") };
                let s = match &self.sps_env[sid] { Some(s) => s.clone(), None => return u.reject("PPS refers to a missing SPS") };
                let gen = self.sps_gen;
                let pe = match self.pps_env[pid].as_mut().unwrap().env(&self.pps, &s, gen) {
                    Some(e) => e,
                    None => return u.reject("its PPS does not decode against its SPS"),
                };
                (&self.slice, vec![nalenv, s, pe], true)
            }
        };
        u.prog = Some(prog.raw);
        let r = if prefix {
            pre(prog, &ctx, &rbsp).map(|(px, k)| (px, Some(k)))
        } else {
            rbsp_all(prog, &ctx, &rbsp).map(|px| (px, None))
        };
        match r {
            None => { u.ctx = ctx; u.reject("syntax") }
            Some((px, k)) => {
                if let Some(k) = k {
                    // 7.3.2.9: slice_segment_data( ) (at least one CTU), then
                    // rbsp_slice_segment_trailing_bits( )
                    if !vh26x::rbsp::slice_tail_ok_x(&rbsp, k, true, true) {
                        u.ctx = ctx;
                        return u.reject("7.3.2.9: no slice data and rbsp_slice_segment_trailing_bits( ) after the header");
                    }
                    // 7.4.7.1: the entry points' subsets are bytes of the slice
                    // data, so their offsets add up to less than it (which the
                    // header's own program cannot see)
                    let ep: u64 = crate::names::annotate(prog.raw, &prog.x, &ctx, &px.trace).iter()
                        .filter(|nm| nm.name.starts_with("entry_point_offset_minus1")).map(|nm| nm.value as u64 + 1).sum();
                    if ep > 0 && ep >= (n.len() as u64).saturating_sub(2 + (k as u64) / 8) {
                        u.ctx = ctx;
                        return u.reject("7.4.7.1: entry points beyond the slice data");
                    }
                }
                if t == 33 {
                    let id = self.sps.get(&px.env, "sps_seq_parameter_set_id") as usize;
                    self.sps_env[id] = Some(px.env.clone());
                    self.sps_gen += 1;
                }
                u.kind = Kind::Parsed;
                u.px = Some(px);
                u.hdr_bits = k;
                u.ctx = ctx;
                u
            }
        }
    }
}

/// Either codec, for drivers.
pub enum Codec { H264(H264), H265(H265) }

impl Codec {
    pub fn new(h265: bool) -> Codec { if h265 { Codec::H265(H265::new()) } else { Codec::H264(H264::new()) } }
    pub fn parse(&mut self, n: &[u8]) -> Unit {
        match self { Codec::H264(c) => c.parse(n), Codec::H265(c) => c.parse(n) }
    }
    pub fn prog(&self, raw: &'static RawProg) -> &Prog {
        match self { Codec::H264(c) => c.prog(raw), Codec::H265(c) => c.prog(raw) }
    }
}

/// Each NAL unit of a stream in one word: `TYPE,PROG,VERDICT,CONF,TRACE`,
/// the verdict `ok`, `raw`, `deferred` or `reject`, CONF 0 for `nonconf`,
/// TRACE the FNV-1a hash of the decoded values (little-endian i64s), and
/// `,REENC` appended if the unit does not re-encode to its bytes. What
/// `vh26x-tool --vec` prints and `tests/smoke.rs` checks.
pub fn summary(h265: bool, nals: &[&[u8]]) -> Vec<String> {
    let mut h = Codec::new(h265);
    nals.iter().map(|n| {
        let u = h.parse(n);
        let v = match u.kind { Kind::Parsed => "ok", Kind::Raw => "raw", Kind::Deferred => "deferred", Kind::Rejected => "reject" };
        let tr = u.px.as_ref().map(|px| px.trace.iter().flat_map(|x| x.to_le_bytes())
            .fold(0xcbf29ce484222325u64, |a, b| (a ^ b as u64).wrapping_mul(0x100000001b3))).unwrap_or(0);
        let reenc = match (u.prog, &u.px) {
            (Some(raw), Some(_)) if reencode(&u, h.prog(raw), n).is_err() => ",REENC",
            _ => "",
        };
        format!("{},{},{},{},{:016x}{}", u.nal_type, u.prog.map(|p| p.name).unwrap_or("-"), v, u.conf() as u8, tr, reenc)
    }).collect()
}
