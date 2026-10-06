//! Random well-formed streams: parameter sets, then slices whose headers are
//! random and whose data is random bits. Each NAL unit is a trace from
//! `rgen`, encoded by vh26x's verified encoder (so conforming as far as the
//! syntax tables go), and checked by decoding it back.
use std::collections::HashMap;
use vh26x::xdec::decode_all;
use vh26x::xenc::{encode_all, encode_pre};
use vh26x::nal::{encode_nal_x, encode_rbsp_x};
use crate::rgen::{Gen, Rng};
use crate::stream::{H264, H265, Prog};

/// Whether the streams generated keep every constraint (set per stream).
static CONFORMING: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(true);

fn mkgen<'a>(p: &'a Prog, ctx: &'a Vec<Vec<i64>>, rng: &'a mut Rng, force: &'a HashMap<&'static str, i64>) -> Gen<'a> {
    let mut g = Gen::new(p.raw, &p.x, ctx, rng, force);
    g.conforming = CONFORMING.load(std::sync::atomic::Ordering::Relaxed);
    g
}

pub fn set_conforming(c: bool) { CONFORMING.store(c, std::sync::atomic::Ordering::Relaxed); }

fn header(p: &Prog, rng: &mut Rng, force: &HashMap<&'static str, i64>) -> Option<(Vec<u8>, Vec<i64>)> {
    let tr = mkgen(p, &vec![], rng, force).run()?;
    let (w, px) = encode_all(&p.x, &vec![], &tr)?;
    Some((w.buf, px.env))
}

fn rbsp_nal(p: &Prog, ctx: &Vec<Vec<i64>>, rng: &mut Rng, force: &HashMap<&'static str, i64>, hdr: &[u8])
    -> Option<(Vec<u8>, Vec<i64>)> {
    for _ in 0..40 {
        let Some(tr) = mkgen(p, ctx, rng, force).run() else { continue };
        let Some((rbsp, px)) = encode_rbsp_x(&p.x, ctx, &tr) else { continue };
        let Some(n) = encode_nal_x(hdr, &rbsp) else { continue };
        return Some((n, px.env));
    }
    None
}

/// A slice NAL unit: a random header, then random slice data and trailing
/// bits. With CABAC (H.264), the data starts with cabac_alignment_one_bits.
fn slice_nal(p: &Prog, ctx: &Vec<Vec<i64>>, rng: &mut Rng, force: &HashMap<&'static str, i64>, hdr: &[u8],
             cabac: bool) -> Option<Vec<u8>> {
    for _ in 0..40 {
        let Some(tr) = mkgen(p, ctx, rng, force).run() else { continue };
        let Some((w, _)) = encode_pre(&p.x, ctx, &tr) else { continue };
        let mut bits: Vec<u8> = (0..w.pos).map(|i| (w.buf[i / 8] >> (7 - i % 8)) & 1).collect();
        if cabac { while bits.len() % 8 != 0 { bits.push(1); } }
        // slice data at least as long as its entry points say (7.4.7.1)
        let ep: usize = crate::names::annotate(p.raw, &p.x, ctx, &tr).iter()
            .filter(|n| n.name.starts_with("entry_point_offset_minus1")).map(|n| n.value as usize + 1).sum();
        let extra = 8 * ep + 8 + rng.below(64) as usize;
        for _ in 0..extra { bits.push((rng.next() & 1) as u8); }
        bits.push(1);
        while bits.len() % 8 != 0 { bits.push(0); }
        let rbsp: Vec<u8> = bits.chunks(8).map(|c| c.iter().fold(0u8, |a, b| a * 2 + b)).collect();
        let Some(n) = encode_nal_x(hdr, &rbsp) else { continue };
        return Some(n);
    }
    None
}

fn f(pairs: &[(&'static str, i64)]) -> HashMap<&'static str, i64> { pairs.iter().copied().collect() }

pub fn h264(seed: u64, slices: usize) -> Option<Vec<Vec<u8>>> {
    let c = H264::new();
    let mut rng = Rng(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1);
    let profiles = [66, 77, 88, 100, 110, 122, 244, 44, 83, 118];
    let profile = profiles[rng.below(profiles.len() as u64) as usize];
    let (hs, nal_s) = header(&c.nal, &mut rng, &f(&[("nal_ref_idc", 3), ("nal_unit_type", 7)]))?;
    let sps_id = rng.below(32) as i64;
    let (sps, sps_env) = rbsp_nal(&c.sps, &vec![nal_s.clone()], &mut rng,
        &f(&[("profile_idc", profile), ("seq_parameter_set_id", sps_id)]), &hs)?;
    let (hp, nal_p) = header(&c.nal, &mut rng, &f(&[("nal_ref_idc", 3), ("nal_unit_type", 8)]))?;
    let pps_id = rng.below(256) as i64;
    let (pps, pps_env) = rbsp_nal(&c.pps, &vec![nal_p, sps_env.clone()], &mut rng,
        &f(&[("seq_parameter_set_id", sps_id), ("pic_parameter_set_id", pps_id)]), &hp)?;
    let mut out = vec![sps, pps];
    for k in 0..slices {
        let (t, refidc) = if k == 0 { (5, 1 + rng.below(3) as i64) } else { (1, rng.below(4) as i64) };
        let (hh, nal_h) = header(&c.nal, &mut rng, &f(&[("nal_ref_idc", refidc), ("nal_unit_type", t)]))?;
        let ctx = vec![nal_h, sps_env.clone(), pps_env.clone()];
        let cabac = c.pps.get(&pps_env, "entropy_coding_mode_flag") == 1;
        out.push(slice_nal(&c.slice, &ctx, &mut rng, &f(&[("pic_parameter_set_id", pps_id)]), &hh, cabac)?);
    }
    Some(out)
}

pub fn h265(seed: u64, slices: usize) -> Option<Vec<Vec<u8>>> {
    let c = H265::new();
    let mut rng = Rng(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1);
    let hdr = |rng: &mut Rng, t: i64| header(&c.nal, rng, &f(&[("nal_unit_type", t), ("nuh_layer_id", 0), ("nuh_temporal_id_plus1", 1)]));
    let (hv, nal_v) = hdr(&mut rng, 32)?;
    let vps_id = rng.below(16) as i64;
    let vps_sub = rng.below(7) as i64;
    let nesting = if vps_sub == 0 { 1 } else { rng.below(2) as i64 };
    let (vps, _) = rbsp_nal(&c.vps, &vec![nal_v], &mut rng,
        &f(&[("vps_video_parameter_set_id", vps_id), ("vps_base_layer_internal_flag", 1), ("vps_base_layer_available_flag", 1),
             ("vps_max_layers_minus1", 0), ("vps_max_sub_layers_minus1", vps_sub), ("vps_temporal_id_nesting_flag", nesting),
             ("vps_extension_flag", 0)]), &hv)?;
    // 7.4.3.2.1: the SPS's sub-layers and nesting agree with the VPS's
    let sps_sub = rng.below(vps_sub as u64 + 1) as i64;
    let sps_nesting = if nesting == 1 || sps_sub == 0 { 1 } else { rng.below(2) as i64 };
    // multiples of 64, so of any MinCbSizeY
    let wmax = if rng.chance(1, 8) { 300 } else { 30 };
    let width = 64 * (1 + rng.below(wmax)) as i64;
    let hmax = if rng.chance(1, 8) { 300 } else { 30 };
    let height = 64 * (1 + rng.below(hmax)) as i64;
    let (hs, nal_s) = hdr(&mut rng, 33)?;
    let sps_id = rng.below(16) as i64;
    let profile = [1, 2, 3, 4, 9][rng.below(5) as usize];
    let (sps, sps_env) = rbsp_nal(&c.sps, &vec![nal_s], &mut rng,
        &f(&[("sps_video_parameter_set_id", vps_id), ("sps_seq_parameter_set_id", sps_id), ("general_profile_idc", profile),
             ("general_profile_space", 0), ("sps_max_sub_layers_minus1", sps_sub), ("sps_temporal_id_nesting_flag", sps_nesting),
             ("sps_multilayer_extension_flag", 0), ("sps_3d_extension_flag", 0),
             ("pic_width_in_luma_samples", width), ("pic_height_in_luma_samples", height)]), &hs)?;
    let (hp, nal_p) = hdr(&mut rng, 34)?;
    let pps_id = rng.below(64) as i64;
    let (pps, pps_env) = rbsp_nal(&c.pps, &vec![nal_p, sps_env.clone()], &mut rng,
        &f(&[("pps_seq_parameter_set_id", sps_id), ("pps_pic_parameter_set_id", pps_id),
             ("pps_multilayer_extension_flag", 0), ("pps_3d_extension_flag", 0)]), &hp)?;
    let mut out = vec![vps, sps, pps];
    for k in 0..slices {
        let t = if k == 0 { 19 } else { 1 };
        let (hh, nal_h) = hdr(&mut rng, t)?;
        let ctx = vec![nal_h, sps_env.clone(), pps_env.clone()];
        let first = if k == 0 { 1 } else { rng.below(2) as i64 };
        let olen = rng.below(4) as i64;
        out.push(slice_nal(&c.slice, &ctx, &mut rng,
            &f(&[("slice_pic_parameter_set_id", pps_id), ("first_slice_segment_in_pic_flag", first),
                 ("offset_len_minus1", olen)]), &hh, false)?);
    }
    Some(out)
}

/// Check a generated stream decodes, NAL unit by NAL unit.
pub fn decodes(nals: &[Vec<u8>], h265: bool) -> bool {
    let mut c = crate::stream::Codec::new(h265);
    nals.iter().all(|n| c.parse(n).kind == crate::stream::Kind::Parsed)
}

#[allow(dead_code)]
fn _unused() { let _ = decode_all; }
