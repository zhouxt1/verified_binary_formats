//! vwebp — a verified WebP decoder: lossless (VP8L, RFC 9649 section 3) and
//! lossy (VP8 key frames, RFC 6386, with ALPH alpha).
//!
//! * `spec`: RFC 9649 section 3 as a spec decoder over the stream's bits,
//!   following libwebp 1.6.0 where the RFC is silent, with a flag for the
//!   streams the RFC's text also allows.
//! * `dec::vp8l_x`: the verified VP8L decoder, proved to compute `spec::vp8l`.
//! * `cspec`, `riff::webp_x`: the container (RFC 9649 section 2) for still
//!   lossless images, and its verified decoder.
//! * `aspec`, `anim::webp_anim_x`: animated WebP with lossless frames,
//!   canvases as libwebp's WebPAnimDecoder assembles them, verified.
//! * `vp8`: lossy images: `vp8::spec` (RFC 6386's reference decoder as a
//!   spec), `vp8::dec::vp8_x` (verified), and lossy files with alpha
//!   (`vp8::fspec`, `vp8::file::webp_lossy_x`).
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, unused_variables, dead_code))]
use vstd::prelude::*;

verus! {
    global size_of usize == 8;
}

pub mod spec;
pub mod huff;
pub mod code;
pub mod pix;
pub mod img;
pub mod inv;
#[cfg(target_arch = "x86_64")]
pub mod invx;
pub mod tr;
pub mod dec;
pub mod cspec;
pub mod riff;
pub mod aspec;
pub mod anim;
pub mod vp8;
pub mod rgb;
#[cfg(target_arch = "x86_64")]
pub mod rgbx;
pub mod api;
