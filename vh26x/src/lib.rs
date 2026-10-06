//! vh26x — verified H.264 and H.265 header parsers and encoders.
//!
//! The syntax tables of H.264 §7.3 and H.265 §7.3 are transcribed as data
//! (`vsync` compiles them), and one verified interpreter decodes and
//! encodes any of them:
//!
//! * `eg`: the descriptors `u(n)`, `ue(v)`, `se(v)` and the SEI 0xFF-byte
//!   coding, as prefix codes.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, unused_variables, dead_code))]
pub use vsyn::{eg, ir, sem, rt, bits, xir, xdec, xenc, raw};
pub mod rbsp;
pub mod esc;
pub mod nal;
pub mod annexb;
