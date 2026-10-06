//! vsyn — a verified interpreter for bitstream syntax tables.
//!
//! A format's syntax tables (H.264 §7.3, H.265 §7.3, AV1 §5) are
//! transcribed as data, and one interpreter, proved once, decodes and
//! encodes any of them:
//!
//! * `eg`, `avd`: the descriptors of H.264/H.265 and of AV1, as prefix
//!   codes;
//! * `ir`: the tables as data, and the arithmetic of their conditions;
//! * `sem`: what a table means, as a spec decoder and a spec encoder;
//! * `rt`: the theorems, for every table: the two are inverse;
//! * `bits`, `xir`, `xdec`, `xenc`: the executable reader, writer,
//!   decoder and encoder, proved equal to the spec;
//! * `raw`: the tables as a compiler writes them.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, unused_variables, dead_code))]
pub mod eg;
pub mod avd;
pub mod ir;
pub mod sem;
pub mod rt;
pub mod bits;
pub mod avx;
pub mod xir;
pub mod xdec;
pub mod xenc;
pub mod raw;
