//! Lossy WebP: VP8 key frames (RFC 6386), verified.
//!
//! * `spec`: RFC 6386's reference decoder, key frames only, as a spec.
//! * `tab`: its tables.
//! * `dec::vp8_x`: the verified decoder, built of `bd` (bool decoder), `hdr`,
//!   `modes`, `tok`, `xf` (inverse transforms), `recon`, `lf` (loop
//!   filter) and `plane`.
//! * `fspec`, `file::webp_lossy_x`: lossy files with ALPH alpha, verified.
pub mod tab;
pub mod spec;
pub mod plane;
pub mod bd;
pub mod hdr;
pub mod modes;
pub mod tok;
pub mod xf;
#[cfg(target_arch = "x86_64")]
pub mod xfx;
pub mod recon;
#[cfg(target_arch = "x86_64")]
pub mod predx;
pub mod lf;
#[cfg(target_arch = "x86_64")]
pub mod lfx;
pub mod dec;
pub mod fspec;
pub mod file;
