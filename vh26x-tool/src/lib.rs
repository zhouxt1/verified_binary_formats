//! Drivers for vh26x's verified header codecs. The per-NAL-unit work (the
//! escaping, the trailing bits, the syntax structure) is vh26x's verified
//! code; what is here is the bookkeeping around it, unverified: splitting
//! a byte stream into NAL units, keeping the parameter sets a later NAL
//! unit is decoded against, and naming the trace's values for printing.
pub mod gen;
pub mod annexb;
pub mod stream;
pub use vsyn_tool::{names, why, rgen};
pub mod sgen;
