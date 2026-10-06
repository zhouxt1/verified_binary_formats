//! Helpers over vsyn programs, for the format drivers (vh26x-tool,
//! vav1-tool). None of this is verified, and none of it decides a verdict:
//! verdicts come from vsyn's verified decoder and encoder.
//!
//! * `names`: a trace's values, named, with their bit positions;
//! * `why`: where and why a structure fails to decode, and the "decoders
//!   shall ignore" constraints it breaks;
//! * `rgen`: random traces that respect a table's constraints, for
//!   structure-aware fuzzing.
pub mod names;
pub mod why;
pub mod rgen;
