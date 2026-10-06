//! vdeflate — a verified DEFLATE (RFC 1951) decoder and compressor.
//!
//! * `spec`: RFC 1951 as a spec decoder over the stream's bits, with a flag
//!   for the streams zlib also accepts.
//! * `huff`: canonical Huffman codes, their tables, and decoders proved to
//!   compute the spec's search.
//! * `inflate`: the whole-buffer decoder, proved to compute the spec.
//! * `step`, `shift`, `agree`: the spec in steps, which depend only on the
//!   bits they read; decoding from a window of the output; dropping decoded
//!   input; a stream decodes as any other with its bits up to its end.
//! * `stream`: the streaming decoder, in bounded memory.
//! * `zstream`: the streaming zlib and gzip decoder.
//! * `wrap`: zlib and gzip, Adler-32 and CRC-32, both ways.
//! * `enc`: the bit writer, canonical codes, the fixed-code compressor.
//! * `enc2`: the compressor (zlib's levels 1 to 9), proved to round-trip.
//! * `deflater`: the streaming compressor, raw, zlib and gzip, in bounded
//!   memory.
//!
//! See README.md.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, unused_variables, dead_code))]
use vstd::prelude::*;

verus! {
    global size_of usize == 8;
}

pub mod spec;
pub mod huff;
pub mod inflate;
pub mod step;
pub mod stream;
pub mod wrap;
pub mod shift;
pub mod enc;
pub mod enc2;
pub mod deflater;
pub mod agree;
pub mod zstream;
