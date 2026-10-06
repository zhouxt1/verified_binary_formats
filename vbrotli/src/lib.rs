//! vbrotli — a verified Brotli (RFC 7932) decoder.
//!
//! * `spec`: RFC 7932 as a spec decoder over the stream's bits, over any
//!   static dictionary laid out as the RFC's, with a flag for the streams
//!   Google's decoder also accepts.
//! * `tables`: the RFC's tables (context lookup, dictionary word counts,
//!   transforms), as spec sequences and exec constants proved equal.
//!
//! See README.md.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, unused_variables, dead_code))]
use vstd::prelude::*;

verus! {
    global size_of usize == 8;
}

pub mod tables;
pub mod spec;
pub mod code;
pub mod br;
pub mod moves;
pub mod sspec;
pub mod hdr;
pub mod dict;
pub mod cmd;
pub mod dec;
pub mod stream;

/// The static dictionary of RFC 7932 Appendix A, as Google's `dictionary.bin`
/// (`difftest/brotli/dict.py` checks it byte for byte against the RFC's
/// text). It is data the spec is parametric in, not part of what is proved.
pub static DICTIONARY: &[u8; 122784] = include_bytes!("../data/dictionary.bin");

pub use dec::Error;

/// Decode a Brotli stream, producing at most `max_out` bytes: the data and
/// the number of bytes the stream took. Proved to compute RFC 7932's output
/// (`dec::brotli_x`, `spec::brotli`) with the static dictionary above.
pub fn decompress(buf: &[u8], max_out: usize) -> Result<(Vec<u8>, usize), Error> {
    let max_out = max_out.min(0x0800_0000_0000_0000 - 1);
    dec::brotli_x(&DICTIONARY[..], buf, max_out).map(|(o, bits, _)| (o, bits / 8))
}

/// Decode a Brotli stream into `out`, producing at most `max_out` bytes:
/// the length of the data, which is `out[..n]`, and the number of bytes the
/// stream took. `out` is reused as it is: bytes past `n` are room kept for
/// the next stream (not zeroed or allocated again), so a buffer passed to
/// one call after another costs nothing to set up. Proved as `decompress`
/// (`dec::brotli_into`).
pub fn decompress_into(buf: &[u8], max_out: usize, out: &mut Vec<u8>) -> Result<(usize, usize), Error> {
    let max_out = max_out.min(0x0800_0000_0000_0000 - 1);
    dec::brotli_into(&DICTIONARY[..], buf, max_out, out).map(|(n, bits, _)| (n, bits / 8))
}

pub use stream::Status;

/// A streaming decoder with the RFC's dictionary: feed it the stream in
/// pieces of any size; after each piece it has sent to `sink` all the output
/// the input so far decides, and its verdict holds for every stream that
/// starts with the input so far (`stream::Decoder::feed`).
pub struct Decompressor {
    d: stream::Decoder,
}

impl Decompressor {
    /// A decoder whose output may be at most `limit` bytes.
    pub fn new(limit: usize) -> Self {
        Decompressor { d: stream::Decoder::new(&DICTIONARY[..], limit) }
    }

    /// Decode the next piece.
    pub fn feed(&mut self, piece: &[u8], sink: &mut Vec<u8>) -> Result<Status, Error> {
        self.d.feed(&DICTIONARY[..], piece, sink)
    }

    /// Bytes the decoder holds between pieces: input not yet used, and its
    /// output buffer.
    pub fn held(&self) -> (usize, usize) {
        (self.d.inp.len(), self.d.out.len())
    }

    /// Whether Google's decoder also accepts the stream (see `spec`).
    pub fn google(&self) -> bool {
        self.d.google
    }
}
