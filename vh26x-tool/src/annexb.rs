//! Annex B byte streams: NAL units after start codes 0x000001, with any
//! number of zero bytes before a start code (leading_zero_8bits, zero_byte,
//! trailing_zero_8bits). A NAL unit contains no 0x000000 or 0x000001 and
//! does not end in 0x00 (§7.4.1), so the split is unique: each NAL unit
//! runs from a start code to the last nonzero byte before the next one.

/// The NAL units of an Annex B byte stream, or `None` when the stream does
/// not start (after zero bytes) with a start code: vh26x's verified split.
pub fn split(b: &[u8]) -> Option<Vec<&[u8]>> {
    vh26x::annexb::split_x(b).map(|v| v.into_iter().map(|(s, e)| &b[s..e]).collect())
}

/// The canonical byte stream of NAL units: each after 0x00000001.
pub fn join(nals: &[Vec<u8>]) -> Vec<u8> {
    let mut v = Vec::new();
    for n in nals {
        v.extend_from_slice(&[0, 0, 0, 1]);
        v.extend_from_slice(n);
    }
    v
}
