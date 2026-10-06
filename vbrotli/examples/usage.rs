//! The calls `vbrotli/README.md` shows, on a small stream: 100,000 bytes of
//! "the cat sat on the mat; " compressed by Google's encoder (quality 9)
//! into 37 bytes.
use vbrotli::{decompress, decompress_into, Decompressor, Error, Status};

const STREAM: [u8; 37] = [
    0x5b, 0x9f, 0x86, 0x01, 0x40, 0xc0, 0x39, 0x96, 0xea, 0x4a, 0xb7, 0x25, 0x91, 0xc3, 0xcb, 0xd3, 0xed, 0x1c, 0x10,
    0x09, 0xe6, 0x32, 0x19, 0x54, 0x2b, 0xbb, 0x43, 0x5c, 0x3e, 0x63, 0xf8, 0x9e, 0x85, 0xfc, 0x02, 0x44, 0x03,
];

fn main() -> Result<(), Error> {
    let data: Vec<u8> = b"the cat sat on the mat; ".iter().cycle().take(100_000).cloned().collect();

    // a whole stream: the data and the bytes the stream took
    let (back, used) = decompress(&STREAM, 1 << 30)?;
    assert!(back == data && used == STREAM.len());

    // into a buffer kept from stream to stream: the data is buf[..n]
    let mut buf = Vec::new();
    for _ in 0..3 {
        let (n, _) = decompress_into(&STREAM, 1 << 30, &mut buf)?;
        assert_eq!(&buf[..n], &data[..]);
    }

    // in pieces of any size, here 5 bytes
    let mut d = Decompressor::new(1 << 30);
    let mut out = Vec::new();
    for piece in STREAM.chunks(5) {
        match d.feed(piece, &mut out)? {
            Status::Done { bits } => {
                assert_eq!(bits, 8 * STREAM.len());
                break;
            }
            Status::NeedMore => {}
        }
    }
    assert_eq!(out, data);

    // a limit on the output
    assert_eq!(decompress(&STREAM, 99_999).err(), Some(Error::TooBig));
    println!("ok: {} bytes from {}", data.len(), STREAM.len());
    Ok(())
}
