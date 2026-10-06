//! The calls `vdeflate/README.md` shows, on a small input.
use vdeflate::inflate::{inflate_raw, Error};
use vdeflate::wrap::{inflate_zlib, inflate_gzip_file, deflate_gzip, deflate_zlib};
use vdeflate::enc2::{deflate_level, level};
use vdeflate::deflater::ZDeflater;
use vdeflate::zstream::{ZInflater, ZStatus};

fn main() -> Result<(), Error> {
    let data: Vec<u8> = b"the cat sat on the mat; ".iter().cycle().take(100_000).cloned().collect();

    // whole buffers
    let raw = deflate_level(&data, level(6)).unwrap();
    let (back, _bits, _) = inflate_raw(&raw, 1 << 30)?;
    assert_eq!(back, data);
    let zl = deflate_zlib(&data, level(1)).unwrap();
    let (back, used, _) = inflate_zlib(&zl, 1 << 30)?;
    assert!(back == data && used == zl.len());
    let mut gz = deflate_gzip(&data, level(9)).unwrap();
    gz.extend(deflate_gzip(b"and a second member", level(6)).unwrap());
    let back = inflate_gzip_file(&gz, 1 << 30)?;
    assert_eq!(back.len(), data.len() + 19);

    // streaming, in pieces
    let (mut z, mut out) = ZDeflater::new(level(6), true).unwrap();
    for piece in data.chunks(1000) {
        out.extend(z.feed(piece));
    }
    out.extend(z.finish());
    let mut d = ZInflater::new(true, 1 << 30);
    let mut back = Vec::new();
    for piece in out.chunks(777) {
        let (d2, r) = d.feed(piece, &mut back);
        d = d2;
        match r? {
            ZStatus::Done { .. } => break,
            ZStatus::NeedMore => {}
        }
    }
    assert_eq!(back, data);
    println!("ok: raw {} bytes, zlib {}, gzip {}, streamed gzip {}", raw.len(), zl.len(), gz.len(), out.len());
    Ok(())
}
