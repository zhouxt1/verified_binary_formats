// vwebp's verified lossless decoder (riff::webp_x, whole files) behind the
// batch protocol of difftest/webp's wdec: records of a u32 length and a
// WebP file; for each, a status byte (1: an image), and for an image its
// width and height (u32 each) and its pixels as little-endian ARGB u32s,
// written in one piece straight to the file descriptor (as wdec's fwrite
// of its rows), so the output costs about what wdec's does.
use std::io::{Read, Write};
use std::os::fd::FromRawFd;
fn main() {
    let mut inp = std::io::stdin().lock();
    // stdout without its line buffering, which scans every byte for '\n'
    let raw = std::mem::ManuallyDrop::new(unsafe { std::fs::File::from_raw_fd(1) });
    let mut out = std::io::BufWriter::with_capacity(1 << 16, &*raw);
    loop {
        let mut len = [0u8; 4];
        if inp.read_exact(&mut len).is_err() { break; }
        let mut buf = vec![0u8; u32::from_le_bytes(len) as usize];
        inp.read_exact(&mut buf).unwrap();
        match vwebp::riff::webp_x(&buf, 1 << 28) {
            Ok((vwebp::riff::WebpX::Still { img, .. }, _)) => {
                out.write_all(&[1]).unwrap();
                out.write_all(&(img.w as u32).to_le_bytes()).unwrap();
                out.write_all(&(img.h as u32).to_le_bytes()).unwrap();
                #[cfg(target_endian = "little")]
                // the pixels' bytes, little-endian as the protocol wants
                let bytes = unsafe { std::slice::from_raw_parts(img.px.as_ptr() as *const u8, 4 * img.px.len()) };
                #[cfg(not(target_endian = "little"))]
                let bytes: Vec<u8> = img.px.iter().flat_map(|c| c.to_le_bytes()).collect();
                out.write_all(&bytes).unwrap();
            }
            _ => out.write_all(&[0]).unwrap(),
        }
        out.flush().unwrap();
    }
}
