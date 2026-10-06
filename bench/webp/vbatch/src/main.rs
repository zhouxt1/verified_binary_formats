// vwebp's verified VP8 decoder (vp8_x) behind the batch protocol of
// difftest/webp's ffydec: records of a u32 length and a bare VP8 frame; for
// each, a status byte, and for a frame its width, height and Y, U, V planes.
use std::io::{Read, Write};
use std::os::unix::io::FromRawFd;
fn main() {
    let mut inp = std::io::stdin().lock();
    // Straight to fd 1: Rust's stdout is line buffered, and scans every
    // plane written through it for a newline.
    let mut out = std::io::BufWriter::new(unsafe { std::fs::File::from_raw_fd(1) });
    loop {
        let mut len = [0u8; 4];
        if inp.read_exact(&mut len).is_err() { break; }
        let mut buf = vec![0u8; u32::from_le_bytes(len) as usize];
        inp.read_exact(&mut buf).unwrap();
        match vwebp::vp8::dec::vp8_x(&buf, 1 << 28) {
            Ok(f) => {
                out.write_all(&[1]).unwrap();
                out.write_all(&(f.w as u32).to_le_bytes()).unwrap();
                out.write_all(&(f.h as u32).to_le_bytes()).unwrap();
                out.write_all(&f.y).unwrap(); out.write_all(&f.u).unwrap(); out.write_all(&f.v).unwrap();
            }
            Err(_) => out.write_all(&[0]).unwrap(),
        }
        out.flush().unwrap();
    }
}
