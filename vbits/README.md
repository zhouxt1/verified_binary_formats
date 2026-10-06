# vbits: verified bit fields over byte buffers

`vbits` is the bit layer the codecs in this repository share. It has no
encoding rules of its own: it gives a byte buffer a bit view, and reads and
writes bit fields in it, with Verus proofs that each read returns the bits
the view holds and each write changes only the bits it names.

* `bitspec`, `bytebits`: the ghost model, bytes as a most-significant-bit-
  first bit sequence, and that view of a byte buffer.
* `prim_read`, `prim_write`, `fastload`, `faststore`: the primitive reads
  and writes (`read_bits`, ...), and the word-at-a-time loads and stores
  they use.
* `lsb`: the least-significant-bit-first view that DEFLATE and Brotli pack
  their bits in, and its window loads (`load_le64`, `peek_lsb`, ...).

There is no `assume` and no `external_body`. `vdeflate`, `vbrotli`,
`vwebp`, `vsyn` and `vh26x` are built on it, and so is
[vasn](https://github.com/zhouxt1/vasn), the verified ASN.1 PER codecs.

```bash
cargo verus verify -p vbits
```
