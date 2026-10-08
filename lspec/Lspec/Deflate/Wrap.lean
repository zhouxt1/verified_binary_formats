import Lspec.Deflate.Spec

/-!
# RFC 1950 (zlib) and RFC 1952 (gzip): the containers around DEFLATE

The two formats that carry a DEFLATE stream, as functions on bytes. Each definition
cites the clause it reads; `docs/spec/rfc1950.txt` and `rfc1952.txt` are the texts
(`docs/spec/get.sh` fetches them). The DEFLATE stream is `Deflate.inflate` of the bits
of the bytes after the header. It may end inside a byte; the trailer starts at the next
byte boundary.

A decoded container gives the data, the number of bytes the container took (bytes after
it are not its), and the DEFLATE stream's zlib flag. zlib 1.3 makes every check listed
here, the same way, so the flag says whether zlib accepts the container too.

**Open points (the text leaves a choice; the choice made):**

1. *FDICT* (RFC 1950 2.2). A zlib stream used on its own has no preset dictionary, and
   2.3 says a decompressor "must reject any stream in which the FDICT flag is set".
   `zlibDecode` refuses it. `zlibDecodeDict` is for a format that supplies a
   dictionary: it is given one, and FDICT's DICTID must be its Adler-32.
2. *FLEVEL* (RFC 1950 2.2). "Not needed for decompression". Ignored.
3. *CINFO above 7* (RFC 1950 2.2). "Not allowed in this version". Refused.
4. *Bytes after ADLER32* (RFC 1950 2.2: "not part of the zlib stream") and after a gzip
   member's ISIZE. Not looked at; the result says where the container ended.
5. *Reserved FLG bits 5 to 7* (RFC 1952 2.3.1.2: a decompressor "must give an error
   indication if any reserved bit is non-zero"). Refused.
6. *CRC16, CRC32 and ISIZE* (RFC 1952 2.3.1.2: a decompressor "need not examine any other
   part of the header or trailer"). Checked, as zlib does: a member with a wrong check
   value is refused.
7. *FTEXT, MTIME, XFL, OS, the extra field's subfields, and the character set of FNAME
   and FCOMMENT* (RFC 1952 2.3.1). Not looked at, beyond skipping the fields.
8. *A gzip file* (RFC 1952 2.2: "a series of members ... with no additional information
   before, between, or after them"). `gzipFile` is one or more members back to back to
   the end of the input; anything else is refused.

The definitions stay in the fragment `Spec.lean` uses: total, first-order functions over
`Nat`, `Bool`, `UInt8`, `Option`, pairs, arrays and structures.
-/

namespace Deflate

/-! ## Reading numbers -/

/-- The byte at `i`, or 0 past the end (callers check the length first). -/
def byteAt (s : Array UInt8) (i : Nat) : Nat := (s.getD i 0).toNat

/-- Four bytes at `i`, the most significant first (RFC 1950 2.1). -/
def be32 (s : Array UInt8) (i : Nat) : Nat :=
  ((byteAt s i * 256 + byteAt s (i + 1)) * 256 + byteAt s (i + 2)) * 256 + byteAt s (i + 3)

/-- Two bytes at `i`, the least significant first (RFC 1952 2.1). -/
def le16 (s : Array UInt8) (i : Nat) : Nat := byteAt s i + 256 * byteAt s (i + 1)

/-- Four bytes at `i`, the least significant first (RFC 1952 2.1). -/
def le32 (s : Array UInt8) (i : Nat) : Nat := le16 s i + 65536 * le16 s (i + 2)

/-! ## RFC 1950 2.2 and 8.2: Adler-32 -/

/-- "s1 is the sum of all bytes, s2 is the sum of all s1 values. Both sums are done modulo
65521": the sums after the bytes from `i`, starting from `s1`, `s2`. -/
def adlerGo (s : Array UInt8) (i s1 s2 : Nat) : Nat × Nat :=
  if i < s.size then
    let s1' := (s1 + byteAt s i) % 65521
    adlerGo s (i + 1) s1' ((s2 + s1') % 65521)
  else (s1, s2)
termination_by s.size - i

/-- "s1 is initialized to 1, s2 to zero. The Adler-32 checksum is stored as s2*65536 +
s1". -/
def adler32 (s : Array UInt8) : Nat :=
  let (s1, s2) := adlerGo s 0 1 0
  s2 * 65536 + s1

/-! ## RFC 1952 2.3.1 and 8: CRC-32 -/

/-- One bit of the register: the appendix's `if (c & 1) c = 0xedb88320L ^ (c >> 1); else c
= c >> 1`. -/
def crcBit (c : Nat) : Nat := if c % 2 = 1 then (c / 2) ^^^ 0xEDB88320 else c / 2

/-- One byte: the appendix's `crc_table[(c ^ buf[n]) & 0xff] ^ (c >> 8)`, with the table
entry worked out bit by bit as `make_crc_table` does. -/
def crcByte (c : Nat) (x : UInt8) : Nat :=
  let c0 := c ^^^ x.toNat
  crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit (crcBit c0)))))))

/-- The register after the bytes from `i`. -/
def crcGo (s : Array UInt8) (i c : Nat) : Nat :=
  if h : i < s.size then crcGo s (i + 1) (crcByte c s[i]) else c
termination_by s.size - i

/-- The appendix's `update_crc` from 0: the register starts as all ones and is inverted at
the end. -/
def crc32 (s : Array UInt8) : Nat := crcGo s 0 0xFFFFFFFF ^^^ 0xFFFFFFFF

/-! ## A decoded container -/

/-- What a zlib stream or a gzip member decodes to. -/
structure Unwrapped where
  /-- The data. -/
  out : Array UInt8
  /-- How many bytes the container took. -/
  used : Nat
  /-- Whether zlib 1.3 accepts it too (the DEFLATE stream's flag). -/
  zlib : Bool
  deriving DecidableEq, Repr

/-- The byte after a DEFLATE stream of `bits` bits that starts at byte `h`: the stream
ends inside its last byte. -/
def afterStream (h bits : Nat) : Nat := h + (bits + 7) / 8

/-! ## RFC 1950 2.2: zlib -/

/-- CMF and FLG: "CM = 8 denotes the deflate compression method", "values of CINFO above 7
are not allowed" (open point 3), and "CMF*256 + FLG is a multiple of 31". -/
def zlibHeaderOk (cmf flg : Nat) : Bool :=
  cmf % 16 == 8 && cmf / 16 ≤ 7 && (cmf * 256 + flg) % 31 == 0

/-- FDICT, bit 5 of FLG. -/
def fdict (flg : Nat) : Bool := flg / 32 % 2 == 1

/-- The trailer after the data `o`, whose DEFLATE stream ended at byte `a`: "ADLER32 ...
a checksum value of the uncompressed data (excluding any dictionary data)". -/
def zlibTrailer (s : Array UInt8) (o : Array UInt8) (a : Nat) (z : Bool) : Option Unwrapped := do
  guard (a + 4 ≤ s.size)
  guard (be32 s a = adler32 o)
  some { out := o, used := a + 4, zlib := z }

/-- A zlib stream with no preset dictionary (open point 1). -/
def zlibDecode (s : Array UInt8) : Option Unwrapped := do
  guard (2 ≤ s.size)
  let cmf := byteAt s 0
  let flg := byteAt s 1
  guard (zlibHeaderOk cmf flg)
  guard (!fdict flg)
  let d ← inflate (bitsOf (s.extract 2 s.size))
  zlibTrailer s d.out (afterStream 2 d.bits) d.zlib

/-- A zlib stream that may use the preset dictionary `dict` (open point 1): "DICT is the
Adler-32 checksum of this sequence of bytes", and the dictionary is "initially fed to the
compressor without producing any compressed output", so the DEFLATE stream decodes with
`dict` as the output before it. Without FDICT this is `zlibDecode`. -/
def zlibDecodeDict (s dict : Array UInt8) : Option Unwrapped := do
  guard (2 ≤ s.size)
  let cmf := byteAt s 0
  let flg := byteAt s 1
  if fdict flg then
    guard (zlibHeaderOk cmf flg)
    guard (6 ≤ s.size)
    guard (be32 s 2 = adler32 dict)
    let (full, q, z) ← inflateBlocks (bitsOf (s.extract 6 s.size)) 0 dict true
    zlibTrailer s (full.extract dict.size full.size) (afterStream 6 q) z
  else zlibDecode s

/-! ## RFC 1952 2.3: a gzip member -/

/-- The first zero byte at or after `i`: the end of FNAME or FCOMMENT, "terminated by a zero
byte". -/
def zeroAt (s : Array UInt8) (i : Nat) : Option Nat :=
  if i < s.size then
    if byteAt s i = 0 then some i else zeroAt s (i + 1)
  else none
termination_by s.size - i

/-- A zero-terminated field at `i` if `present`: the position after it. -/
def skipZ (s : Array UInt8) (i : Nat) (present : Bool) : Option Nat :=
  if present then (zeroAt s i).map (· + 1) else some i

/-- The member header: "ID1 = 31 (0x1f), ID2 = 139 (0x8b)", "CM = 8 denotes the deflate
compression method", "reserved FLG bits must be zero" (open point 5), then MTIME, XFL and
OS, which are not looked at (open point 7), then the optional fields in their order. Gives
the position after it. -/
def gzipHeader (s : Array UInt8) : Option Nat := do
  guard (10 ≤ s.size)
  guard (byteAt s 0 = 0x1f && byteAt s 1 = 0x8b && byteAt s 2 = 8)
  let flg := byteAt s 3
  guard (flg / 32 = 0)
  -- FEXTRA: "XLEN bytes of extra field"
  let i1 ← if flg / 4 % 2 = 1 then do
      guard (12 ≤ s.size)
      guard (12 + le16 s 10 ≤ s.size)
      some (12 + le16 s 10)
    else some 10
  -- FNAME, then FCOMMENT
  let i2 ← skipZ s i1 (flg / 8 % 2 = 1)
  let i3 ← skipZ s i2 (flg / 16 % 2 = 1)
  -- FHCRC: "the two least significant bytes of the CRC32 for all bytes of the gzip header
  -- up to and not including the CRC16" (open point 6)
  if flg / 2 % 2 = 1 then do
    guard (i3 + 2 ≤ s.size)
    guard (le16 s i3 = crc32 (s.extract 0 i3) % 65536)
    some (i3 + 2)
  else some i3

/-- One gzip member: the header, the compressed blocks, then CRC32, "a Cyclic Redundancy
Check value of the uncompressed data", and ISIZE, "the size of the original
(uncompressed) input data modulo 2^32" (open point 6). -/
def gzipDecode (s : Array UInt8) : Option Unwrapped := do
  let h ← gzipHeader s
  let d ← inflate (bitsOf (s.extract h s.size))
  let a := afterStream h d.bits
  guard (a + 8 ≤ s.size)
  guard (le32 s a = crc32 d.out)
  guard (le32 s (a + 4) = d.out.size % 4294967296)
  some { out := d.out, used := a + 8, zlib := d.zlib }

/-! ## RFC 1952 2.2: a gzip file -/

/-- The members from byte `i` to the end, their data joined. -/
def gzipMembers (s : Array UInt8) (i : Nat) (acc : Array UInt8) : Option (Array UInt8) :=
  if i < s.size then do
    let u ← gzipDecode (s.extract i s.size)
    if 0 < u.used then  -- not reached otherwise: a member is at least 18 bytes
      gzipMembers s (i + u.used) (acc ++ u.out)
    else none
  else some acc
termination_by s.size - i

/-- "A gzip file consists of a series of members": one or more, up to the end (open
point 8). -/
def gzipFile (s : Array UInt8) : Option (Array UInt8) :=
  if s.size = 0 then none else gzipMembers s 0 #[]

end Deflate
