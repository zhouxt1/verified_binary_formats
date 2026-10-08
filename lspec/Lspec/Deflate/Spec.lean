/-!
# RFC 1951 (DEFLATE): the canonical spec

The decoding process of RFC 1951, section 3, as one function on the stream's
bits. Each definition cites the clause it reads; `docs/spec/rfc1951.txt` is
the text (`docs/spec/get.sh` fetches it).

`inflate b` is the decoded data, the number of bits the stream took (what
follows is not DEFLATE's), and whether zlib 1.3 also accepts the stream. The
decoder reads the RFC as leniently as the text allows. Where zlib is stricter
the stream decodes the same, and the flag is off. Where the text is silent,
the choice made is listed below and cited as "open point N" where it is made.

**Open points (the text is silent or ambiguous; the choice made):**

1. *Incomplete Huffman codes* (lengths that leave some bit strings with no
   symbol). The text forbids none, and 3.2.7 shows one (a single distance code
   of one bit). They decode. Only a bit string with no symbol is refused, when
   it is read. zlib refuses every incomplete code except a lit/length or
   distance code with a single code of length 1. Flag off.
2. *Over-subscribed codes* (lengths no prefix code has). 3.2.2's algorithm
   still assigns codes, but some of them have more bits than their length (the
   count runs past `2^len - 1`), so the lengths describe no code. Refused.
3. *HDIST = 30, 31* (31 or 32 distance codes). Allowed by 3.2.7's range 1-32.
   They decode. zlib refuses them. Flag off.
4. *HLIT = 30, 31* (287 or 288 lit/length codes). Outside 3.2.7's range
   257-286. Refused.
5. *Lit/length symbols 286, 287 and distance symbols 30, 31.* These "will never
   actually occur" (3.2.6), and the 3.2.5 tables have no row for them. Refused
   when read.
6. *Length symbol 284 with extra bits 31* (length 258). The 3.2.5 table says
   284 covers 227-257, and 258 has its own symbol, 285. It decodes as 258, like
   zlib.
7. *Bit order of extra bits.* 3.2.5 says extra bits are "a machine integer
   stored with the most-significant bit first". 3.1.1 says data elements other
   than Huffman codes are packed least significant bit first. They are read by
   3.1.1, as every decoder does. The 3.2.5 sentence is about the integer's
   value, not its packing.
8. *A distance past the first byte of output.* 3.2.3: "a distance cannot refer
   past the beginning of the output stream". Refused. (Preset dictionaries are
   RFC 1950's business.)
9. *A dynamic block with no code for end-of-block (symbol 256).* Such a block
   can never end. It is refused at the header, which changes no verdict.
10. *Repeat code 16 with no previous length*, or a run of lengths past
    HLIT + HDIST + 258. Refused.
11. *NLEN not the one's complement of LEN* (3.2.4). Refused. *BTYPE = 11*
    ("reserved (error)", 3.2.3). Refused.
12. *Bits after the final block, and the bits skipped to a stored block's byte
    boundary.* Not looked at. 3.2.4: "any bits of input up to the next byte
    boundary are ignored".

The definitions are kept in a fragment that other verifiers' logics express
directly: total, first-order functions over `Nat`, `Bool`, `UInt8`, `Option`,
pairs and arrays, with structural or measured recursion. Guards marked "not
reached" exist only to make a recursion's measure evident. `Guards.lean` shows
they always hold.
-/

namespace Deflate

/-! ## 3.1.1 Packing into bytes -/

/-- A DEFLATE stream as a sequence of bits. -/
abbrev Bits := Array Bool

/-- The bits of a byte sequence: "data elements are packed into bytes in order
of increasing bit number within the byte, i.e., starting with the
least-significant bit of the byte". -/
def bitsOf (bytes : Array UInt8) : Bits :=
  Array.ofFn (n := bytes.size * 8) fun i =>
    (bytes[i.val / 8]'(by have := i.isLt; omega)).toNat.testBit (i.val % 8)

/-- The `n` bits from `p` as a number, the first the least significant: "data
elements other than Huffman codes are packed starting with the
least-significant bit of the data element". -/
def lsbVal (b : Bits) (p : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if b.getD p false then 1 else 0) + 2 * lsbVal b (p + 1) n

/-- The `l` bits from `p` as a number, the first the most significant: "Huffman
codes are packed starting with the most-significant bit of the code". -/
def msbVal (b : Bits) (p : Nat) : Nat → Nat
  | 0 => 0
  | l + 1 => (if b.getD p false then 2 ^ l else 0) + msbVal b (p + 1) l

/-- A data element of `n` bits at `p`, if the stream has them. -/
def getbits (b : Bits) (p n : Nat) : Option Nat :=
  if p + n ≤ b.size then some (lsbVal b p n) else none

/-! ## 3.2.2 Use of Huffman coding in the "deflate" format -/

/-- The code lengths of an alphabet, one per symbol in symbol order. Length 0
means the symbol has no code. -/
abbrev Lens := Array Nat

/-- `MAX_BITS`: no DEFLATE code is longer. -/
def maxBits : Nat := 15

/-- Step 1: `bl_count[N]`, the number of codes of length `N`. -/
def blCount (lens : Lens) (N : Nat) : Nat :=
  lens.toList.count N

/-- Step 2: `next_code[bits]`, the smallest code of each length.
`code = (code + bl_count[bits-1]) << 1`, with `code = 0` and `bl_count[0] = 0`
to start. -/
def nextCode (lens : Lens) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | bits + 1 => 2 * (nextCode lens bits + blCount lens bits)

/-- Step 3: the code of symbol `n`. Codes of one length are consecutive in
symbol order from `next_code` of that length, so `n`'s code is that length's
`next_code` plus the number of earlier symbols with the same length. -/
def codeOf (lens : Lens) (n : Nat) : Nat :=
  let len := lens.getD n 0
  nextCode lens len + (lens.toList.take n).count len

/-- The code of an alphabet: each symbol's (length, code). A symbol of length 0
has no code and is never decoded. -/
def code (lens : Lens) : Array (Nat × Nat) :=
  Array.ofFn (n := lens.size) fun n => (lens[n], codeOf lens n)

/-- The symbol whose code is the `l` bits at `p`, if one is. -/
def symOfLen (c : Array (Nat × Nat)) (b : Bits) (p l : Nat) : Option Nat :=
  c.findIdx? (· == (l, msbVal b p l))

/-- Decode one symbol at `p` (3.2.1): read bits until they are some symbol's
code. Gives the symbol and the position after its code. The codes 3.2.2
assigns are prefix-free for any lengths, so at most one symbol's code begins
the bits. Trying the shortest length first only makes this a function
(`decodeSym_code_iff` in `Prefix.lean`). -/
def decodeSym (c : Array (Nat × Nat)) (b : Bits) (p : Nat) : Option (Nat × Nat) :=
  go 1
where
  go (l : Nat) : Option (Nat × Nat) :=
    if l = 0 ∨ maxBits < l ∨ b.size < p + l then none
    else match symOfLen c b p l with
      | some n => some (n, p + l)
      | none => go (l + 1)
  termination_by maxBits + 1 - l

/-- The Kraft sum of the lengths, in units of 2^-15: `Σ 2^(15 - len)` over the
symbols that have a code. -/
def kraft (lens : Lens) : Nat :=
  (lens.toList.map fun len => if 1 ≤ len ∧ len ≤ maxBits then 2 ^ (maxBits - len) else 0).sum

/-- Lengths that some prefix code has: the Kraft inequality (open point 2). -/
def notOversub (lens : Lens) : Bool := kraft lens ≤ 2 ^ maxBits

/-- Lengths whose code leaves no bit string without a symbol. -/
def complete (lens : Lens) : Bool := kraft lens == 2 ^ maxBits

/-- zlib 1.3's rule (`inftrees.c`, `inflate_table`). It accepts no codes at
all, or a complete code, or a single code of length 1 for a lit/length or
distance code but not the code length code (`clCode`). Open point 1. -/
def zlibOk (lens : Lens) (clCode : Bool) : Bool :=
  lens.all (· == 0) || complete lens ||
    (!clCode && blCount lens 1 == 1 && kraft lens == 2 ^ (maxBits - 1))

/-! ## 3.2.5 Compressed blocks (length and distance codes) -/

/-- The length table: (base length, extra bits) of symbols 257..285, in order,
transcribed from the table. Symbols 286, 287 have no row (open point 5). -/
def lenTable : Array (Nat × Nat) := #[
  (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (9, 0), (10, 0),  -- 257..264
  (11, 1), (13, 1), (15, 1), (17, 1),                               -- 265..268
  (19, 2), (23, 2), (27, 2), (31, 2),                               -- 269..272
  (35, 3), (43, 3), (51, 3), (59, 3),                               -- 273..276
  (67, 4), (83, 4), (99, 4), (115, 4),                              -- 277..280
  (131, 5), (163, 5), (195, 5), (227, 5),                           -- 281..284
  (258, 0)]                                                         -- 285

/-- The distance table: (base distance, extra bits) of distance symbols 0..29.
Symbols 30, 31 have no row (open point 5). -/
def distTable : Array (Nat × Nat) := #[
  (1, 0), (2, 0), (3, 0), (4, 0), (5, 1), (7, 1), (9, 2), (13, 2),  -- 0..7
  (17, 3), (25, 3), (33, 4), (49, 4), (65, 5), (97, 5),             -- 8..13
  (129, 6), (193, 6), (257, 7), (385, 7), (513, 8), (769, 8),       -- 14..19
  (1025, 9), (1537, 9), (2049, 10), (3073, 10), (4097, 11),         -- 20..24
  (6145, 11), (8193, 12), (12289, 12), (16385, 13), (24577, 13)]    -- 25..29

/-! ## 3.2.6 Compression with fixed Huffman codes (BTYPE=01) -/

/-- The fixed lit/length code lengths: 0-143 8 bits, 144-255 9, 256-279 7,
280-287 8. -/
def fixedLit : Lens :=
  Array.ofFn (n := 288) fun i =>
    if i.val < 144 then 8 else if i.val < 256 then 9 else if i.val < 280 then 7 else 8

/-- The fixed distance code lengths: "distance codes 0-31 are represented by
(fixed-length) 5-bit codes". -/
def fixedDist : Lens := Array.replicate 32 5

/-! ## 3.2.3 Details of block format, and compressed data (3.2.5) -/

/-- Copy `len` bytes from `d` back to the end of `out`, one at a time, so a copy
may overlap what it writes ("adds X,Y,X,Y,X to the output stream"). -/
def lzCopy (out : Array UInt8) (d : Nat) : Nat → Array UInt8
  | 0 => out
  | len + 1 => lzCopy (out.push (out.getD (out.size - d) 0)) d len

/-- The symbols of a compressed block from `p` up to its end-of-block code,
appended to `out`. Gives the output and the position after end-of-block. -/
def inflateSyms (lit dist : Array (Nat × Nat)) (b : Bits) (p : Nat) (out : Array UInt8) :
    Option (Array UInt8 × Nat) :=
  match decodeSym lit b p with
  | none => none
  | some (s, p1) =>
    if s < 256 then
      -- a literal byte
      if _h : p < p1 ∧ p1 ≤ b.size then  -- not reached otherwise
        inflateSyms lit dist b p1 (out.push s.toUInt8)
      else none
    else if s = 256 then
      -- end of block
      some (out, p1)
    else do
      -- a <length, backward distance> pair
      let (base, extra) ← lenTable[s - 257]?
      let e ← getbits b p1 extra
      let (ds, p3) ← decodeSym dist b (p1 + extra)
      let (dbase, dextra) ← distTable[ds]?
      let e2 ← getbits b p3 dextra
      let d := dbase + e2
      let p4 := p3 + dextra
      if d ≤ out.size then  -- open point 8
        if _h : p < p4 ∧ p4 ≤ b.size then  -- not reached otherwise
          inflateSyms lit dist b p4 (lzCopy out d (base + e))
        else none
      else none
termination_by b.size - p

/-! ## 3.2.7 Compression with dynamic Huffman codes (BTYPE=10) -/

/-- The order the code length code lengths come in. -/
def clOrder : Array Nat := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- The `hclen` code length code lengths at `p`, 3 bits each, in `clOrder`.
Gives the 19 lengths (symbols not given get 0) and the position after them. -/
def readCL (b : Bits) (p hclen : Nat) : Option (Lens × Nat) :=
  go 0 (Array.replicate 19 0)
where
  go (i : Nat) (acc : Lens) : Option (Lens × Nat) :=
    if i < hclen then do
      let v ← getbits b (p + 3 * i) 3
      go (i + 1) (acc.set! (clOrder.getD i 0) v)
    else some (acc, p + 3 * hclen)
  termination_by hclen - i

/-- Read code lengths with the code length code `cl` from `p` until there are
`total`, appended to `acc`. Symbols 0-15 are the lengths 0-15. 16 copies the
previous length 3-6 times (2 extra bits). 17 writes 0 3-10 times (3 bits). 18
writes 0 11-138 times (7 bits). One sequence runs across both alphabets: "the
code length repeat codes can cross from HLIT + 257 to the HDIST + 1 code
lengths". -/
def readLens (cl : Array (Nat × Nat)) (b : Bits) (p total : Nat) (acc : Lens) :
    Option (Lens × Nat) :=
  if _h : total ≤ acc.size then some (acc, p)
  else match decodeSym cl b p with
    | none => none
    | some (s, p1) =>
      if s < 16 then
        readLens cl b p1 total (acc.push s)
      else do
        let nb := if s = 16 then 2 else if s = 17 then 3 else 7
        let base := if s = 18 then 11 else 3
        let e ← getbits b p1 nb
        let rep := base + e
        let v ← if s = 16 then acc.back? else some 0  -- open point 10
        if acc.size + rep ≤ total then  -- open point 10
          readLens cl b (p1 + nb) total (acc ++ Array.replicate rep v)
        else none
termination_by total - acc.size
decreasing_by all_goals (simp_all; (repeat' split) <;> omega)

/-- A dynamic block's header at `p`: the lit/length and distance code lengths,
the position after them, and whether zlib accepts them. -/
def dynHeader (b : Bits) (p : Nat) : Option (Lens × Lens × Nat × Bool) := do
  let hlit ← getbits b p 5
  let hdist ← getbits b (p + 5) 5
  let hclen ← getbits b (p + 10) 4
  let nlit := hlit + 257
  let ndist := hdist + 1
  guard (nlit ≤ 286)  -- open point 4
  let (cl, q) ← readCL b (p + 14) (hclen + 4)
  guard (notOversub cl)  -- open point 2
  let (lens, r) ← readLens (code cl) b q (nlit + ndist) #[]
  let lit := lens.extract 0 nlit
  let dist := lens.extract nlit (nlit + ndist)
  guard (lit.getD 256 0 ≠ 0)  -- open point 9
  guard (notOversub lit && notOversub dist)  -- open point 2
  let zlib := zlibOk cl true && zlibOk lit false && zlibOk dist false && ndist ≤ 30
  some (lit, dist, r, zlib)

/-! ## 3.2.4 Non-compressed blocks (BTYPE=00) -/

/-- A stored block, from just after its 3 header bits at `p`. Skip to a byte
boundary, then LEN, NLEN ("the one's complement of LEN"), and LEN bytes. Gives
the bytes and the position after them. -/
def stored (b : Bits) (p : Nat) : Option (Array UInt8 × Nat) := do
  let q := (p + 7) / 8 * 8
  let len ← getbits b q 16
  let nlen ← getbits b (q + 16) 16
  guard (len + nlen = 65535)  -- open point 11
  guard (q + 32 + 8 * len ≤ b.size)
  some (Array.ofFn (n := len) fun j => (lsbVal b (q + 32 + 8 * j.val) 8).toUInt8, q + 32 + 8 * len)

/-! ## 3.2.3 Details of block format: the stream -/

/-- One block of type `btype` from `p`, just after its header, appended to
`out`. Gives the output, the position after the block, and whether zlib
accepts it. -/
def block (b : Bits) (p btype : Nat) (out : Array UInt8) : Option (Array UInt8 × Nat × Bool) :=
  match btype with
  | 0 => do
    let (bytes, q) ← stored b p
    some (out ++ bytes, q, true)
  | 1 => do
    let (o, q) ← inflateSyms (code fixedLit) (code fixedDist) b p out
    some (o, q, true)
  | 2 => do
    let (lit, dist, q, zlib) ← dynHeader b p
    let (o, r) ← inflateSyms (code lit) (code dist) b q out
    some (o, r, zlib)
  | _ => none  -- "11 - reserved (error)", open point 11

/-- The blocks from `p` up to and including the one with BFINAL set ("do ...
while not last block"), appended to `out`. -/
def inflateBlocks (b : Bits) (p : Nat) (out : Array UInt8) (zlib : Bool) :
    Option (Array UInt8 × Nat × Bool) := do
  let bfinal ← getbits b p 1
  let btype ← getbits b (p + 1) 2
  let (o, q, z) ← block b (p + 3) btype out
  if bfinal = 1 then
    some (o, q, zlib && z)
  else if _h : p < q ∧ q ≤ b.size then  -- not reached otherwise
    inflateBlocks b q o (zlib && z)
  else none
termination_by b.size - p

/-- What a DEFLATE stream decodes to. -/
structure Decoded where
  /-- The data. -/
  out : Array UInt8
  /-- How many bits of the input the stream took. -/
  bits : Nat
  /-- Whether zlib 1.3 accepts the stream too. -/
  zlib : Bool
  deriving Repr, DecidableEq

/-- A raw DEFLATE stream: `none` if the bits are not one, by RFC 1951. -/
def inflate (b : Bits) : Option Decoded := do
  let (out, bits, zlib) ← inflateBlocks b 0 #[] true
  some { out, bits, zlib }

/-- `inflate` on bytes. -/
def inflateBytes (bytes : Array UInt8) : Option Decoded :=
  inflate (bitsOf bytes)

end Deflate
