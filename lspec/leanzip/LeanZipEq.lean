import Zip.Spec.Deflate
import Lspec

/-!
# lean-zip's DEFLATE spec against the Lean spec

lean-zip (github.com/kim-em/lean-zip, by Kim Morrison) has its own spec decoder,
`Deflate.Spec.decode`, written independently from RFC 1951. We use it with the fix for
kim-em/lean-zip#2586, which makes it reject a dynamic header declaring more than 286
literal/length or 30 distance codes, as zlib does. This file shows the two specs then
differ in exactly one place: lean-zip also rejects HDIST 30 and 31 (31 or 32 distance
codes), which RFC 1951 allows and this spec accepts with its zlib flag off.

* `LeanZipSpec.inflate` is `Deflate.inflate` with the HLIT check widened to
  `nlit ≤ 286 && ndist ≤ 30`, and nothing else changed.
* `leanzip_goR_eq`: lean-zip's `decode.goR` on a byte string's bits is
  `LeanZipSpec.inflate`: the same verdict, the same data, the same bits left over.
* `LeanZipSpec.inflate_spec`: whatever lean-zip decodes, `Deflate.inflate` decodes the
  same.
* `LeanZipSpec.inflate_of_zlib`: whatever `Deflate.inflate` decodes with the zlib flag on,
  lean-zip decodes the same.
-/

namespace LeanZipSpec

open Deflate

/-- `Deflate.dynHeader` with zlib's count check `ndist ≤ 30` next to open point 4. -/
def dynHeader (b : Bits) (p : Nat) : Option (Lens × Lens × Nat × Bool) := do
  let hlit ← getbits b p 5
  let hdist ← getbits b (p + 5) 5
  let hclen ← getbits b (p + 10) 4
  let nlit := hlit + 257
  let ndist := hdist + 1
  guard (nlit ≤ 286 && ndist ≤ 30)
  let (cl, q) ← readCL b (p + 14) (hclen + 4)
  guard (notOversub cl)
  let (lens, r) ← readLens (code cl) b q (nlit + ndist) #[]
  let lit := lens.extract 0 nlit
  let dist := lens.extract nlit (nlit + ndist)
  guard (lit.getD 256 0 ≠ 0)
  guard (notOversub lit && notOversub dist)
  let zlib := zlibOk cl true && zlibOk lit false && zlibOk dist false && ndist ≤ 30
  some (lit, dist, r, zlib)

/-- `Deflate.block` with `LeanZipSpec.dynHeader`. -/
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
  | _ => none

/-- `Deflate.inflateBlocks` with `LeanZipSpec.block`. -/
def inflateBlocks (b : Bits) (p : Nat) (out : Array UInt8) (zlib : Bool) :
    Option (Array UInt8 × Nat × Bool) := do
  let bfinal ← getbits b p 1
  let btype ← getbits b (p + 1) 2
  let (o, q, z) ← block b (p + 3) btype out
  if bfinal = 1 then
    some (o, q, zlib && z)
  else if _h : p < q ∧ q ≤ b.size then
    inflateBlocks b q o (zlib && z)
  else none
termination_by b.size - p

/-- `Deflate.inflate` with `LeanZipSpec.inflateBlocks`. -/
def inflate (b : Bits) : Option Decoded := do
  let (out, bits, zlib) ← inflateBlocks b 0 #[] true
  some { out, bits, zlib }

/-! ## `LeanZipSpec` is the Lean spec with one more check, which zlib makes too -/

theorem dynHeader_spec {b : Bits} {p : Nat} {r : Lens × Lens × Nat × Bool}
    (h : dynHeader b p = some r) : Deflate.dynHeader b p = some r := by
  unfold dynHeader at h
  unfold Deflate.dynHeader
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨hlit, h1, hdist, h2, hclen, h3, u, hg, h⟩ := h
  refine ⟨hlit, h1, hdist, h2, hclen, h3, (), ?_, h⟩
  have : hlit + 257 ≤ 286 := by
    by_cases hc : (decide (hlit + 257 ≤ 286) && decide (hdist + 1 ≤ 30)) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1
    · rw [Bridge.guard_neg' hc] at hg; simp at hg
  exact Bridge.guard_pos' this

/-- The zlib flag of a dynamic header includes `ndist ≤ 30`. -/
theorem dynHeader_of_zlib {b : Bits} {p : Nat} {lit dist : Lens} {q : Nat}
    (h : Deflate.dynHeader b p = some (lit, dist, q, true)) : dynHeader b p = some (lit, dist, q, true) := by
  unfold Deflate.dynHeader at h
  unfold dynHeader
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨hlit, h1, hdist, h2, hclen, h3, u, hg, h⟩ := h
  refine ⟨hlit, h1, hdist, h2, hclen, h3, (), ?_, h⟩
  have hn : hlit + 257 ≤ 286 := by
    by_cases hc : hlit + 257 ≤ 286
    · exact hc
    · rw [Bridge.guard_neg' hc] at hg; simp at hg
  -- the zlib flag being true forces `hdist + 1 ≤ 30`
  have hd : hdist + 1 ≤ 30 := by
    obtain ⟨⟨cl, q'⟩, -, h⟩ := h
    obtain ⟨-, -, h⟩ := h
    obtain ⟨⟨lens, r⟩, -, h⟩ := h
    obtain ⟨-, -, h⟩ := h
    obtain ⟨-, -, h⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.2.2.2
  exact Bridge.guard_pos' (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hn, hd⟩)

theorem block_spec {b : Bits} {p t : Nat} {out : Array UInt8} {r : Array UInt8 × Nat × Bool}
    (h : block b p t out = some r) : Deflate.block b p t out = some r := by
  unfold block at h
  unfold Deflate.block
  split at h
  · exact h
  · exact h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨x, hx, h⟩ := h
    exact ⟨x, dynHeader_spec hx, h⟩
  · simp at h

theorem block_of_zlib {b : Bits} {p t : Nat} {out o : Array UInt8} {q : Nat}
    (h : Deflate.block b p t out = some (o, q, true)) : block b p t out = some (o, q, true) := by
  unfold Deflate.block at h
  unfold block
  split at h
  · exact h
  · exact h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨⟨lit, dist, q', z⟩, hx, h⟩ := h
    obtain ⟨⟨o', r⟩, hs, h⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, dynHeader_of_zlib hx, _, hs, rfl⟩
  · simp at h

theorem inflateBlocks_spec (b : Bits) (p : Nat) (out : Array UInt8) (z : Bool)
    (r : Array UInt8 × Nat × Bool) (h : inflateBlocks b p out z = some r) :
    Deflate.inflateBlocks b p out z = some r := by
  induction p, out, z using inflateBlocks.induct b generalizing r with
  | case1 p out z ih =>
    rw [inflateBlocks] at h
    rw [Deflate.inflateBlocks]
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨bf, h1, bt, h2, ⟨o, q, z'⟩, h3, h⟩ := h
    refine ⟨bf, h1, bt, h2, ⟨o, q, z'⟩, block_spec h3, ?_⟩
    split at h
    · simpa [*] using h
    · split at h
      · rename_i hf hq
        simp only [hf, ite_false, dif_pos hq]
        exact ih o q z' hq r h
      · simp at h

/-- The zlib flag only goes from true to false along the blocks. -/
theorem inflateBlocks_zlib (b : Bits) (p : Nat) (out o : Array UInt8) (z : Bool) (q : Nat)
    (h : Deflate.inflateBlocks b p out z = some (o, q, true)) : z = true := by
  induction p, out, z using Deflate.inflateBlocks.induct b generalizing o q with
  | case1 p out z ih =>
    rw [Deflate.inflateBlocks] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨bf, -, bt, -, ⟨o', q', z'⟩, -, h⟩ := h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true] at h; exact h.2.2.1
    · split at h
      · rename_i hq
        have := ih o' q' z' hq o q h
        simp only [Bool.and_eq_true] at this; exact this.1
      · simp at h

theorem inflateBlocks_of_zlib (b : Bits) (p : Nat) (out o : Array UInt8) (z : Bool) (q : Nat)
    (h : Deflate.inflateBlocks b p out z = some (o, q, true)) :
    inflateBlocks b p out z = some (o, q, true) := by
  induction p, out, z using Deflate.inflateBlocks.induct b generalizing o q with
  | case1 p out z ih =>
    rw [Deflate.inflateBlocks] at h
    rw [inflateBlocks]
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨bf, h1, bt, h2, ⟨o', q', z'⟩, h3, h⟩ := h
    have hz' : z' = true := by
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true] at h; exact h.2.2.2
      · split at h
        · have := inflateBlocks_zlib b q' o' o (z && z') q h
          simp only [Bool.and_eq_true] at this; exact this.2
        · simp at h
    subst hz'
    refine ⟨bf, h1, bt, h2, ⟨o', q', true⟩, block_of_zlib h3, ?_⟩
    split at h
    · simpa [*] using h
    · split at h
      · rename_i hf hq
        simp only [hf, ite_false, dif_pos hq]
        exact ih o' q' true hq o q h
      · simp at h

/-- **Whatever lean-zip's reading decodes, the Lean spec decodes the same.** -/
theorem inflate_spec {b : Bits} {d : Decoded} (h : inflate b = some d) :
    Deflate.inflate b = some d := by
  unfold inflate at h
  unfold Deflate.inflate
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨x, hx, h⟩ := h
  exact ⟨x, inflateBlocks_spec b 0 #[] true x hx, h⟩

/-- **Whatever the Lean spec decodes with the zlib flag on, lean-zip's reading decodes the
same.** -/
theorem inflate_of_zlib {b : Bits} {d : Decoded} (h : Deflate.inflate b = some d)
    (hz : d.zlib = true) : inflate b = some d := by
  unfold Deflate.inflate at h
  unfold inflate
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨⟨o, q, z⟩, hx, h⟩ := h
  simp only [Option.some.injEq] at h
  subst h
  simp only at hz
  subst hz
  exact ⟨_, inflateBlocks_of_zlib b 0 #[] o true q hx, rfl⟩

end LeanZipSpec

namespace LeanZipEq

open Deflate.Spec

/-! ## Bits -/

theorem flatMap_length (l : List UInt8) : (l.flatMap bytesToBits.byteToBits).length = l.length * 8 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, bytesToBits.byteToBits_length, ih, List.length_cons]
    omega

theorem flatMap_bits (l : List UInt8) (k : Nat) (h : k < (l.flatMap bytesToBits.byteToBits).length) :
    (l.flatMap bytesToBits.byteToBits)[k] =
      (l[k / 8]'(by rw [flatMap_length] at h; omega)).toNat.testBit (k % 8) := by
  induction l generalizing k with
  | nil => simp at h
  | cons x xs ih =>
    have hx : (bytesToBits.byteToBits x).length = 8 := bytesToBits.byteToBits_length x
    simp only [List.flatMap_cons] at h ⊢
    by_cases hk : k < 8
    · rw [List.getElem_append_left (by omega)]
      simp only [bytesToBits.byteToBits, List.getElem_ofFn]
      simp only [show k / 8 = 0 by omega, show k % 8 = k by omega, List.getElem_cons_zero]
    · rw [List.getElem_append_right (by omega)]
      rw [List.length_append, hx] at h
      simp only [hx]
      rw [ih (k - 8) (by omega)]
      simp only [hx, show k / 8 = (k - 8) / 8 + 1 by omega, List.getElem_cons_succ,
        show (k - 8) % 8 = k % 8 by omega]

theorem bytesToBits_eq (data : ByteArray) :
    bytesToBits data = (Deflate.bitsOf data.data).toList := by
  apply List.ext_getElem
  · rw [bytesToBits_length]
    simp only [Array.length_toList, Deflate.bitsOf, Array.size_ofFn, ByteArray.size]
  · intro k h1 h2
    unfold bytesToBits
    refine (flatMap_bits _ _ _).trans ?_
    simp [Deflate.bitsOf]

theorem readBitsLSB_eq (b : Deflate.Bits) (p n : Nat) (hp0 : p ≤ b.size) :
    readBitsLSB n (b.toList.drop p) =
      (Deflate.getbits b p n).map (fun v => (v, b.toList.drop (p + n))) := by
  induction n generalizing p with
  | zero => simp [readBitsLSB, Deflate.getbits, Deflate.lsbVal]; omega
  | succ n ih =>
    by_cases hp : p < b.size
    · rw [List.drop_eq_getElem_cons (by simp; omega), readBitsLSB, ih (p + 1) (by omega)]
      by_cases hn : p + 1 + n ≤ b.size
      · have e1 : Deflate.getbits b (p + 1) n = some (Deflate.lsbVal b (p + 1) n) := by
          simp [Deflate.getbits, hn]
        have e2 : Deflate.getbits b p (n + 1) = some (Deflate.lsbVal b p (n + 1)) := by
          unfold Deflate.getbits; rw [if_pos (by omega)]
        rw [e1, e2]
        simp only [Option.map_some, Deflate.lsbVal, Array.getD, hp, dite_true, Array.getElem_toList,
          show p + 1 + n = p + (n + 1) by omega]
        simp only [bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq, and_true]
        show (if b[p] = true then 1 else 0) + _ = (if b[p] = true then 1 else 0) + _
        omega
      · have e1 : Deflate.getbits b (p + 1) n = none := by simp [Deflate.getbits, hn]
        have e2 : Deflate.getbits b p (n + 1) = none := by
          unfold Deflate.getbits; rw [if_neg (by omega)]
        rw [e1, e2]; rfl
    · rw [List.drop_eq_nil_of_le (by simp; omega)]
      have e2 : Deflate.getbits b p (n + 1) = none := by
        unfold Deflate.getbits; rw [if_neg (by omega)]
      rw [e2]; rfl

/-! ## 3.2.2: lean-zip's canonical codes are the Lean spec's -/

open Huffman.Spec in
theorem countLengths_foldl (mb : Nat) (L : List Nat) (acc : Array Nat) (hs : acc.size = mb + 1) :
    (L.foldl (fun acc len => if len == 0 || len > mb then acc else acc.set! len (acc[len]! + 1)) acc).size
      = mb + 1 ∧
    ∀ l, 1 ≤ l → l ≤ mb →
      (L.foldl (fun acc len => if len == 0 || len > mb then acc else acc.set! len (acc[len]! + 1)) acc)[l]!
        = acc[l]! + L.count l := by
  induction L generalizing acc with
  | nil => simp [hs]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split
    · rename_i hx
      obtain ⟨h1, h2⟩ := ih acc hs
      refine ⟨h1, fun l hl1 hl2 => ?_⟩
      rw [h2 l hl1 hl2, List.count_cons]
      simp at hx
      have : x ≠ l := by omega
      simp [this]
    · rename_i hx
      have hs' : (acc.set! x (acc[x]! + 1)).size = mb + 1 := by simp [hs]
      obtain ⟨h1, h2⟩ := ih _ hs'
      refine ⟨h1, fun l hl1 hl2 => ?_⟩
      rw [h2 l hl1 hl2, List.count_cons]
      simp at hx
      by_cases hxl : x = l
      · subst hxl
        simp [Array.set!, Array.getElem!_eq_getD, Array.getD, hs, show x < mb + 1 by omega]; omega
      · simp [Array.set!, Array.getElem!_eq_getD, Array.getD, hs, Array.getElem_setIfInBounds, hxl,
          show l < mb + 1 by omega]

theorem countLengths_get (L : List Nat) (mb l : Nat) (hl1 : 1 ≤ l) (hl2 : l ≤ mb) :
    (Huffman.Spec.countLengths L mb)[l]! = L.count l := by
  unfold Huffman.Spec.countLengths
  rw [(countLengths_foldl mb L _ (by simp)).2 l hl1 hl2]
  simp [Array.getElem!_eq_getD, Array.getD, show l < mb + 1 by omega]

theorem countLengths_size (L : List Nat) (mb : Nat) : (Huffman.Spec.countLengths L mb).size = mb + 1 := by
  unfold Huffman.Spec.countLengths
  exact (countLengths_foldl mb L _ (by simp)).1

theorem countLengths_zero (L : List Nat) (mb : Nat) : (Huffman.Spec.countLengths L mb)[0]! = 0 := by
  unfold Huffman.Spec.countLengths
  generalize hacc : Array.replicate (mb + 1) 0 = acc
  have h0 : acc[0]! = 0 := by rw [← hacc]; simp [Array.getElem!_eq_getD, Array.getD]
  have hs : acc.size = mb + 1 := by rw [← hacc]; simp
  clear hacc
  induction L generalizing acc with
  | nil => simpa using h0
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split
    · exact ih acc h0 hs
    · rename_i hx
      simp at hx
      apply ih
      · simp [Array.set!, Array.getElem!_eq_getD, Array.getD, hs, Array.getElem_setIfInBounds,
          show (0 : Nat) < mb + 1 by omega, show x ≠ 0 by omega] at h0 ⊢
        exact h0
      · simp [hs]

theorem getElem!_set! (arr : Array Nat) (i v l : Nat) :
    (arr.set! i v)[l]! = if i = l ∧ i < arr.size then v else arr[l]! := by
  rw [Array.set!, getElem!_def, getElem!_def, Array.getElem?_setIfInBounds]
  by_cases h1 : i = l
  · subst h1; by_cases h2 : i < arr.size <;> simp [h2]
  · simp [h1]

theorem nextCodes_go_size (bl : Array Nat) (mb : Nat) (arr : Array Nat) (bits code : Nat)
    (hs : arr.size = mb + 1) : (Huffman.Spec.nextCodes.go bl mb arr bits code).size = mb + 1 := by
  induction h : mb + 1 - bits generalizing bits code arr with
  | zero => rw [Huffman.Spec.nextCodes.go, dif_pos (by omega)]; exact hs
  | succ k ih =>
    rw [Huffman.Spec.nextCodes.go, dif_neg (by omega)]
    exact ih _ (bits + 1) _ (by simp [hs]) (by omega)

theorem nextCodes_go_keep (bl : Array Nat) (mb : Nat) (arr : Array Nat) (bits code l : Nat)
    (hl : l < bits) : (Huffman.Spec.nextCodes.go bl mb arr bits code)[l]! = arr[l]! := by
  induction h : mb + 1 - bits generalizing bits code arr with
  | zero => rw [Huffman.Spec.nextCodes.go, dif_pos (by omega)]
  | succ k ih =>
    rw [Huffman.Spec.nextCodes.go, dif_neg (by omega)]
    simp only
    rw [ih _ (bits + 1) _ (by omega) (by omega), getElem!_set!, if_neg (by omega)]

theorem nextCodes_go_eq (L : List Nat) (mb : Nat) (arr : Array Nat) (bits code : Nat)
    (hs : arr.size = mb + 1) (hb : 1 ≤ bits)
    (hc : code = if bits = 1 then 0 else Deflate.nextCode L.toArray (bits - 1)) :
    ∀ l, bits ≤ l → l ≤ mb →
      (Huffman.Spec.nextCodes.go (Huffman.Spec.countLengths L mb) mb arr bits code)[l]! =
        Deflate.nextCode L.toArray l := by
  induction h : mb + 1 - bits generalizing bits code arr with
  | zero => intro l h1 h2; omega
  | succ k ih =>
    intro l h1 h2
    rw [Huffman.Spec.nextCodes.go, dif_neg (by omega)]
    have hcode : (code + (Huffman.Spec.countLengths L mb)[bits - 1]!) * 2 =
        Deflate.nextCode L.toArray bits := by
      by_cases h1' : bits = 1
      · subst h1'; simp [hc, countLengths_zero, Deflate.nextCode]
      · rw [hc, if_neg h1', countLengths_get L mb (bits - 1) (by omega) (by omega)]
        obtain ⟨c, rfl⟩ : ∃ c, bits = c + 1 := ⟨bits - 1, by omega⟩
        rw [Deflate.nextCode_succ _ (by omega)]
        simp [Deflate.blCount]; omega
    simp only
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rw [nextCodes_go_keep _ _ _ _ _ _ (by omega), getElem!_set!, if_pos (by omega), hcode]
    · exact ih _ (bits + 1) _ (by simp [hs]) (by omega)
        (by rw [if_neg (by omega), Nat.add_sub_cancel]; exact hcode) (by omega) l (by omega) h2

theorem nextCodes_eq (L : List Nat) (mb l : Nat) (h1 : 1 ≤ l) (h2 : l ≤ mb) :
    (Huffman.Spec.nextCodes (Huffman.Spec.countLengths L mb) mb)[l]! = Deflate.nextCode L.toArray l :=
  nextCodes_go_eq L mb _ 1 0 (by simp) (by omega) (by simp) l h1 h2

theorem foldl_count (xs : List Nat) (len a : Nat) :
    xs.foldl (fun acc l => if (l == len) = true then acc + 1 else acc) a = a + xs.count len := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, List.count_cons]
    by_cases h : x = len <;> simp [h] <;> omega

/-- lean-zip's codeword for a symbol is the Lean spec's code for it, as bits. -/
theorem codeFor_eq (L : List Nat) (mb s : Nat) (hs : s < L.length) (h1 : 1 ≤ L[s]) (h2 : L[s] ≤ mb) :
    Huffman.Spec.codeFor L mb s = some (Huffman.Spec.natToBits (Deflate.codeOf L.toArray s) L[s]) := by
  unfold Huffman.Spec.codeFor
  rw [dif_pos hs]
  simp only
  rw [if_neg (by simp; omega)]
  congr 2
  rw [nextCodes_eq L mb L[s] h1 h2, foldl_count]
  simp [Deflate.codeOf, Array.getD, hs]

theorem msbList_lt' (xs : List Bool) : Bridge.msbList xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [Bridge.msbList]
  | cons x t ih => rw [Bridge.msbList_cons, List.length_cons, Nat.pow_succ]; split <;> omega

theorem natToBits_msbList (xs : List Bool) : Huffman.Spec.natToBits (Bridge.msbList xs) xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons x t ih =>
    rw [Bridge.msbList_cons, List.length_cons, Huffman.Spec.natToBits]
    have hlt := msbList_lt' t
    congr 1
    · cases x
      · simp [Nat.testBit_lt_two_pow hlt]
      · simp [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
    · conv => rhs; rw [← ih]
      rw [Huffman.Spec.natToBits_eq_iff]
      intro i hi
      cases x
      · simp
      · simp [Nat.testBit_two_pow_add_gt hi]

theorem decode_some {α : Type} (table : List (Huffman.Spec.Codeword × α)) (bits : List Bool) (a : α)
    (r : List Bool) (h : Huffman.Spec.decode table bits = some (a, r)) :
    ∃ cw, (cw, a) ∈ table ∧ cw.IsPrefix bits ∧ r = bits.drop cw.length := by
  induction table with
  | nil => simp [Huffman.Spec.decode] at h
  | cons e es ih =>
    obtain ⟨cw, s⟩ := e
    simp only [Huffman.Spec.decode] at h
    split at h
    · rename_i hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨cw, List.mem_cons_self .., (Huffman.Spec.isPrefixOf_iff _ _).mp hp, rfl⟩
    · obtain ⟨cw', hm, hp, hr⟩ := ih h
      exact ⟨cw', List.mem_cons_of_mem _ hm, hp, hr⟩

theorem codeOf_lt (L : List Nat) (mb s : Nat) (hv : Huffman.Spec.ValidLengths L mb) (hs : s < L.length)
    (h1 : 1 ≤ L[s]) (h2 : L[s] ≤ mb) : Deflate.codeOf L.toArray s < 2 ^ L[s] := by
  have := Huffman.Spec.code_value_bound L mb s hv hs (by simp; omega)
  rw [nextCodes_eq L mb L[s] h1 h2, foldl_count] at this
  simpa [Deflate.codeOf, Array.getD, hs] using this

/-- lean-zip's Huffman decoding is the Lean spec's, for valid code lengths. -/
theorem decode_eq (L : List Nat) (mb : Nat) (hv : Huffman.Spec.ValidLengths L mb) (hmb : mb ≤ 15)
    (b : Deflate.Bits) (p : Nat) (hp : p ≤ b.size) :
    Huffman.Spec.decode ((Huffman.Spec.allCodes L mb).map fun (sym, cw) => (cw, sym)) (b.toList.drop p) =
      (Deflate.decodeSym (Deflate.code L.toArray) b p).map (fun x => (x.1, b.toList.drop x.2)) := by
  cases hd : Deflate.decodeSym (Deflate.code L.toArray) b p with
  | some x =>
    obtain ⟨s, q⟩ := x
    obtain ⟨hs, h1, h15, rfl, hq, hc⟩ := (Deflate.decodeSym_code_iff _ _ _ _ _).mp hd
    simp only [List.size_toArray] at hs
    simp only [List.getElem_toArray] at h1 h15 hc hq
    have hmbs : L[s] ≤ mb := hv.1 _ (List.getElem_mem hs)
    have hcw := codeFor_eq L mb s hs h1 hmbs
    have hmem : (Huffman.Spec.natToBits (Deflate.codeOf L.toArray s) L[s], s) ∈
        (Huffman.Spec.allCodes L mb).map fun (sym, cw) => (cw, sym) :=
      List.mem_map.mpr ⟨(s, _), (Huffman.Spec.allCodes_mem_iff _ _ _ _).mpr ⟨hs, hcw⟩, rfl⟩
    have hsplit : b.toList.drop p =
        Huffman.Spec.natToBits (Deflate.codeOf L.toArray s) L[s] ++ b.toList.drop (p + L[s]) := by
      rw [hc, ← Bridge.msbList_take b p L[s] hq]
      have hlen : ((b.toList.drop p).take L[s]).length = L[s] := by simp; omega
      conv => rhs; arg 1; arg 2; rw [← hlen]
      rw [natToBits_msbList, ← List.drop_drop, List.take_append_drop]
    rw [hsplit, Huffman.Spec.decode_prefix_free _ _ s _ hmem]
    · simp
    · intro cw1 s1 cw2 s2 m1 m2 hne
      obtain ⟨⟨t1, c1⟩, m1', e1⟩ := List.mem_map.mp m1
      obtain ⟨⟨t2, c2⟩, m2', e2⟩ := List.mem_map.mp m2
      simp only [Prod.mk.injEq] at e1 e2
      obtain ⟨rfl, rfl⟩ := e1
      obtain ⟨rfl, rfl⟩ := e2
      by_cases hst : t1 = t2
      · subst hst
        have a1 := ((Huffman.Spec.allCodes_mem_iff _ _ _ _).mp m1').2
        have a2 := ((Huffman.Spec.allCodes_mem_iff _ _ _ _).mp m2').2
        rw [a1] at a2
        exact absurd (by rw [Option.some.inj a2]) hne
      · exact Huffman.Spec.allCodes_prefix_free_of_ne L mb hv _ _ _ _ m1' m2' hst
  | none =>
    cases hdec : Huffman.Spec.decode ((Huffman.Spec.allCodes L mb).map fun (sym, cw) => (cw, sym))
        (b.toList.drop p) with
    | none => rfl
    | some y =>
      exfalso
      obtain ⟨a, r⟩ := y
      obtain ⟨cw, hm, hpre, -⟩ := decode_some _ _ _ _ hdec
      obtain ⟨⟨t, c⟩, hm', e⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at e
      obtain ⟨hc1, ht1⟩ := e
      subst hc1
      rw [ht1] at hm'
      obtain ⟨ha, hcf⟩ := (Huffman.Spec.allCodes_mem_iff _ _ _ _).mp hm'
      obtain ⟨hs', hlen, -⟩ := Huffman.Spec.codeFor_spec hcf
      have ⟨hl0, hlm⟩ := Huffman.Spec.codeFor_len_bounds hlen
      rw [codeFor_eq L mb a ha (by omega) hlm, Option.some.injEq] at hcf
      subst hcf
      have hpl := hpre.length_le
      rw [Huffman.Spec.natToBits_length] at hpl
      simp at hpl
      have hpb : p + L[a] ≤ b.size := by omega
      have htake := List.prefix_iff_eq_take.mp hpre
      rw [Huffman.Spec.natToBits_length] at htake
      have hmsb : Huffman.Spec.natToBits (Deflate.msbVal b p L[a]) L[a] = (b.toList.drop p).take L[a] := by
        rw [← Bridge.msbList_take b p L[a] hpb]
        have hlen : ((b.toList.drop p).take L[a]).length = L[a] := by simp; omega
        conv => lhs; arg 2; rw [← hlen]
        rw [natToBits_msbList]
      have heq := Huffman.Spec.natToBits_injective _ _ _ (codeOf_lt L mb a hv ha (by omega) hlm)
        (Deflate.msbVal_lt b p L[a]) (htake.trans hmsb.symm)
      have := (Deflate.decodeSym_code_iff (L.toArray) b p a (p + L[a])).mpr
        ⟨by simpa using ha, by simp; omega, by simp [Deflate.maxBits]; omega, by simp, by simpa using hpb,
          by simpa using heq⟩
      rw [hd] at this
      cases this

/-! ## 3.2.5: tables and LZ77 copies -/

theorem lengthBase_eq : ∀ k : Fin 29,
    lengthBase[k.val]? = some (Deflate.lenTable[k.val]!).1 ∧
    lengthExtra[k.val]? = some (Deflate.lenTable[k.val]!).2 := by decide

theorem distBase_eq : ∀ k : Fin 30,
    distBase[k.val]? = some (Deflate.distTable[k.val]!).1 ∧
    distExtra[k.val]? = some (Deflate.distTable[k.val]!).2 := by decide

theorem succ_mod (i d : Nat) (hd : 0 < d) :
    (i + 1) % d = if i % d + 1 = d then 0 else i % d + 1 := by
  have h1 := Nat.mod_lt i hd
  have h2 := Nat.div_add_mod i d
  split
  · rename_i h
    have : i + 1 = d * (i / d + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [this, Nat.mul_mod_right]
  · rename_i h
    have : i + 1 = d * (i / d) + (i % d + 1) := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- The Lean spec's byte-by-byte LZ77 copy is lean-zip's `List.ofFn` copy. -/
theorem lzCopy_toList (o : Array UInt8) (d n : Nat) (hd : 1 ≤ d) (hdo : d ≤ o.size) :
    (Deflate.lzCopy o d n).toList =
      o.toList ++ List.ofFn fun (i : Fin n) => o.toList[o.toList.length - d + (i.val % d)]! := by
  induction n generalizing o with
  | zero => simp [Deflate.lzCopy]
  | succ n ih =>
    rw [Deflate.lzCopy, ih _ (by simp; omega), List.ofFn_succ]
    have hx : o.getD (o.size - d) 0 = o.toList[o.toList.length - d + 0 % d]! := by
      simp [Array.getD, show o.size - d < o.size by omega, getElem!_def,
        List.getElem?_eq_getElem (show o.size - d < o.toList.length by simp; omega)]
    simp only [Array.toList_push, List.append_assoc, List.singleton_append, List.length_append,
      List.length_singleton, Array.length_toList, hx]
    congr 2
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_ofFn, Fin.val_succ]
    rw [succ_mod i d (by omega)]
    have hr := Nat.mod_lt i (show 0 < d by omega)
    simp only [Array.length_toList] at *
    split
    · rename_i h
      rw [show o.size + 1 - d + i % d = o.size by omega]
      simp [getElem!_def]
    · rename_i h
      rw [show o.size + 1 - d + i % d = o.size - d + (i % d + 1) by omega]
      have hlt : o.size - d + (i % d + 1) < o.size := by omega
      simp [getElem!_def, List.getElem?_append_left (show o.size - d + (i % d + 1) < o.toList.length by
        simp; omega)]

/-! ## 3.2.5: compressed data -/

theorem decode_eq' (L : List Nat) (hv : Huffman.Spec.ValidLengths L 15) (b : Deflate.Bits) (p : Nat)
    (hp : p ≤ b.size) :
    Huffman.Spec.decode (List.map (fun x => (x.snd, x.fst)) (Huffman.Spec.allCodes L)) (b.toList.drop p) =
      (Deflate.decodeSym (Deflate.code L.toArray) b p).map (fun x => (x.1, b.toList.drop x.2)) :=
  decode_eq L 15 hv (by omega) b p hp

theorem bind_none' {α β : Type} (x : Option α) : (x.bind fun _ => (none : Option β)) = none := by
  cases x <;> rfl

/-- lean-zip's symbol decoding then LZ77 resolution is the Lean spec's
`inflateSyms`. -/
theorem syms_eq (lit dist : List Nat) (hl : Huffman.Spec.ValidLengths lit 15)
    (hdv : Huffman.Spec.ValidLengths dist 15) (b : Deflate.Bits) (p : Nat) (o : Array UInt8) :
    p ≤ b.size →
    ((decodeSymbols lit dist (b.toList.drop p)).bind fun x =>
        (resolveLZ77 x.1 o.toList).map fun acc => (acc, x.2)) =
      (Deflate.inflateSyms (Deflate.code lit.toArray) (Deflate.code dist.toArray) b p o).map
        (fun r => (r.1.toList, b.toList.drop r.2)) := by
  induction p, o using Deflate.inflateSyms.induct (Deflate.code lit.toArray) b with
  | case1 p o hd =>
    intro hp
    rw [decodeSymbols, Deflate.inflateSyms, hd]
    simp only [decodeLitLen, Option.bind_eq_bind]
    rw [decode_eq lit 15 hl (by omega) b p hp, hd]
    rfl
  | case2 p o s p1 hd hs hg ih =>
    intro hp
    rw [decodeSymbols, Deflate.inflateSyms, hd]
    simp only [decodeLitLen, Option.bind_eq_bind]
    rw [decode_eq lit 15 hl (by omega) b p hp, hd]
    simp only [Option.map_some, Option.bind_some, hs, if_true, hg]
    simp only [pure, Option.bind_some, and_self, dite_true]
    rw [dif_pos (by simp; omega)]
    rw [← ih (by omega), Option.bind_assoc]
    congr 1
    funext x
    simp [Array.toList_push]
  | case3 p o s p1 hd hs hg =>
    exact absurd (Deflate.decodeSym_spec hd).2 hg
  | case4 p o p1 hd hs =>
    intro hp
    rw [decodeSymbols, Deflate.inflateSyms, hd]
    simp only [decodeLitLen, Option.bind_eq_bind]
    rw [decode_eq lit 15 hl (by omega) b p hp, hd]
    simp [pure]
  | case5 p o s p1 hd hs h256 ih =>
    intro hp
    have hsp := Deflate.decodeSym_spec hd
    rw [decodeSymbols, Deflate.inflateSyms, hd]
    simp only [decodeLitLen, Option.bind_eq_bind]
    rw [decode_eq lit 15 hl (by omega) b p hp, hd]
    simp only [Option.map_some, Option.bind_some, hs, h256, if_false, ite_false]
    simp only [pure, Option.bind_some]
    rw [if_neg (by simp; omega)]
    rcases Nat.lt_or_ge 285 s with h285 | h285
    · have hb : lengthBase[s - 257]? = none := by simp [lengthBase]; omega
      rw [hb, Bridge.lenTable_none _ (by omega)]
      rfl
    obtain ⟨hb1, hb2⟩ := lengthBase_eq ⟨s - 257, by omega⟩
    have hlt : Deflate.lenTable[s - 257]? = some (Deflate.lenTable[s - 257]!) := by
      have := Bridge.lenTable_eq ⟨s - 257, by omega⟩
      simp only at this
      rw [this]; simp [getElem!_def, this]
    simp only at hb1 hb2
    generalize Deflate.lenTable[s - 257]! = be at hb1 hb2 hlt
    obtain ⟨base, extra⟩ := be
    rw [hb1, hb2, hlt]
    simp only [Option.bind_some]
    rw [readBitsLSB_eq b p1 extra (by omega)]
    cases hg1 : Deflate.getbits b p1 extra with
    | none => rfl
    | some e =>
      have hg1' := Deflate.getbits_some hg1
      simp only [Option.map_some, Option.bind_some]
      rw [decode_eq' dist hdv b (p1 + extra) (by omega)]
      cases hd2 : Deflate.decodeSym (Deflate.code dist.toArray) b (p1 + extra) with
      | none => rfl
      | some x =>
        obtain ⟨ds, p3⟩ := x
        have hsp2 := Deflate.decodeSym_spec hd2
        simp only [Option.map_some, Option.bind_some]
        rcases Nat.lt_or_ge 29 ds with h29 | h29
        · have hb : distBase[ds]? = none := by simp [distBase]; omega
          rw [hb, Bridge.distTable_none _ (by omega)]
          rfl
        obtain ⟨hd1, hd2'⟩ := distBase_eq ⟨ds, by omega⟩
        have hdt := Bridge.distTable_eq ⟨ds, by omega⟩
        simp only at hd1 hd2' hdt
        have hdt' : Deflate.distTable[ds]? = some (Deflate.distTable[ds]!) := by
          rw [hdt]; simp [getElem!_def, hdt]
        have hdpos : 1 ≤ (Deflate.distTable[ds]!).1 := by
          simp [getElem!_def, hdt, Bridge.distBaseF]; split <;> omega
        generalize Deflate.distTable[ds]! = dd at hd1 hd2' hdt' hdpos
        obtain ⟨dbase, dextra⟩ := dd
        rw [hd1, hd2', hdt']
        simp only [Option.bind_some]
        rw [readBitsLSB_eq b p3 dextra (by omega)]
        cases hg2 : Deflate.getbits b p3 dextra with
        | none => rfl
        | some e2 =>
          have hg2' := Deflate.getbits_some hg2
          simp only [Option.map_some, Option.bind_some]
          rw [dif_pos (by simp; omega), Option.bind_assoc]
          by_cases hdo : dbase + e2 ≤ o.size
          · have hp4 : p < p3 + dextra ∧ p3 + dextra ≤ b.size := by omega
            rw [if_pos hdo, dif_pos hp4]
            rw [← ih base e p3 dbase dextra e2 hp4 hp4.2]
            refine congrArg (Option.bind (decodeSymbols lit dist _)) (funext fun x => ?_)
            simp only [Option.bind_some, resolveLZ77]
            rw [if_neg (by simp; omega), lzCopy_toList o _ _ (by omega) hdo]
          · rw [if_neg hdo]
            cases hds : decodeSymbols lit dist (List.drop (p3 + dextra) b.toList) with
            | none => rfl
            | some r =>
              simp only [Option.bind_some, resolveLZ77]
              rw [if_pos (by simp; omega)]
              rfl

/-! ## 3.2.4: stored blocks -/

theorem xor_ones (n a : Nat) (h : a < 2 ^ n) : a ^^^ (2 ^ n - 1) = 2 ^ n - 1 - a := by
  induction n generalizing a with
  | zero => simp at h; subst h; rfl
  | succ n ih =>
    have hd := Nat.xor_div_two_pow (a := a) (b := 2 ^ (n + 1) - 1) (n := 1)
    have hm := Nat.xor_mod_two_pow (a := a) (b := 2 ^ (n + 1) - 1) (n := 1)
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
    have e1 : (2 ^ (n + 1) - 1) / 2 ^ 1 = 2 ^ n - 1 := by rw [hp]; omega
    have e2 : (2 ^ (n + 1) - 1) % 2 ^ 1 = 1 := by rw [hp]; omega
    rw [e1, ih (a / 2 ^ 1) (by rw [hp] at h; omega)] at hd
    rw [e2] at hm
    have hr : a % 2 ^ 1 = 0 ∨ a % 2 ^ 1 = 1 := by omega
    have hx : a % 2 ^ 1 ^^^ 1 = 1 - a % 2 ^ 1 := by rcases hr with h | h <;> rw [h] <;> rfl
    rw [hx] at hm
    have := Nat.div_add_mod (a ^^^ (2 ^ (n + 1) - 1)) (2 ^ 1)
    rw [hd, hm] at this
    rw [← this]
    simp only [Nat.pow_one] at *
    rw [hp] at h ⊢
    omega

theorem xor_ffff (a b : Nat) (ha : a < 2 ^ 16) :
    (a ^^^ b == 0xFFFF) = decide (a + b = 65535) := by
  have key : a ^^^ b = 65535 ↔ b = a ^^^ 65535 := by
    constructor
    · intro h; rw [← h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    · intro h; rw [h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hc := xor_ones 16 a ha
  simp only [show (2 : Nat) ^ 16 - 1 = 65535 by rfl] at hc
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [show (0xFFFF : Nat) = 65535 by rfl, key, hc]
  omega

theorem readNBytes_eq (b : Deflate.Bits) (n r : Nat) (acc : List UInt8) (hr : r ≤ b.size) :
    decodeStored.readNBytes n (b.toList.drop r) acc =
      if r + 8 * n ≤ b.size then
        some (acc ++ List.ofFn (fun j : Fin n => (Deflate.lsbVal b (r + 8 * j.val) 8).toUInt8),
          b.toList.drop (r + 8 * n))
      else none := by
  induction n generalizing r acc with
  | zero => simp [decodeStored.readNBytes, hr]
  | succ n ih =>
    rw [decodeStored.readNBytes, readBitsLSB_eq b r 8 hr]
    by_cases h8 : r + 8 ≤ b.size
    · have hg : Deflate.getbits b r 8 = some (Deflate.lsbVal b r 8) := by
        unfold Deflate.getbits; rw [if_pos h8]
      rw [hg, Option.map_some]
      show decodeStored.readNBytes n (b.toList.drop (r + 8)) (acc ++ [(Deflate.lsbVal b r 8).toUInt8]) = _
      rw [ih (r + 8) _ h8]
      by_cases hn : r + 8 + 8 * n ≤ b.size
      · rw [if_pos hn, if_pos (show r + 8 * (n + 1) ≤ b.size by omega), List.ofFn_succ]
        simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, Fin.val_succ, List.append_assoc,
          List.singleton_append]
        have hf : (fun j : Fin n => (Deflate.lsbVal b (r + 8 * (j.val + 1)) 8).toUInt8) =
            (fun j : Fin n => (Deflate.lsbVal b (r + 8 + 8 * j.val) 8).toUInt8) := by
          funext j; rw [show r + 8 * (j.val + 1) = r + 8 + 8 * j.val by omega]
        rw [hf, show r + 8 * (n + 1) = r + 8 + 8 * n by omega]
      · rw [if_neg hn, if_neg (show ¬(r + 8 * (n + 1) ≤ b.size) by omega)]
    · have hg : Deflate.getbits b r 8 = none := by unfold Deflate.getbits; rw [if_neg h8]
      rw [hg, if_neg (show ¬(r + 8 * (n + 1) ≤ b.size) by omega)]
      rfl

theorem stored_eq (b : Deflate.Bits) (hb8 : b.size % 8 = 0) (p : Nat) (hp : p ≤ b.size) :
    decodeStored (b.toList.drop p) = (Deflate.stored b p).map (fun r => (r.1.toList, b.toList.drop r.2)) := by
  unfold decodeStored alignToByte Deflate.stored
  have hq : (p + 7) / 8 * 8 ≤ b.size := by omega
  rw [List.drop_drop, List.length_drop, Array.length_toList,
    show p + (b.size - p) % 8 = (p + 7) / 8 * 8 by omega]
  generalize (p + 7) / 8 * 8 = q at hq ⊢
  simp only [Option.bind_eq_bind]
  rw [readBitsLSB_eq b q 16 hq]
  cases h1 : Deflate.getbits b q 16 with
  | none => rfl
  | some len =>
    have h1' := Deflate.getbits_some h1
    simp only [Option.map_some, Option.bind_some]
    rw [readBitsLSB_eq b (q + 16) 16 (by omega)]
    cases h2 : Deflate.getbits b (q + 16) 16 with
    | none => rfl
    | some nlen =>
      have h2' := Deflate.getbits_some h2
      have hl16 : len < 2 ^ 16 := by rw [h1'.2]; exact Bridge.lsbVal_lt b _ 16
      simp only [Option.map_some, Option.bind_some]
      rw [xor_ffff len nlen hl16]
      by_cases hc : len + nlen = 65535
      · rw [Bridge.guard_pos' (by simp [hc]), Bridge.guard_pos' hc, Option.bind_some, Option.bind_some,
          show q + 16 + 16 = q + 32 by omega, readNBytes_eq b len (q + 32) [] (by omega)]
        by_cases hs : q + 32 + 8 * len ≤ b.size
        · rw [if_pos hs, Bridge.guard_pos' hs, Option.bind_some]
          simp [Array.toList_ofFn]
        · rw [if_neg hs, Bridge.guard_neg' hs]; rfl
      · rw [Bridge.guard_neg' (by simp [hc]), Bridge.guard_neg' hc]; rfl

/-! ## 3.2.7: the dynamic header -/

theorem codeLengthOrder_eq : codeLengthOrder = Deflate.clOrder := by decide

theorem readCLLengths_eq (b : Deflate.Bits) (p0 : Nat) :
    ∀ k i (acc : List Nat), i + k ≤ 19 → acc.length = 19 → p0 + 3 * i ≤ b.size →
      Deflate.Spec.readCLLengths k i acc (b.toList.drop (p0 + 3 * i)) =
        (Deflate.readCL.go b p0 (i + k) i acc.toArray).map (fun r => (r.1.toList, b.toList.drop r.2)) := by
  intro k
  induction k with
  | zero =>
    intro i acc _ _ _
    rw [Deflate.Spec.readCLLengths, Deflate.readCL.go, if_neg (by omega)]
    simp
  | succ k ih =>
    intro i acc hik hl hp
    rw [Deflate.Spec.readCLLengths, Deflate.readCL.go, if_pos (by omega), readBitsLSB_eq b _ 3 hp]
    cases hg : Deflate.getbits b (p0 + 3 * i) 3 with
    | none => rfl
    | some v =>
      have hg' := Deflate.getbits_some hg
      simp only [Option.map_some, bind, Option.bind]
      rw [show p0 + 3 * i + 3 = p0 + 3 * (i + 1) by omega,
        ih (i + 1) _ (by omega) (by simp [hl]) (by omega), show i + 1 + k = i + (k + 1) by omega,
        codeLengthOrder_eq]
      have hi : Deflate.clOrder[i]! = Deflate.clOrder.getD i 0 := by
        simp [getElem!_def, Array.getD, show i < Deflate.clOrder.size by simp [Deflate.clOrder]; omega]
      rw [hi]
      congr 2
      simp [Array.set!, Array.setIfInBounds, List.set_toArray]
      intro h; exact List.set_eq_of_length_le h

theorem foldl_add (f : Nat → Nat) (xs : List Nat) (a : Nat) :
    xs.foldl (fun acc l => acc + f l) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih]; simp; omega

theorem kraft_scale (L : List Nat) (mb : Nat) (hmb : mb ≤ 15) (hle : ∀ l ∈ L, l ≤ mb) :
    (L.map Bridge.kterm).sum = 2 ^ (15 - mb) * ((L.filter (· != 0)).map fun l => 2 ^ (mb - l)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hx := hle x (List.mem_cons_self ..)
    rw [List.map_cons, List.sum_cons, ih (fun l hl => hle l (List.mem_cons_of_mem _ hl))]
    by_cases h0 : x = 0
    · subst h0; simp [Bridge.kterm]
    · simp only [List.filter_cons, show (x != 0) = true by simp [h0], if_true, List.map_cons,
        List.sum_cons, Nat.mul_add]
      unfold Bridge.kterm Deflate.maxBits
      rw [if_pos (by omega), ← Nat.pow_add, show 15 - mb + (mb - x) = 15 - x by omega]

theorem valid_iff (L : List Nat) (mb : Nat) (hmb : mb ≤ 15) (hle : ∀ l ∈ L, l ≤ mb) :
    Huffman.Spec.ValidLengths L mb ↔ Deflate.notOversub L.toArray = true := by
  unfold Huffman.Spec.ValidLengths Deflate.notOversub Deflate.kraft
  rw [foldl_add, Nat.zero_add, decide_eq_true_iff, List.toList_toArray,
    show (List.map (fun len => if 1 ≤ len ∧ len ≤ Deflate.maxBits then 2 ^ (Deflate.maxBits - len) else 0) L) =
      L.map Bridge.kterm from rfl, kraft_scale L mb hmb hle, show Deflate.maxBits = 15 from rfl]
  have hp : 0 < 2 ^ (15 - mb) := Nat.two_pow_pos _
  have h15 : (2 : Nat) ^ 15 = 2 ^ (15 - mb) * 2 ^ mb := by rw [← Nat.pow_add]; congr 1; omega
  rw [h15]
  constructor
  · rintro ⟨-, h⟩; exact Nat.mul_le_mul_left _ h
  · intro h; exact ⟨hle, Nat.le_of_mul_le_mul_left h hp⟩

theorem back_mem {acc : Deflate.Lens} {v : Nat} (h : acc.back? = some v) : v ∈ acc.toList := by
  simp only [Array.back?] at h
  rw [Array.getElem?_eq_some_iff] at h
  obtain ⟨hi, rfl⟩ := h
  simp

theorem readLens_le (c : Array (Nat × Nat)) (b : Deflate.Bits) (total : Nat) :
    ∀ p (acc : Deflate.Lens) lens r, (∀ x ∈ acc.toList, x ≤ 15) →
      Deflate.readLens c b p total acc = some (lens, r) → ∀ x ∈ lens.toList, x ≤ 15 := by
  intro p acc
  induction p, acc using Deflate.readLens.induct c b total with
  | case1 p acc ht =>
    intro lens r hle h; rw [Deflate.readLens, dif_pos ht] at h; simp at h; rw [← h.1]; exact hle
  | case2 p acc ht hd =>
    intro lens r hle h; rw [Deflate.readLens, dif_neg ht, hd] at h; simp at h
  | case3 p acc ht s p1 hd hs ih =>
    intro lens r hle h
    rw [Deflate.readLens, dif_neg ht, hd] at h
    simp only [hs, ite_true] at h
    exact ih lens r (by intro x hx; simp at hx; rcases hx with hx | hx; exact hle x (by simpa using hx); omega) h
  | case4 p acc ht s p1 hd hs nb base ih =>
    intro lens r hle h
    rw [Deflate.readLens, dif_neg ht, hd] at h
    simp only [hs, ite_false, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨e, -, h⟩ := h
    simp only [nb, base, dite_eq_ite] at ih
    rcases (show s = 16 ∨ s = 17 ∨ s = 18 ∨ (s ≠ 16 ∧ s ≠ 17 ∧ s ≠ 18) by omega) with
      hs' | hs' | hs' | ⟨h16, h17, h18⟩
    all_goals
      first
      | (subst hs'; simp +decide only [↓reduceIte] at h ih)
      | simp only [h16, h17, h18, ite_false] at h ih
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, h⟩ := h
      split at h
      · refine ih e v lens r ?_ h
        intro x hx
        simp only [Array.toList_append, List.mem_append, Array.toList_replicate, List.mem_replicate] at hx
        rcases hx with hx | ⟨-, rfl⟩
        · exact hle x hx
        · first
          | (simp at hv; omega)
          | exact hle _ (back_mem hv)
      · simp at h

theorem getLast!_toList (acc : Array Nat) (x : Nat) (h : acc.back? = some x) : acc.toList.getLast! = x := by
  have hpos : 0 < acc.size := by
    rcases Nat.eq_zero_or_pos acc.size with h0 | h0
    · simp [Array.back?, h0] at h
    · exact h0
  simp only [Array.back?, Array.getElem?_eq_getElem (show acc.size - 1 < acc.size by omega),
    Option.some.injEq] at h
  rw [List.getLast!_eq_getElem!, getElem!_def, Array.length_toList,
    List.getElem?_eq_getElem (show acc.size - 1 < acc.toList.length by simp; omega)]
  simpa using h

theorem decodeCL_eq (cl : List Nat) (hv : Huffman.Spec.ValidLengths cl 7) (hcl : cl.length = 19)
    (b : Deflate.Bits) (total : Nat) : ∀ p (acc : Deflate.Lens), p ≤ b.size →
    decodeDynamicTables.decodeCLSymbols ((Huffman.Spec.allCodes cl 7).map fun (sym, cw) => (cw, sym))
        total acc.toList (b.toList.drop p) =
      (Deflate.readLens (Deflate.code cl.toArray) b p total acc).map
        (fun r => (r.1.toList, b.toList.drop r.2)) := by
  intro p acc
  induction p, acc using Deflate.readLens.induct (Deflate.code cl.toArray) b total with
  | case1 p acc ht =>
    intro hp
    rw [decodeDynamicTables.decodeCLSymbols, Deflate.readLens, dif_pos ht, if_pos (by simp; omega)]
    rfl
  | case2 p acc ht hd =>
    intro hp
    rw [decodeDynamicTables.decodeCLSymbols, Deflate.readLens, dif_neg ht, if_neg (by simp; omega),
      decode_eq cl 7 hv (by omega) b p hp, hd]
    rfl
  | case3 p acc ht s p1 hd hs ih =>
    intro hp
    have hsp := Deflate.decodeSym_spec hd
    rw [decodeDynamicTables.decodeCLSymbols, Deflate.readLens, dif_neg ht, if_neg (by simp; omega),
      decode_eq cl 7 hv (by omega) b p hp, hd]
    simp only [Option.map_some, hs, if_true]
    rw [show acc.toList ++ [s] = (acc.push s).toList by simp]
    exact ih (by omega)
  | case4 p acc ht s p1 hd hs nb base ih =>
    intro hp
    have hsp := Deflate.decodeSym_spec hd
    rw [Deflate.code_size] at hsp
    simp only [List.size_toArray, hcl] at hsp
    rw [decodeDynamicTables.decodeCLSymbols, Deflate.readLens, dif_neg ht, if_neg (by simp; omega),
      decode_eq cl 7 hv (by omega) b p hp, hd]
    simp only [Option.map_some, hs, if_false, ite_false]
    simp only [nb, base, dite_eq_ite] at ih
    rcases (show s = 16 ∨ s = 17 ∨ s = 18 by omega) with rfl | rfl | rfl
    · simp +decide only [↓reduceIte] at ih ⊢
      rw [readBitsLSB_eq b p1 2 (by omega)]
      cases hg : Deflate.getbits b p1 2 with
      | none => simp
      | some e =>
        have hg' := Deflate.getbits_some hg
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
        by_cases hacc : acc.size = 0
        · have hb : acc.back? = none := by simp [Array.back?, hacc]
          rw [if_pos (by simp [hacc]), hb]; rfl
        · obtain ⟨x, hb⟩ : ∃ x, acc.back? = some x := by
            simp only [Array.back?]
            exact ⟨_, Array.getElem?_eq_getElem (by omega)⟩
          have hl : acc.toList.getLast! = x := getLast!_toList acc x hb
          rw [if_neg (by simp only [Array.length_toList, beq_iff_eq]; exact hacc), hb, Option.bind_some, hl]
          by_cases hle : acc.size + (3 + e) ≤ total
          · rw [if_pos (by simp; omega), if_pos hle]
            have := ih e x (by omega)
            rw [Array.toList_append, Array.toList_replicate] at this
            rw [show e + 3 = 3 + e by omega]
            exact this
          · rw [if_neg (by simp; omega), if_neg hle]; rfl
    · simp +decide only [↓reduceIte] at ih ⊢
      rw [readBitsLSB_eq b p1 3 (by omega)]
      cases hg : Deflate.getbits b p1 3 with
      | none => simp
      | some e =>
        have hg' := Deflate.getbits_some hg
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
        by_cases hle : acc.size + (3 + e) ≤ total
        · rw [if_pos (by simp; omega), if_pos hle]
          have := ih e 0 (by omega)
          rw [Array.toList_append, Array.toList_replicate] at this
          rw [show e + 3 = 3 + e by omega]
          exact this
        · rw [if_neg (by simp; omega), if_neg hle]; rfl
    · simp +decide only [↓reduceIte] at ih ⊢
      rw [readBitsLSB_eq b p1 7 (by omega)]
      cases hg : Deflate.getbits b p1 7 with
      | none => simp
      | some e =>
        have hg' := Deflate.getbits_some hg
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
        by_cases hle : acc.size + (11 + e) ≤ total
        · rw [if_pos (by simp; omega), if_pos hle]
          have := ih e 0 (by omega)
          rw [Array.toList_append, Array.toList_replicate] at this
          rw [show e + 11 = 11 + e by omega]
          exact this
        · rw [if_neg (by simp; omega), if_neg hle]; rfl

theorem readCL_go_le7 (b : Deflate.Bits) (p hclen : Nat) :
    ∀ i (acc : Deflate.Lens) cl q, (∀ x ∈ acc.toList, x ≤ 7) →
      Deflate.readCL.go b p hclen i acc = some (cl, q) → ∀ x ∈ cl.toList, x ≤ 7 := by
  intro i acc
  induction i, acc using Deflate.readCL.go.induct hclen with
  | case1 i acc hi ih =>
    intro cl q hle h
    rw [Deflate.readCL.go, if_pos hi] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    have hv8 : v < 8 := by rw [(Deflate.getbits_some hv).2]; exact Bridge.lsbVal_lt b _ 3
    refine ih v cl q ?_ h
    intro x hx
    simp only [Array.set!, Array.toList_setIfInBounds] at hx
    rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · exact hle x hx
    · omega
  | case2 i acc hi =>
    intro cl q hle h
    rw [Deflate.readCL.go, if_neg hi] at h
    simp at h; rw [← h.1]; exact hle

/-- `LeanZipSpec.dynHeader` without the end-of-block check (open point 9), which
lean-zip makes later, when the block's symbols are read. -/
def dynTables (b : Deflate.Bits) (p : Nat) : Option (Deflate.Lens × Deflate.Lens × Deflate.Lens × Nat) := do
  let hlit ← Deflate.getbits b p 5
  let hdist ← Deflate.getbits b (p + 5) 5
  let hclen ← Deflate.getbits b (p + 10) 4
  let nlit := hlit + 257
  let ndist := hdist + 1
  guard (nlit ≤ 286 && ndist ≤ 30)
  let (cl, q) ← Deflate.readCL b (p + 14) (hclen + 4)
  guard (Deflate.notOversub cl)
  let (lens, r) ← Deflate.readLens (Deflate.code cl) b q (nlit + ndist) #[]
  let lit := lens.extract 0 nlit
  let dist := lens.extract nlit (nlit + ndist)
  guard (Deflate.notOversub lit && Deflate.notOversub dist)
  some (cl, lit, dist, r)

theorem readCL_go_bound (b : Deflate.Bits) (p hclen : Nat) :
    ∀ i (acc : Deflate.Lens) cl q, p + 3 * i ≤ b.size →
      Deflate.readCL.go b p hclen i acc = some (cl, q) → q ≤ b.size := by
  intro i acc
  induction i, acc using Deflate.readCL.go.induct hclen with
  | case1 i acc hi ih =>
    intro cl q hb h
    rw [Deflate.readCL.go, if_pos hi] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    exact ih v cl q (by have := (Deflate.getbits_some hv).1; omega) h
  | case2 i acc hi =>
    intro cl q hb h
    rw [Deflate.readCL.go, if_neg hi] at h
    simp at h; omega

theorem tables_eq (b : Deflate.Bits) (p : Nat) (hp : p ≤ b.size) :
    decodeDynamicTables (b.toList.drop p) =
      (dynTables b p).map (fun x => (x.2.1.toList, x.2.2.1.toList, b.toList.drop x.2.2.2)) := by
  unfold decodeDynamicTables dynTables
  simp only [Option.bind_eq_bind]
  rw [readBitsLSB_eq b p 5 hp]
  cases h1 : Deflate.getbits b p 5 with
  | none => rfl
  | some hlit =>
  have h1' := Deflate.getbits_some h1
  simp only [Option.map_some, Option.bind_some]
  rw [readBitsLSB_eq b (p + 5) 5 (by omega)]
  cases h2 : Deflate.getbits b (p + 5) 5 with
  | none => rfl
  | some hdist =>
  have h2' := Deflate.getbits_some h2
  simp only [Option.map_some, Option.bind_some]
  rw [show p + 5 + 5 = p + 10 by omega, readBitsLSB_eq b (p + 10) 4 (by omega)]
  cases h3 : Deflate.getbits b (p + 10) 4 with
  | none => rfl
  | some hclen =>
  have h3' := Deflate.getbits_some h3
  have hc16 : hclen < 16 := by rw [h3'.2]; exact Bridge.lsbVal_lt b _ 4
  simp only [Option.map_some, Option.bind_some]
  by_cases hng : ¬(decide (hlit + 257 ≤ 286) && decide (hdist + 1 ≤ 30)) = true
  · rw [Bridge.guard_neg' hng]; rfl
  rw [Bridge.guard_pos' (Decidable.of_not_not hng), Option.bind_some, Option.bind_some]
  have hrc := readCLLengths_eq b (p + 14) (hclen + 4) 0 (List.replicate 19 0) (by omega) (by simp)
    (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at hrc
  rw [show p + 10 + 4 = p + 14 by omega, hrc]
  unfold Deflate.readCL
  rw [show (List.replicate 19 0).toArray = Array.replicate 19 0 from rfl]
  cases hR : Deflate.readCL.go b (p + 14) (hclen + 4) 0 (Array.replicate 19 0) with
  | none => rfl
  | some x =>
  obtain ⟨cl, q⟩ := x
  have hcl : cl.size = 19 := Bridge.readCL_go_size b (p + 14) (hclen + 4) 0 _ cl q (by simp) hR
  have hle7 := readCL_go_le7 b (p + 14) (hclen + 4) 0 _ cl q (by simp) hR
  have hq := readCL_go_bound b (p + 14) (hclen + 4) 0 _ cl q (by omega) hR
  simp only [Option.map_some, Option.bind_some]
  have hvc := valid_iff cl.toList 7 (by omega) hle7
  rw [Array.toArray_toList] at hvc
  by_cases hov : Deflate.notOversub cl = true
  · rw [Bridge.guard_pos' (hvc.mpr hov), Bridge.guard_pos' hov, Option.bind_some, Option.bind_some]
    have hdc := decodeCL_eq cl.toList (hvc.mpr hov) (by simp [hcl]) b (hlit + 257 + (hdist + 1)) q #[] hq
    rw [Array.toArray_toList] at hdc
    rw [show ([] : List Nat) = (#[] : Deflate.Lens).toList from rfl, hdc]
    cases hL : Deflate.readLens (Deflate.code cl) b q (hlit + 257 + (hdist + 1)) #[] with
    | none => rfl
    | some y =>
    obtain ⟨lens, r⟩ := y
    have hsz := Bridge.readLens_size _ b _ q #[] lens r (by simp) hL
    have hle := readLens_le _ b _ q #[] lens r (by simp) hL
    simp only [Option.map_some, Option.bind_some]
    rw [Bridge.guard_pos' (by simp [hsz]), Option.bind_some]
    have et : (lens.extract 0 (hlit + 257)).toList = lens.toList.take (hlit + 257) := by
      simp [Array.toList_extract, List.extract]
    have ed : (lens.extract (hlit + 257) (hlit + 257 + (hdist + 1))).toList = lens.toList.drop (hlit + 257) := by
      simp only [Array.toList_extract, List.extract]
      rw [List.take_of_length_le (by simp; omega)]
    have x1 : lens.extract 0 (hlit + 257) = (lens.toList.take (hlit + 257)).toArray := by
      apply Array.toList_inj.mp; rw [et, List.toList_toArray]
    have x2 : lens.extract (hlit + 257) (hlit + 257 + (hdist + 1)) = (lens.toList.drop (hlit + 257)).toArray := by
      apply Array.toList_inj.mp; rw [ed, List.toList_toArray]
    have hv1 := valid_iff (lens.toList.take (hlit + 257)) 15 (by omega)
      (fun x hx => hle x (List.mem_of_mem_take hx))
    have hv2 := valid_iff (lens.toList.drop (hlit + 257)) 15 (by omega)
      (fun x hx => hle x (List.mem_of_mem_drop hx))
    rw [x1, x2]
    try simp only [List.toList_toArray]
    by_cases g1 : Deflate.notOversub (lens.toList.take (hlit + 257)).toArray = true
    · by_cases g2 : Deflate.notOversub (lens.toList.drop (hlit + 257)).toArray = true
      · have k : (Deflate.notOversub (lens.toList.take (hlit + 257)).toArray &&
            Deflate.notOversub (lens.toList.drop (hlit + 257)).toArray) = true := by simp [g1, g2]
        rw [Bridge.guard_pos' (hv1.mpr g1), Bridge.guard_pos' (hv2.mpr g2), Bridge.guard_pos' k]
        rfl
      · have k : ¬(Deflate.notOversub (lens.toList.take (hlit + 257)).toArray &&
            Deflate.notOversub (lens.toList.drop (hlit + 257)).toArray) = true := by simp [g2]
        have n2 : ¬Huffman.Spec.ValidLengths (lens.toList.drop (hlit + 257)) 15 := fun h => g2 (hv2.mp h)
        rw [Bridge.guard_pos' (hv1.mpr g1), Bridge.guard_neg' n2, Bridge.guard_neg' k]
        rfl
    · have k : ¬(Deflate.notOversub (lens.toList.take (hlit + 257)).toArray &&
          Deflate.notOversub (lens.toList.drop (hlit + 257)).toArray) = true := by simp [g1]
      have n1 : ¬Huffman.Spec.ValidLengths (lens.toList.take (hlit + 257)) 15 := fun h => g1 (hv1.mp h)
      rw [Bridge.guard_neg' n1, Bridge.guard_neg' k]
      rfl
  · rw [Bridge.guard_neg' (fun h => hov (hvc.mp h)), Bridge.guard_neg' hov]
    rfl

/-! ## 3.2.3: blocks and the stream -/

/-- Without a code for end-of-block, a block never ends. -/
theorem inflateSyms_no_eob (lit : Deflate.Lens) (h0 : lit.getD 256 0 = 0) (dist : Array (Nat × Nat))
    (b : Deflate.Bits) (p : Nat) (o : Array UInt8) :
    Deflate.inflateSyms (Deflate.code lit) dist b p o = none := by
  induction p, o using Deflate.inflateSyms.induct (Deflate.code lit) b with
  | case1 p o hd => rw [Deflate.inflateSyms, hd]
  | case2 p o s p1 hd hs hg ih => rw [Deflate.inflateSyms, hd]; simp [hs, hg, ih]
  | case3 p o s p1 hd hs hg => rw [Deflate.inflateSyms, hd]; simp [hs, hg]
  | case4 p o p1 hd hs =>
    exfalso
    obtain ⟨h256, h1, -⟩ := (Deflate.decodeSym_code_iff _ _ _ _ _).mp hd
    simp [Array.getD, h256] at h0; omega
  | case5 p o s p1 hd hs h256 ih =>
    rw [Deflate.inflateSyms, hd]
    simp only [hs, h256, if_false, ite_false, Option.bind_eq_bind]
    cases h1 : Deflate.lenTable[s - 257]? with
    | none => rfl
    | some x =>
    obtain ⟨base, extra⟩ := x
    simp only [Option.bind_some]
    cases h2 : Deflate.getbits b p1 extra with
    | none => rfl
    | some e =>
    simp only [Option.bind_some]
    cases h3 : Deflate.decodeSym dist b (p1 + extra) with
    | none => rfl
    | some y =>
    obtain ⟨ds, p3⟩ := y
    simp only [Option.bind_some]
    cases h4 : Deflate.distTable[ds]? with
    | none => rfl
    | some z =>
    obtain ⟨dbase, dextra⟩ := z
    simp only [Option.bind_some]
    cases h5 : Deflate.getbits b p3 dextra with
    | none => rfl
    | some e2 =>
    simp only [Option.bind_some]
    split
    · split
      · rename_i _ hg; exact ih base e p3 dbase dextra e2 hg
      · rfl
    · rfl

theorem dynHeader_tables (b : Deflate.Bits) (p : Nat) :
    (LeanZipSpec.dynHeader b p).map (fun x => (x.1, x.2.1, x.2.2.1)) =
      (dynTables b p).bind (fun x => if x.2.1.getD 256 0 ≠ 0 then some (x.2.1, x.2.2.1, x.2.2.2) else none) := by
  unfold LeanZipSpec.dynHeader dynTables
  simp only [Option.bind_eq_bind]
  cases Deflate.getbits b p 5 with
  | none => rfl
  | some hlit =>
  cases Deflate.getbits b (p + 5) 5 with
  | none => rfl
  | some hdist =>
  cases Deflate.getbits b (p + 10) 4 with
  | none => rfl
  | some hclen =>
  simp only [Option.bind_some]
  by_cases hng : ¬(decide (hlit + 257 ≤ 286) && decide (hdist + 1 ≤ 30)) = true
  · rw [Bridge.guard_neg' hng]; rfl
  rw [Bridge.guard_pos' (Decidable.of_not_not hng), Option.bind_some, Option.bind_some]
  cases Deflate.readCL b (p + 14) (hclen + 4) with
  | none => rfl
  | some x =>
  obtain ⟨cl, q⟩ := x
  simp only [Option.bind_some]
  by_cases h1 : Deflate.notOversub cl = true
  · rw [Bridge.guard_pos' h1, Option.bind_some, Option.bind_some]
    cases Deflate.readLens (Deflate.code cl) b q (hlit + 257 + (hdist + 1)) #[] with
    | none => rfl
    | some y =>
    obtain ⟨lens, r⟩ := y
    simp only [Option.bind_some]
    by_cases h3 : (Deflate.notOversub (lens.extract 0 (hlit + 257)) &&
        Deflate.notOversub (lens.extract (hlit + 257) (hlit + 257 + (hdist + 1)))) = true
    · rw [Bridge.guard_pos' h3]
      by_cases h2 : (lens.extract 0 (hlit + 257)).getD 256 0 ≠ 0
      · rw [Bridge.guard_pos' h2]
        simp only [Option.bind_some, Option.map_some, if_pos h2]
      · rw [Bridge.guard_neg' h2]
        simp only [Option.bind_some, Option.bind_none, Option.map_none, if_neg h2]
    · rw [Bridge.guard_neg' h3]
      by_cases h2 : (lens.extract 0 (hlit + 257)).getD 256 0 ≠ 0
      · rw [Bridge.guard_pos' h2]; rfl
      · rw [Bridge.guard_neg' h2]; rfl
  · rw [Bridge.guard_neg' h1]; rfl

theorem fixedLit_eq : fixedLitLengths = Deflate.fixedLit.toList := by decide +kernel

theorem fixedDist_eq : fixedDistLengths = Deflate.fixedDist.toList := by
  simp [fixedDistLengths, Deflate.fixedDist]

/-- lean-zip's three kinds of block, without what follows them in `decode.goR`. -/
def theirBlock (bt : Nat) (bits : List Bool) (acc : List UInt8) : Option (List UInt8 × List Bool) :=
  match bt with
  | 0 => (decodeStored bits).map fun x => (acc ++ x.1, x.2)
  | 1 => (decodeSymbols fixedLitLengths fixedDistLengths bits).bind fun x =>
      (resolveLZ77 x.1 acc).map fun a => (a, x.2)
  | 2 => (decodeDynamicTables bits).bind fun t => (decodeSymbols t.1 t.2.1 t.2.2).bind fun x =>
      (resolveLZ77 x.1 acc).map fun a => (a, x.2)
  | _ => none

theorem readLens_bound (c : Array (Nat × Nat)) (b : Deflate.Bits) (total : Nat) :
    ∀ p (acc : Deflate.Lens) lens r, p ≤ b.size →
      Deflate.readLens c b p total acc = some (lens, r) → r ≤ b.size := by
  intro p acc
  induction p, acc using Deflate.readLens.induct c b total with
  | case1 p acc ht =>
    intro lens r hp h; rw [Deflate.readLens, dif_pos ht] at h; simp at h; omega
  | case2 p acc ht hd =>
    intro lens r hp h; rw [Deflate.readLens, dif_neg ht, hd] at h; simp at h
  | case3 p acc ht s p1 hd hs ih =>
    intro lens r hp h
    rw [Deflate.readLens, dif_neg ht, hd] at h
    simp only [hs, ite_true] at h
    exact ih lens r (Deflate.decodeSym_spec hd).2.2 h
  | case4 p acc ht s p1 hd hs nb base ih =>
    intro lens r hp h
    have hsp := Deflate.decodeSym_spec hd
    rw [Deflate.readLens, dif_neg ht, hd] at h
    simp only [hs, ite_false, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨e, he, h⟩ := h
    have he' := Deflate.getbits_some he
    simp only [nb, base, dite_eq_ite] at ih he'
    rcases (show s = 16 ∨ s = 17 ∨ s = 18 ∨ (s ≠ 16 ∧ s ≠ 17 ∧ s ≠ 18) by omega) with
      hs' | hs' | hs' | ⟨h16, h17, h18⟩
    all_goals
      first
      | (subst hs'; simp +decide only [↓reduceIte] at h ih he')
      | simp only [h16, h17, h18, ite_false] at h ih he'
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨v, -, h⟩ := h
      split at h
      · exact ih e v lens r (by omega) h
      · simp at h

theorem dynTables_props {b : Deflate.Bits} {p : Nat} {x : Deflate.Lens × Deflate.Lens × Deflate.Lens × Nat}
    (h : dynTables b p = some x) :
    Huffman.Spec.ValidLengths x.2.1.toList 15 ∧ Huffman.Spec.ValidLengths x.2.2.1.toList 15 ∧
      x.2.2.2 ≤ b.size := by
  unfold dynTables at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨hlit, -, hdist, -, hclen, h3, -, -, ⟨cl, q⟩, hR, u1, hg1, ⟨lens, r⟩, hL, u2, hg2, h⟩ := h
  have h3' := Deflate.getbits_some h3
  simp only [Option.some.injEq] at h
  subst h
  rw [Deflate.guard_some] at hg2
  simp only [Bool.and_eq_true] at hg2 hL ⊢
  have hle := readLens_le _ b _ q #[] lens r (by simp) hL
  have hq : q ≤ b.size := by
    unfold Deflate.readCL at hR
    exact readCL_go_bound b (p + 14) (hclen + 4) 0 _ cl q (by omega) hR
  refine ⟨?_, ?_, readLens_bound _ b _ q #[] lens r hq hL⟩
  · rw [valid_iff _ 15 (by omega) (fun y hy => hle y (by
      simp only [Array.toList_extract, List.extract] at hy
      first | exact List.mem_of_mem_drop (List.mem_of_mem_take hy) | exact List.mem_of_mem_take hy)),
      Array.toArray_toList]
    exact hg2.1
  · rw [valid_iff _ 15 (by omega) (fun y hy => hle y (by
      simp only [Array.toList_extract, List.extract] at hy
      first | exact List.mem_of_mem_drop (List.mem_of_mem_take hy) | exact List.mem_of_mem_take hy)),
      Array.toArray_toList]
    exact hg2.2

theorem block_eq (b : Deflate.Bits) (hb8 : b.size % 8 = 0) (p bt : Nat) (hp : p ≤ b.size)
    (o : Array UInt8) :
    theirBlock bt (b.toList.drop p) o.toList =
      (LeanZipSpec.block b p bt o).map (fun r => (r.1.toList, b.toList.drop r.2.1)) := by
  rcases (show bt = 0 ∨ bt = 1 ∨ bt = 2 ∨ 3 ≤ bt by omega) with rfl | rfl | rfl | h3
  · simp only [theirBlock, LeanZipSpec.block, Option.bind_eq_bind]
    rw [stored_eq b hb8 p hp]
    cases Deflate.stored b p with
    | none => rfl
    | some x => simp [Array.toList_append]
  · simp only [theirBlock, LeanZipSpec.block, Option.bind_eq_bind]
    have hv1 := fixedLitLengths_valid
    have hv2 := fixedDistLengths_valid
    rw [fixedLit_eq, fixedDist_eq] at *
    rw [syms_eq _ _ hv1 hv2 b p o hp, Array.toArray_toList, Array.toArray_toList]
    cases Deflate.inflateSyms (Deflate.code Deflate.fixedLit) (Deflate.code Deflate.fixedDist) b p o with
    | none => rfl
    | some x => rfl
  · simp only [theirBlock, LeanZipSpec.block, Option.bind_eq_bind]
    rw [tables_eq b p hp]
    have hdt := dynHeader_tables b p
    cases hT : dynTables b p with
    | none =>
      rw [hT] at hdt
      have : LeanZipSpec.dynHeader b p = none := by
        cases h : LeanZipSpec.dynHeader b p with
        | none => rfl
        | some y => rw [h] at hdt; cases hdt
      rw [this]; rfl
    | some x =>
      obtain ⟨cl, lit, dist, r⟩ := x
      obtain ⟨hv1, hv2, hr⟩ := dynTables_props hT
      rw [hT] at hdt
      simp only [Option.map_some, Option.bind_some]
      rw [syms_eq _ _ hv1 hv2 b r o hr, Array.toArray_toList, Array.toArray_toList]
      simp only [Option.bind_some] at hdt
      by_cases h256 : lit.getD 256 0 ≠ 0
      · rw [if_pos h256] at hdt
        cases h : LeanZipSpec.dynHeader b p with
        | none => rw [h] at hdt; cases hdt
        | some y =>
          obtain ⟨lit', dist', r', z⟩ := y
          rw [h] at hdt
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hdt
          obtain ⟨rfl, rfl, rfl⟩ := hdt
          simp only [Option.bind_some]
          cases Deflate.inflateSyms (Deflate.code lit') (Deflate.code dist') b r' o with
          | none => rfl
          | some w => rfl
      · rw [if_neg h256] at hdt
        have : LeanZipSpec.dynHeader b p = none := by
          cases h : LeanZipSpec.dynHeader b p with
          | none => rfl
          | some y => rw [h] at hdt; cases hdt
        rw [this, inflateSyms_no_eob lit (by simpa using h256)]
        rfl
  · obtain ⟨k, rfl⟩ : ∃ k, bt = k + 3 := ⟨bt - 3, by omega⟩
    rfl

theorem goR_unfold (bits : List Bool) (acc : List UInt8) :
    decode.goR bits acc =
      (readBitsLSB 1 bits).bind fun x => (readBitsLSB 2 x.2).bind fun y =>
        (theirBlock y.1 y.2 acc).bind fun z =>
          if x.1 == 1 then some z
          else if _h : z.2.length < bits.length then decode.goR z.2 z.1 else none := by
  rw [decode.goR]
  simp only [Option.bind_eq_bind]
  cases readBitsLSB 1 bits with
  | none => rfl
  | some x =>
  obtain ⟨bf, r1⟩ := x
  simp only [Option.bind_some]
  cases readBitsLSB 2 r1 with
  | none => rfl
  | some y =>
  obtain ⟨bt, r2⟩ := y
  simp only [Option.bind_some]
  rcases (show bt = 0 ∨ bt = 1 ∨ bt = 2 ∨ 3 ≤ bt by omega) with rfl | rfl | rfl | h3
  · simp only [theirBlock]
    cases decodeStored r2 with
    | none => rfl
    | some w => rfl
  · simp only [theirBlock]
    cases decodeSymbols fixedLitLengths fixedDistLengths r2 with
    | none => rfl
    | some w =>
      simp only [Option.bind_some]
      cases resolveLZ77 w.1 acc with
      | none => rfl
      | some a => rfl
  · simp only [theirBlock]
    cases decodeDynamicTables r2 with
    | none => rfl
    | some t =>
      simp only [Option.bind_some]
      cases decodeSymbols t.1 t.2.1 t.2.2 with
      | none => rfl
      | some w =>
        simp only [Option.bind_some]
        cases resolveLZ77 w.1 acc with
        | none => rfl
        | some a => rfl
  · obtain ⟨k, rfl⟩ : ∃ k, bt = k + 3 := ⟨bt - 3, by omega⟩
    rfl

theorem dynTables_ge {b : Deflate.Bits} {p : Nat} {x : Deflate.Lens × Deflate.Lens × Deflate.Lens × Nat}
    (h : dynTables b p = some x) : p ≤ x.2.2.2 := by
  unfold dynTables at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨hlit, -, hdist, -, hclen, -, -, -, ⟨cl, q⟩, hR, u1, -, ⟨lens, r⟩, hL, u2, -, h⟩ := h
  simp only [Option.some.injEq] at h
  subst h
  unfold Deflate.readCL at hR
  have h1 := Deflate.readCL_go_pos b (p + 14) (hclen + 4) _ _ _ _ hR
  have h2 := Deflate.readLens_ge _ _ _ _ _ _ _ hL
  simp only at h2 ⊢
  omega

theorem leanzip_block_bounds {b : Deflate.Bits} {p t : Nat} {o o' : Array UInt8} {q : Nat} {z : Bool}
    (h : LeanZipSpec.block b p t o = some (o', q, z)) : p < q ∧ q ≤ b.size := by
  unfold LeanZipSpec.block at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨bytes, q'⟩, hs, h⟩ := h
    simp at h; obtain ⟨-, rfl, -⟩ := h
    exact Deflate.stored_bounds hs
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨o2, q'⟩, hs, h⟩ := h
    simp at h; obtain ⟨-, rfl, -⟩ := h
    exact Deflate.inflateSyms_bounds _ _ _ _ _ _ _ hs
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨lit, dist, q', zl⟩, hd, h⟩ := h
    obtain ⟨⟨o2, r⟩, hs, h⟩ := h
    simp at h; obtain ⟨-, rfl, -⟩ := h
    have h3 := Deflate.inflateSyms_bounds _ _ _ _ _ _ _ hs
    have hdt := dynHeader_tables b p
    rw [hd] at hdt
    simp only [Option.map_some] at hdt
    cases hT : dynTables b p with
    | none => rw [hT] at hdt; cases hdt
    | some x =>
      rw [hT] at hdt
      simp only [Option.bind_some] at hdt
      split at hdt
      · simp only [Option.some.injEq, Prod.mk.injEq] at hdt
        have := dynTables_ge hT
        simp only at h3 ⊢
        omega
      · cases hdt
  · simp at h

theorem goR_eq (b : Deflate.Bits) (hb8 : b.size % 8 = 0) (p : Nat) (o : Array UInt8) (z : Bool) :
    p ≤ b.size →
    decode.goR (b.toList.drop p) o.toList =
      (LeanZipSpec.inflateBlocks b p o z).map (fun r => (r.1.toList, b.toList.drop r.2.1)) := by
  induction p, o, z using LeanZipSpec.inflateBlocks.induct b with
  | case1 p o z ih =>
    intro hp
    rw [goR_unfold, LeanZipSpec.inflateBlocks]
    simp only [Option.bind_eq_bind]
    rw [readBitsLSB_eq b p 1 hp]
    cases h1 : Deflate.getbits b p 1 with
    | none => rfl
    | some bf =>
    have h1' := Deflate.getbits_some h1
    simp only [Option.map_some, Option.bind_some]
    rw [readBitsLSB_eq b (p + 1) 2 (by omega)]
    cases h2 : Deflate.getbits b (p + 1) 2 with
    | none => rfl
    | some bt =>
    have h2' := Deflate.getbits_some h2
    simp only [Option.map_some, Option.bind_some]
    rw [show p + 1 + 2 = p + 3 by omega, block_eq b hb8 (p + 3) bt (by omega) o]
    cases hB : LeanZipSpec.block b (p + 3) bt o with
    | none => rfl
    | some x =>
    obtain ⟨o', q, z'⟩ := x
    have hq := leanzip_block_bounds hB
    simp only [Option.map_some, Option.bind_some]
    by_cases hf : bf = 1
    · rw [if_pos (by simp [hf]), if_pos hf]; rfl
    · rw [if_neg (by simp [hf]), if_neg hf, dif_pos (by simp; omega), dif_pos (by omega)]
      exact ih o' q z' (by omega) hq.2

theorem decode_go_goR : ∀ (bits : List Bool) (acc : List UInt8),
    decode.go bits acc = (decode.goR bits acc).map Prod.fst := by
  intro bits
  induction h : bits.length using Nat.strongRecOn generalizing bits with
  | _ n ih =>
    intro acc
    rw [decode.go, decode.goR]
    simp only [Option.bind_eq_bind]
    cases readBitsLSB 1 bits with
    | none => rfl
    | some x =>
    obtain ⟨bf, r1⟩ := x
    simp only [Option.bind_some]
    cases readBitsLSB 2 r1 with
    | none => rfl
    | some y =>
    obtain ⟨bt, r2⟩ := y
    simp only [Option.bind_some]
    have step : ∀ (acc' : List UInt8) (r3 : List Bool),
        (if bf == 1 then pure acc' else if _h : r3.length < bits.length then decode.go r3 acc' else none) =
          Option.map Prod.fst
            (if bf == 1 then pure (acc', r3) else if _h : r3.length < bits.length then decode.goR r3 acc' else none) := by
      intro acc' r3
      by_cases hf : (bf == 1) = true
      · simp [hf, pure]
      · simp only [hf, Bool.false_eq_true, ite_false]
        by_cases hl : r3.length < bits.length
        · rw [dif_pos hl, dif_pos hl]; exact ih r3.length (by omega) r3 rfl acc'
        · rw [dif_neg hl, dif_neg hl]; rfl
    rcases (show bt = 0 ∨ bt = 1 ∨ bt = 2 ∨ 3 ≤ bt by omega) with rfl | rfl | rfl | h3
    · cases decodeStored r2 with
      | none => rfl
      | some w => exact step _ _
    · cases decodeSymbols fixedLitLengths fixedDistLengths r2 with
      | none => rfl
      | some w =>
        simp only [Option.bind_some]
        cases resolveLZ77 w.1 acc with
        | none => rfl
        | some a => exact step _ _
    · cases decodeDynamicTables r2 with
      | none => rfl
      | some t =>
        simp only [Option.bind_some]
        cases decodeSymbols t.1 t.2.1 t.2.2 with
        | none => rfl
        | some w =>
          simp only [Option.bind_some]
          cases resolveLZ77 w.1 acc with
          | none => rfl
          | some a => exact step _ _
    · obtain ⟨k, rfl⟩ : ∃ k, bt = k + 3 := ⟨bt - 3, by omega⟩
      rfl

/-- **lean-zip's spec decoder is the Lean spec without open point 4**: on any byte
string, `decode.goR` gives what `LeanZipSpec.inflate` gives, the decoded data and the bits
after the stream. -/
theorem leanzip_goR_eq (data : ByteArray) :
    decode.goR (bytesToBits data) [] =
      (LeanZipSpec.inflate (Deflate.bitsOf data.data)).map
        (fun d => (d.out.toList, (bytesToBits data).drop d.bits)) := by
  have hb8 : (Deflate.bitsOf data.data).size % 8 = 0 := by simp [Deflate.bitsOf]
  rw [bytesToBits_eq]
  have := goR_eq (Deflate.bitsOf data.data) hb8 0 #[] true (by omega)
  simp only [List.drop_zero, Array.toList_empty] at this
  rw [this]
  unfold LeanZipSpec.inflate
  simp only [Option.bind_eq_bind]
  cases LeanZipSpec.inflateBlocks (Deflate.bitsOf data.data) 0 #[] true with
  | none => rfl
  | some x => rfl

/-- The same for lean-zip's `decode`, which its `DecodesTo` is defined by. -/
theorem leanzip_decode_eq (data : ByteArray) :
    decode (bytesToBits data) = (LeanZipSpec.inflate (Deflate.bitsOf data.data)).map (fun d => d.out.toList) := by
  unfold decode
  rw [decode_go_goR, leanzip_goR_eq]
  cases LeanZipSpec.inflate (Deflate.bitsOf data.data) with
  | none => rfl
  | some d => rfl

/-- **Everything the Lean spec decodes with the zlib flag on, lean-zip's spec decodes the
same.** -/
theorem decodesTo_of_inflate (data : ByteArray) (d : Deflate.Decoded)
    (h : Deflate.inflateBytes data.data = some d) (hz : d.zlib = true) :
    DecodesTo data ⟨d.out⟩ := by
  unfold DecodesTo
  rw [leanzip_decode_eq, LeanZipSpec.inflate_of_zlib h hz]
  rfl

/-- **Everything lean-zip's spec decodes, the Lean spec decodes the same.** -/
theorem inflate_of_decodesTo (data out : ByteArray) (h : DecodesTo data out) :
    ∃ d, Deflate.inflateBytes data.data = some d ∧ d.out = out.data := by
  unfold DecodesTo at h
  rw [leanzip_decode_eq] at h
  cases hd : LeanZipSpec.inflate (Deflate.bitsOf data.data) with
  | none => simp [hd] at h
  | some d =>
    simp only [hd, Option.map_some, Option.some.injEq] at h
    exact ⟨d, LeanZipSpec.inflate_spec hd, Array.toList_inj.mp h⟩

end LeanZipEq
