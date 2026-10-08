import Lspec.Deflate.Prefix

/-!
# puff's Huffman decoding, as a model for implementations in other verifiers

Mark Adler's `puff.c` (zlib `contrib/puff`) decodes a symbol from two tables:
`count[l]`, the number of symbols of each length, and `symbol[]`, the coded
symbols ordered by length and then by symbol. It reads the code one bit at a
time and keeps `first`, the first code of the current length, and `index`, the
number of symbols with shorter codes.

This file restates `decodeSym (code lens)` in that shape (`decode`) and proves
the two equal (`decode_eq`). The model is meant to be imported into another
verifier together with the spec (`vpuff/` imports it into Rocq), so it uses only
plain functions `Nat → Nat`, structural recursion and arithmetic, and its
theorems take their hypotheses about arrays through `getD`. The C proof then
only has to show that the C code computes this model.
-/

namespace Deflate.Puff

/-- How many of the symbols `0 .. n-1` have length `l`. -/
def cnt (len : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, l => cnt len n l + (if len n = l then 1 else 0)

/-- puff's `offs[l]`: where the symbols of length `l` start in the symbol
table, `Σ count j` for `1 ≤ j < l`. -/
def offs (count : Nat → Nat) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | l + 2 => offs count (l + 1) + count (l + 1)

/-- `Σ count j * 2^(L - j)` for `1 ≤ j ≤ L`: the codes of lengths `1..L` count
as this many `L`-bit strings. puff's `left` after length `L` is `2^L` minus it. -/
def kr (count : Nat → Nat) : Nat → Nat
  | 0 => 0
  | L + 1 => 2 * kr count L + count (L + 1)

/-- puff's `decode` (the bit-at-a-time version, `SLOW` in puff.c), reading bit
`q` of a stream of `nbits` bits as `bit q`. `k` lengths remain to try; at length
`len`, `code` holds the first `len - 1` bits, `first` is the first code of
length `len` and `index` the number of symbols with shorter codes. -/
def go (count symbol : Nat → Nat) (bit : Nat → Bool) (nbits p : Nat) :
    Nat → Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _, _, _ => none
  | k + 1, len, code, first, index =>
    if nbits < p + len then none
    else if code + (if bit (p + len - 1) then 1 else 0) < first + count len then
      some (symbol (index + (code + (if bit (p + len - 1) then 1 else 0) - first)), p + len)
    else
      go count symbol bit nbits p k (len + 1)
        (2 * (code + (if bit (p + len - 1) then 1 else 0))) (2 * (first + count len))
        (index + count len)

/-- Decode one symbol at bit `p`. -/
def decode (count symbol : Nat → Nat) (bit : Nat → Bool) (nbits p : Nat) : Option (Nat × Nat) :=
  go count symbol bit nbits p maxBits 1 0 0 0

/-- Bit `q` of a byte sequence, given its bytes. -/
def byteBit (byte : Nat → Nat) (q : Nat) : Bool := (byte (q / 8)).testBit (q % 8)

/-! ## Counting -/

theorem cnt_eq_count_take (lens : Lens) (n l : Nat) (hn : n ≤ lens.size) :
    cnt (lens.getD · 0) n l = (lens.toList.take n).count l := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    have hx : lens.toList[n]? = some (lens.getD n 0) := by
      simp [Array.getD, show n < lens.size by omega]
    rw [cnt, ih (by omega), List.take_add_one, hx, Option.toList_some, List.count_append,
      List.count_singleton]
    by_cases h : lens.getD n 0 = l <;> simp [h]

/-- `bl_count` counted puff's way. -/
theorem blCount_eq_cnt (lens : Lens) (l : Nat) :
    blCount lens l = cnt (lens.getD · 0) lens.size l := by
  rw [cnt_eq_count_take lens _ l (Nat.le_refl _), blCount, ← Array.length_toList, List.take_length]

theorem kr_zero (M : Nat) : kr (fun _ => 0) M = 0 := by
  induction M with
  | zero => rfl
  | succ M ih => simp [kr, ih]

theorem kr_add (c d : Nat → Nat) (M : Nat) :
    kr (fun l => c l + d l) M = kr c M + kr d M := by
  induction M with
  | zero => rfl
  | succ M ih => simp only [kr, ih]; omega

/-- One code of length `x` counts as `2^(M - x)` strings of `M` bits. -/
theorem kr_one (x M : Nat) :
    kr (fun l => if x = l then 1 else 0) M = if 1 ≤ x ∧ x ≤ M then 2 ^ (M - x) else 0 := by
  induction M with
  | zero => simp [kr]; omega
  | succ M ih =>
    simp only [kr, ih]
    by_cases h1 : x = M + 1
    · subst h1; simp [show ¬ (M + 1 ≤ M) by omega]
    · by_cases h2 : 1 ≤ x ∧ x ≤ M
      · have e : M + 1 - x = (M - x) + 1 := by omega
        simp [h1, h2, e, Nat.pow_succ, show 1 ≤ x ∧ x ≤ M + 1 from by omega]
        omega
      · have : ¬ (1 ≤ x ∧ x ≤ M + 1) := by omega
        simp [h1, h2, this]

theorem kraft_list (L : List Nat) :
    (L.map fun len => if 1 ≤ len ∧ len ≤ maxBits then 2 ^ (maxBits - len) else 0).sum =
      kr (fun l => L.count l) maxBits := by
  induction L with
  | nil => simp [kr_zero]
  | cons x L ih =>
    have : (fun l => (x :: L).count l) = fun l => L.count l + (if x = l then 1 else 0) := by
      funext l; rw [List.count_cons]; by_cases h : x = l <;> simp [h]
    rw [List.map_cons, List.sum_cons, ih, this, kr_add, kr_one]
    omega

/-- The codes counted by `kraft`, length by length. -/
theorem kraft_eq_kr (lens : Lens) : kraft lens = kr (blCount lens) maxBits := by
  rw [kraft, kraft_list]; rfl

/-! ## Decoding -/

theorem cnt_mono (len : Nat → Nat) (l : Nat) {m n : Nat} (h : m ≤ n) :
    cnt len m l ≤ cnt len n l := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with h | h
    · rw [h]; exact Nat.le_refl _
    · have := ih (by omega); rw [cnt]; omega

theorem cnt_lt (len : Nat → Nat) {j m : Nat} (hj : j < m) :
    cnt len j (len j) < cnt len m (len j) := by
  have := cnt_mono len (len j) (show j + 1 ≤ m by omega)
  rw [cnt, if_pos rfl] at this; omega

/-- The `c`-th symbol of length `l`. -/
theorem cnt_exists (len : Nat → Nat) (l : Nat) :
    ∀ N c, c < cnt len N l → ∃ m < N, len m = l ∧ cnt len m l = c := by
  intro N
  induction N with
  | zero => intro c h; simp [cnt] at h
  | succ N ih =>
    intro c h
    rw [cnt] at h
    by_cases hc : c < cnt len N l
    · obtain ⟨m, hm, h1, h2⟩ := ih c hc; exact ⟨m, by omega, h1, h2⟩
    · by_cases hl : len N = l
      · rw [if_pos hl] at h; exact ⟨N, by omega, hl, by omega⟩
      · rw [if_neg hl] at h; omega

theorem codeOf_eq_cnt (lens : Lens) {m : Nat} (hm : m < lens.size) :
    codeOf lens m = nextCode lens (lens.getD m 0) + cnt (lens.getD · 0) m (lens.getD m 0) := by
  rw [codeOf, cnt_eq_count_take lens m _ (by omega)]

theorem msbVal_succ (b : Bits) (p l : Nat) :
    msbVal b p (l + 1) = 2 * msbVal b p l + (if b.getD (p + l) false then 1 else 0) := by
  rw [msbVal_add b p l 1]
  simp only [msbVal]
  split <;> simp <;> omega

theorem getD_eq_getElem (lens : Lens) {m : Nat} (hm : m < lens.size) :
    lens.getD m 0 = lens[m] := by
  simp [Array.getD, hm]

/-- At length `len`, the symbols of that length have the codes
`first .. first + blCount - 1`, so the bits `c` are one of them exactly when
`c < first + blCount`, and then they are the `(c - first)`-th. -/
theorem symOfLen_hit (lens : Lens) (b : Bits) (p len : Nat)
    (h1 : nextCode lens len ≤ msbVal b p len)
    (h2 : msbVal b p len < nextCode lens len + blCount lens len) :
    ∃ m < lens.size, lens.getD m 0 = len ∧
      cnt (lens.getD · 0) m len = msbVal b p len - nextCode lens len ∧
      symOfLen (code lens) b p len = some m := by
  rw [blCount_eq_cnt] at h2
  obtain ⟨m, hm, hl, hc⟩ := cnt_exists (lens.getD · 0) len lens.size
    (msbVal b p len - nextCode lens len) (by omega)
  refine ⟨m, hm, hl, hc, ?_⟩
  rw [symOfLen, Array.findIdx?_eq_some_iff_getElem]
  refine ⟨by simpa [code_size] using hm, ?_, ?_⟩
  · rw [code_getElem]
    simp only [beq_iff_eq, Prod.mk.injEq]
    refine ⟨by rw [← getD_eq_getElem lens hm, hl], ?_⟩
    rw [codeOf_eq_cnt lens hm, hl, hc]; omega
  · intro j hj
    have hj' : j < lens.size := by omega
    rw [code_getElem]
    simp only [Prod.mk.injEq, not_and, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true]
    intro hlj
    rw [← getD_eq_getElem lens hj'] at hlj
    rw [codeOf_eq_cnt lens hj', hlj]
    have := cnt_lt (lens.getD · 0) (show j < m by simpa using hj)
    simp only [hlj] at this
    omega

theorem symOfLen_miss (lens : Lens) (b : Bits) (p len : Nat)
    (h : nextCode lens len + blCount lens len ≤ msbVal b p len) :
    symOfLen (code lens) b p len = none := by
  rw [symOfLen, Array.findIdx?_eq_none_iff]
  intro x hx
  obtain ⟨m, hm, rfl⟩ := Array.mem_iff_getElem.mp hx
  have hm' : m < lens.size := by simpa [code_size] using hm
  rw [code_getElem]
  simp only [Prod.mk.injEq, not_and, beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true]
  intro hl
  rw [← getD_eq_getElem lens hm'] at hl
  rw [codeOf_eq_cnt lens hm', hl]
  have := cnt_lt (lens.getD · 0) hm'
  simp only [hl] at this
  rw [blCount_eq_cnt] at h
  omega

theorem go_eq (lens : Lens) (count symbol : Nat → Nat)
    (hc : ∀ l, count l = blCount lens l)
    (hs : ∀ s, s < lens.size → 1 ≤ lens.getD s 0 →
      symbol (offs count (lens.getD s 0) + cnt (lens.getD · 0) s (lens.getD s 0)) = s)
    (bit : Nat → Bool) (b : Bits) (hbit : ∀ q, q < b.size → bit q = b.getD q false) (p : Nat) :
    ∀ k len cd first index, len + k = maxBits + 1 → 1 ≤ len →
      cd = 2 * msbVal b p (len - 1) → first = nextCode lens len → index = offs count len →
      first ≤ cd →
      go count symbol bit b.size p k len cd first index = decodeSym.go (code lens) b p len := by
  have hM : maxBits = 15 := rfl
  intro k
  induction k with
  | zero =>
    intro len cd first index hk _ _ _ _ _
    have hcond : len = 0 ∨ maxBits < len ∨ b.size < p + len := Or.inr (Or.inl (by omega))
    rw [go, decodeSym.go, if_pos hcond]
  | succ k ih =>
    intro len cd first index hk h1 hcd hfirst hindex hle
    rw [go, decodeSym.go]
    by_cases hsize : b.size < p + len
    · have hcond : len = 0 ∨ maxBits < len ∨ b.size < p + len := Or.inr (Or.inr hsize)
      rw [if_pos hsize, if_pos hcond]
    · have hcond : ¬ (len = 0 ∨ maxBits < len ∨ b.size < p + len) := by omega
      rw [if_neg hsize, if_neg hcond]
      have hmsb : cd + (if bit (p + len - 1) then 1 else 0) = msbVal b p len := by
        obtain ⟨l, rfl⟩ : ∃ l, len = l + 1 := ⟨len - 1, by omega⟩
        rw [msbVal_succ, hcd, hbit _ (by omega)]
        simp
      rw [hmsb, hc len, hfirst]
      by_cases hhit : msbVal b p len < nextCode lens len + blCount lens len
      · rw [if_pos hhit]
        obtain ⟨m, hm, hl, hcm, hsym⟩ := symOfLen_hit lens b p len (by omega) hhit
        rw [hsym]
        have := hs m hm (by omega)
        rw [hl, hcm, ← hindex] at this
        rw [this]
      · rw [if_neg hhit, symOfLen_miss lens b p len (by omega)]
        have hnext : nextCode lens (len + 1) = 2 * (nextCode lens len + blCount lens len) :=
          nextCode_succ lens h1
        have hoffs : offs count (len + 1) = offs count len + count len := by
          obtain ⟨l, rfl⟩ : ∃ l, len = l + 1 := ⟨len - 1, by omega⟩; rfl
        apply ih (len + 1) _ _ _ (by omega) (by omega) (by simp) hnext.symm
          (by rw [hoffs, hindex, hc]) (by omega)

theorem bitsOf_getD (bytes : Array UInt8) (q : Nat) (hq : q < (bitsOf bytes).size) :
    (bitsOf bytes).getD q false = byteBit (fun i => (bytes.getD i 0).toNat) q := by
  have hq' : q < bytes.size * 8 := by simpa [bitsOf] using hq
  have hb : q / 8 < bytes.size := by omega
  simp [bitsOf, Array.getD, hq', hb, byteBit]

/-- **puff's decoding is the spec's.** For tables as puff's `construct` builds
them (`count` the number of codes of each length, `symbol` the coded symbols by
length and then by symbol), `decode` reads the same symbol and stops at the same
bit as `decodeSym`, or fails exactly when it fails. -/
theorem decode_eq (lens : Lens) (count symbol : Nat → Nat)
    (hc : ∀ l, count l = blCount lens l)
    (hs : ∀ s, s < lens.size → 1 ≤ lens.getD s 0 →
      symbol (offs count (lens.getD s 0) + cnt (lens.getD · 0) s (lens.getD s 0)) = s)
    (bytes : Array UInt8) (p : Nat) :
    decode count symbol (byteBit (fun i => (bytes.getD i 0).toNat)) (bytes.size * 8) p =
      decodeSym (code lens) (bitsOf bytes) p := by
  have hsz : (bitsOf bytes).size = bytes.size * 8 := by simp [bitsOf]
  rw [decode, decodeSym, ← hsz]
  exact go_eq lens count symbol hc hs _ (bitsOf bytes)
    (fun q hq => (bitsOf_getD bytes q hq).symm) p maxBits 1 0 0 0 (by simp [maxBits]) (by omega)
    (by simp [msbVal]) (by rfl) (by rfl) (Nat.le_refl 0)

end Deflate.Puff
