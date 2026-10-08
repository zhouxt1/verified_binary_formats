import Lspec.Deflate.Spec

/-!
# 3.2.1, 3.2.2: canonical codes are prefix codes

`decodeSym` reads bits until they are some symbol's code, trying the shortest
length first. This file shows that the order does not matter. The codes that
3.2.2 assigns are prefix-free for *any* lengths. (Over-subscribed lengths give
some symbols codes too large for their length, so those symbols can never be
decoded, but no ambiguity arises.) So `decodeSym` returns exactly the one
symbol whose code begins the bits, if there is one:
`decodeSym_code_iff`.
-/

namespace Deflate

/-! ## The numbers of bit strings -/

theorem msbVal_lt (b : Bits) (p l : Nat) : msbVal b p l < 2 ^ l := by
  induction l generalizing p with
  | zero => simp [msbVal]
  | succ l ih =>
    have := ih (p + 1)
    simp only [msbVal, Nat.pow_succ]
    split <;> omega

/-- `a + k` bits are the first `a` bits followed by the next `k`. -/
theorem msbVal_add (b : Bits) (p a k : Nat) :
    msbVal b p (a + k) = msbVal b p a * 2 ^ k + msbVal b (p + a) k := by
  induction a generalizing p with
  | zero => simp [msbVal]
  | succ a ih =>
    rw [Nat.add_right_comm, msbVal, msbVal, ih (p + 1), Nat.add_right_comm p 1 a,
      Nat.add_comm a 1, ← Nat.add_assoc p 1 a]
    split <;> grind

/-- The first `a` bits of `c` bits are their number divided by `2^(c - a)`. -/
theorem msbVal_prefix (b : Bits) (p a c : Nat) (h : a ≤ c) :
    msbVal b p c / 2 ^ (c - a) = msbVal b p a := by
  obtain ⟨k, rfl⟩ : ∃ k, c = a + k := ⟨c - a, by omega⟩
  rw [msbVal_add, Nat.add_sub_cancel_left, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos k),
    Nat.div_eq_of_lt (msbVal_lt b _ k), Nat.add_zero]

/-! ## Step 2: the first codes of each length -/

theorem nextCode_succ (lens : Lens) {c : Nat} (h : 1 ≤ c) :
    nextCode lens (c + 1) = 2 * (nextCode lens c + blCount lens c) := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  rfl

/-- Every code of length `c` comes after the codes of each shorter length
`a`, extended to `c` bits. -/
theorem nextCode_ge (lens : Lens) {a c : Nat} (ha : 1 ≤ a) (hac : a < c) :
    (nextCode lens a + blCount lens a) * 2 ^ (c - a) ≤ nextCode lens c := by
  induction c with
  | zero => omega
  | succ c ih =>
    rw [nextCode_succ lens (by omega)]
    rcases Nat.lt_or_ge a c with h | h
    · have := ih h
      rw [show c + 1 - a = (c - a) + 1 by omega, Nat.pow_succ]
      grind
    · obtain rfl : a = c := by omega
      simp; omega

/-! ## Step 3: the codes -/

theorem count_take_succ (l : List Nat) {n : Nat} (h : n < l.length) :
    (l.take (n + 1)).count l[n] = (l.take n).count l[n] + 1 := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, List.count_append, List.count_singleton_self]

/-- The symbols before `n` with `n`'s length are fewer than all of them. -/
theorem count_take_lt (l : List Nat) {n : Nat} (h : n < l.length) :
    (l.take n).count l[n] + 1 ≤ l.count l[n] := by
  have hs := (List.take_sublist (n + 1) l).count_le l[n]
  rw [count_take_succ l h] at hs
  exact hs

theorem count_take_mono (l : List Nat) (x : Nat) {n m : Nat} (h : n ≤ m) :
    (l.take n).count x ≤ (l.take m).count x := by
  have : l.take n = (l.take m).take n := by rw [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact (List.take_sublist n _).count_le x

theorem codeOf_eq (lens : Lens) {n : Nat} (h : n < lens.size) :
    codeOf lens n = nextCode lens lens[n] + (lens.toList.take n).count lens[n] := by
  simp [codeOf, Array.getD, h]

/-- The heart of it. A symbol's code, cut to a shorter or equal length, is
never another symbol's code. -/
theorem code_not_prefix (lens : Lens) {n m : Nat} (hn : n < lens.size) (hm : m < lens.size)
    (hnm : n ≠ m) (ha : 1 ≤ lens[n]) (hac : lens[n] ≤ lens[m]) :
    codeOf lens m / 2 ^ (lens[m] - lens[n]) ≠ codeOf lens n := by
  rw [codeOf_eq lens hn, codeOf_eq lens hm]
  have hn' : n < lens.toList.length := by simpa using hn
  have hm' : m < lens.toList.length := by simpa using hm
  have cn := count_take_lt lens.toList hn'
  have cm := count_take_lt lens.toList hm'
  simp only [Array.getElem_toList] at cn cm
  rcases Nat.lt_or_ge lens[n] lens[m] with hlt | hge
  · -- a shorter code: the longer one starts after all codes of its length
    have hg := nextCode_ge lens ha hlt
    have hb : blCount lens lens[n] = lens.toList.count lens[n] := rfl
    intro heq
    have h1 : (nextCode lens lens[n] + (lens.toList.take n).count lens[n] + 1) *
        2 ^ (lens[m] - lens[n]) ≤ nextCode lens lens[m] + (lens.toList.take m).count lens[m] := by
      have := Nat.mul_le_mul_right (2 ^ (lens[m] - lens[n]))
        (show nextCode lens lens[n] + (lens.toList.take n).count lens[n] + 1 ≤
          nextCode lens lens[n] + blCount lens lens[n] by omega)
      omega
    have h2 := (Nat.le_div_iff_mul_le (Nat.two_pow_pos (lens[m] - lens[n]))).mpr h1
    omega
  · -- the same length: consecutive codes in symbol order
    have hl : lens[m] = lens[n] := by omega
    rw [hl, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    intro heq
    have heq' : (lens.toList.take m).count lens[n] = (lens.toList.take n).count lens[n] := by
      omega
    rcases Nat.lt_or_gt_of_ne hnm with h | h
    · have h1 := count_take_mono lens.toList lens[n] (show n + 1 ≤ m by omega)
      have h2 := count_take_succ lens.toList hn'
      simp only [Array.getElem_toList] at h2
      omega
    · have h1 := count_take_mono lens.toList lens[n] (show m + 1 ≤ n by omega)
      have h2 := count_take_succ lens.toList hm'
      simp only [Array.getElem_toList, hl] at h2
      omega

/-- Symbol `n`'s code begins the bits at `p`. -/
def Matches (lens : Lens) (b : Bits) (p n : Nat) : Prop :=
  ∃ h : n < lens.size, 1 ≤ lens[n] ∧ codeOf lens n = msbVal b p lens[n]

/-- At most one symbol's code begins any bits: the code is a prefix code. -/
theorem matches_unique {lens : Lens} {b : Bits} {p n m : Nat}
    (hn : Matches lens b p n) (hm : Matches lens b p m) : n = m := by
  obtain ⟨hn, ha, cn⟩ := hn
  obtain ⟨hm, hc, cm⟩ := hm
  apply Classical.byContradiction
  intro hnm
  rcases Nat.le_total lens[n] lens[m] with h | h
  · apply code_not_prefix lens hn hm hnm ha h
    rw [cm, cn, msbVal_prefix b p _ _ h]
  · apply code_not_prefix lens hm hn (Ne.symm hnm) hc h
    rw [cm, cn, msbVal_prefix b p _ _ h]

/-! ## `decodeSym` decodes the symbol whose code begins the bits -/

theorem code_size (lens : Lens) : (code lens).size = lens.size := by simp [code]

theorem code_getElem (lens : Lens) {n : Nat} (h : n < (code lens).size) :
    (code lens)[n] = (lens[n]'(by simpa [code_size] using h), codeOf lens n) := by
  simp [code]

theorem symOfLen_some {lens : Lens} {b : Bits} {p l n : Nat}
    (h : symOfLen (code lens) b p l = some n) :
    ∃ hn : n < lens.size, lens[n] = l ∧ codeOf lens n = msbVal b p l := by
  obtain ⟨hn, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  rw [code_getElem] at hp
  simp at hp
  exact ⟨by simpa [code_size] using hn, hp⟩

theorem decodeSym_go_some (lens : Lens) (b : Bits) (p l : Nat) :
    ∀ s q, decodeSym.go (code lens) b p l = some (s, q) →
      ∃ hs : s < lens.size, lens[s] ≤ maxBits ∧ q = p + lens[s] ∧ q ≤ b.size ∧
        1 ≤ lens[s] ∧ codeOf lens s = msbVal b p lens[s] := by
  induction l using decodeSym.go.induct (code lens) b p with
  | case1 l h =>
    intro s q hs; rw [decodeSym.go] at hs; simp [h] at hs
  | case2 l h n hn =>
    intro s q hs; rw [decodeSym.go] at hs; simp [h, hn] at hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨hs, hl, hc⟩ := symOfLen_some hn
    subst hl
    exact ⟨hs, by omega, rfl, by omega, by omega, hc⟩
  | case3 l h hn ih =>
    intro s q hs; rw [decodeSym.go] at hs; simp [h, hn] at hs
    exact ih s q hs

theorem decodeSym_go_of_matches (lens : Lens) (b : Bits) (p s : Nat)
    (hs : s < lens.size) (h1 : 1 ≤ lens[s]) (h15 : lens[s] ≤ maxBits)
    (hb : p + lens[s] ≤ b.size) (hc : codeOf lens s = msbVal b p lens[s]) (l : Nat) :
    1 ≤ l → l ≤ lens[s] → decodeSym.go (code lens) b p l = some (s, p + lens[s]) := by
  have hm : Matches lens b p s := ⟨hs, h1, hc⟩
  induction l using decodeSym.go.induct (code lens) b p with
  | case1 l h =>
    intro hl1 hl2; exfalso; omega
  | case2 l h n hn =>
    intro hl1 hl2
    rw [decodeSym.go]; simp [h, hn]
    obtain ⟨hn', hl, hcn⟩ := symOfLen_some hn
    have : Matches lens b p n := ⟨hn', by omega, by rw [hl]; exact hcn⟩
    obtain rfl := matches_unique this hm
    exact ⟨rfl, by rw [hl]⟩
  | case3 l h hn ih =>
    intro hl1 hl2
    rw [decodeSym.go]; simp [h, hn]
    rcases Nat.lt_or_ge l lens[s] with hlt | hge
    · exact ih (by omega) (by omega)
    · exfalso
      have hl : l = lens[s] := by omega
      have := Array.findIdx?_eq_none_iff.mp hn ((code lens)[s]'(by simpa [code_size] using hs))
        (Array.getElem_mem _)
      rw [code_getElem] at this
      simp [hl, hc] at this

/-- **Decoding a symbol** (3.2.1). `decodeSym` on the code of `lens` gives `s`
and the position after it exactly when `s` has a code of 1 to 15 bits that
begins the bits at `p`. By `matches_unique` there is at most one such
symbol, for any lengths. -/
theorem decodeSym_code_iff (lens : Lens) (b : Bits) (p s q : Nat) :
    decodeSym (code lens) b p = some (s, q) ↔
      ∃ hs : s < lens.size, 1 ≤ lens[s] ∧ lens[s] ≤ maxBits ∧ q = p + lens[s] ∧
        q ≤ b.size ∧ codeOf lens s = msbVal b p lens[s] := by
  constructor
  · intro h
    obtain ⟨hs, h15, hq, hb, h1, hc⟩ := decodeSym_go_some lens b p 1 s q h
    exact ⟨hs, h1, h15, hq, hb, hc⟩
  · rintro ⟨hs, h1, h15, rfl, hb, hc⟩
    exact decodeSym_go_of_matches lens b p s hs h1 h15 hb hc 1 (by omega) h1

end Deflate
