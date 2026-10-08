import Lspec.Bridge.VDeflate
import Lspec.Deflate.Spec
import Lspec.Deflate.Prefix
import Lspec.Deflate.Guards

/-!
# vdeflate's Verus spec is the Lean spec

`V.vdeflate.spec.inflate` is `vdeflate/src/spec.rs` as translated from
Verus's VIR (`VDeflate.lean`). `verus_inflate_eq` shows that for every choice
of the values Verus leaves unspecified, it gives what `Deflate.inflate` gives:
the same verdict, data, bit count and zlib flag.

The proof goes function by function, bottom up. Each Verus function is shown
to compute its Lean counterpart on the Lean values' images: bits as
`List Bool`, positions and lengths as `Int`, code lengths and bytes as lists
of `Int`.
-/

namespace VModel.Seq

variable {α : Type}

@[simp] theorem len_list (s : List α) : len s = s.length := len_eq s

theorem index_eq (u : Unspec) {τ : VTy} {α : Type} {hτ : τ.denote = α} (s : List α) (i : Nat)
    (h : i < s.length) : index u τ hτ s i = s[i] := by
  unfold index
  induction s generalizing i with
  | nil => simp at h
  | cons x t ih =>
    cases i with
    | zero => simp [indexWith]
    | succ i =>
      simp only [indexWith]
      rw [if_neg (by omega)]
      have := ih i (by simp at h; omega)
      simpa using this

theorem subrange_eq (s : List α) (i j : Nat) (h : i ≤ j) (hj : j ≤ s.length) :
    subrange s i j = (s.drop i).take (j - i) := by
  induction s generalizing i j with
  | nil => simp [subrange]
  | cons x t ih =>
    simp only [subrange]
    cases i with
    | succ i =>
      rw [if_pos (by omega), show ((i + 1 : Nat) : Int) - 1 = ((i : Nat) : Int) by omega,
        show (j : Int) - 1 = ((j - 1 : Nat) : Int) by omega,
        ih i (j - 1) (by omega) (by simp at hj; omega)]
      simp only [List.drop_succ_cons]; congr 1; omega
    | zero =>
      rw [if_neg (by omega)]
      cases j with
      | zero => simp
      | succ j =>
        rw [if_neg (by omega), show ((j + 1 : Nat) : Int) - 1 = ((j : Nat) : Int) by omega,
          ih 0 j (by omega) (by simp at hj; omega)]
        simp

theorem new_eq (u : Unspec) {τ : VTy} {α : Type} {hτ : τ.denote = α} (n : Nat) (f : Int → α) :
    new u τ hτ n f = (List.range n).map fun (k : Nat) => f (k : Int) := by
  simp only [new, newWith, show ¬((n : Int) < 0) by omega, ite_false, Int.toNat_natCast]
  induction n with
  | zero => rfl
  | succ n ih => simp [newWith.go, ih, push_eq, List.range_succ]

theorem last_eq (u : Unspec) {τ : VTy} {α : Type} {hτ : τ.denote = α} (s : List α) (x : α) :
    last u τ hτ (s ++ [x]) = x := by
  unfold last
  rw [show len (s ++ [x]) - 1 = ((s.length : Nat) : Int) by simp]
  rw [index_eq u _ _ (by simp)]; simp

theorem dropLast_eq (s : List α) (x : α) : dropLast (s ++ [x]) = s := by
  unfold dropLast
  rw [show len (s ++ [x]) - 1 = ((s.length : Nat) : Int) by simp]
  rw [show (0 : Int) = ((0 : Nat) : Int) by rfl, subrange_eq _ 0 s.length (by omega) (by simp)]
  simp

theorem update_eq (u : Unspec) {τ : VTy} {α : Type} {hτ : τ.denote = α} (s : List α) (i : Nat) (a : α)
    (h : i < s.length) : update u τ hτ s i a = s.set i a := by
  unfold update updateWith
  rw [if_neg (by simp <;> omega)]
  induction s generalizing i with
  | nil => simp at h
  | cons x t ih =>
    cases i with
    | zero => simp [updateWith.go]
    | succ i =>
      simp only [updateWith.go]
      rw [if_neg (by omega), show ((i + 1 : Nat) : Int) - 1 = ((i : Nat) : Int) by omega,
        ih i (by simp at h; omega)]
      rfl

end VModel.Seq

namespace VModel

theorem ediv_ne (u : Unspec) (x y : Int) (h : y ≠ 0) : ediv u x y = x / y := by simp [ediv, h]
theorem emod_ne (u : Unspec) (x y : Int) (h : y ≠ 0) : emod u x y = x % y := by simp [emod, h]

theorem clip_u8 (u : Unspec) (x : Int) (h0 : 0 ≤ x) (h1 : x < 256) : clip u (.u 8) x = x :=
  clip_of_contains u _ x (by simp [IntRange.contains]; omega)

/-- `0 ≤ x` for sums and products of naturals, powers and lengths. -/
syntax "nonneg" : tactic
macro_rules
  | `(tactic| nonneg) => `(tactic| first
      | omega
      | exact Int.natCast_nonneg _
      | exact Seq.len_nonneg _
      | (apply Int.pow_nonneg; omega)
      | (apply Int.add_nonneg <;> nonneg)
      | (apply Int.mul_nonneg <;> nonneg))

/-- Drop the `nat` clips Verus puts on `nat` arithmetic, where the value is nonnegative. -/
macro "unclip" : tactic => `(tactic| (try simp (disch := nonneg) only [VModel.clip_nat]))

theorem someVal_some (u : Unspec) {τ : VTy} {α : Type} {hτ : τ.denote = α} (x : α) :
    someVal u τ hτ (some x) = x := rfl

end VModel

open VModel

namespace Bridge

/-! ## Bits -/

/-- A list of bits as a number, the first the least significant. -/
def lsbList : List Bool → Nat
  | [] => 0
  | x :: t => (if x then 1 else 0) + 2 * lsbList t

/-- A list of bits as a number, the first the most significant. -/
def msbList (s : List Bool) : Nat := s.foldl (fun v x => 2 * v + (if x then 1 else 0)) 0

theorem lval_eq (u : Unspec) (s : List Bool) : V.vbits.lsb.lval u s = lsbList s := by
  induction s with
  | nil => rw [V.vbits.lsb.lval]; simp [lsbList]
  | cons x t ih =>
    rw [V.vbits.lsb.lval]
    have hsub : Seq.subrange (x :: t) 1 (Seq.len (x :: t)) = t := by
      rw [Seq.len_list, show ((x :: t).length : Int) = (((x :: t).length : Nat) : Int) by rfl,
        show (1 : Int) = ((1 : Nat) : Int) by rfl,
        Seq.subrange_eq _ 1 _ (by simp) (by simp)]
      simp
    rw [hsub, ih, show (0 : Int) = ((0 : Nat) : Int) by rfl, Seq.index_eq u _ 0 (by simp)]
    cases x <;> simp [lsbList] <;> unclip <;> omega

theorem lsbList_take (b : Deflate.Bits) (p n : Nat) (h : p + n ≤ b.size) :
    lsbList ((b.toList.drop p).take n) = Deflate.lsbVal b p n := by
  induction n generalizing p with
  | zero => simp [lsbList, Deflate.lsbVal]
  | succ n ih =>
    have hp : p < b.toList.length := by simp; omega
    rw [List.drop_eq_getElem_cons hp, List.take_succ_cons, lsbList, Deflate.lsbVal,
      ← ih (p + 1) (by omega)]
    simp [Array.getD, show p < b.size by omega]

theorem lsbList_lt (s : List Bool) : lsbList s < 2 ^ s.length := by
  induction s with
  | nil => simp [lsbList]
  | cons x t ih => simp only [lsbList, List.length_cons, Nat.pow_succ]; split <;> omega

theorem getbits_eq (u : Unspec) (b : Deflate.Bits) (p n : Nat) :
    V.vdeflate.spec.getbits u b.toList p n =
      Option.map (fun v : Nat => (v : Int)) (Deflate.getbits b p n) := by
  unfold V.vdeflate.spec.getbits Deflate.getbits
  simp only [IntRange.contains, show (0 : Int) ≤ n by omega, decide_true, dite_true, Seq.len_list,
    Array.length_toList, ← Int.natCast_add]
  by_cases h : p + n ≤ b.size
  · rw [dif_pos (by simp <;> omega), if_pos h,
      Seq.subrange_eq _ p (p + n) (by omega) (by simp <;> omega), lval_eq]
    simp [lsbList_take b p n h]
  · rw [dif_neg (by simp <;> omega), if_neg h]; rfl

theorem msbList_append (s : List Bool) (x : Bool) :
    msbList (s ++ [x]) = 2 * msbList s + (if x then 1 else 0) := by
  simp [msbList, List.foldl_append]

theorem bits_val_eq (u : Unspec) (s : List Bool) : V.vbits.bitspec.bits_val u s = msbList s := by
  induction h : s.length generalizing s with
  | zero =>
    rw [V.vbits.bitspec.bits_val]; simp at h; subst h; simp [msbList]
  | succ n ih =>
    rcases List.eq_nil_or_concat s with rfl | ⟨t, x, rfl⟩
    · simp at h
    · rw [List.concat_eq_append] at h ⊢
      rw [V.vbits.bitspec.bits_val]
      simp only [Seq.len_list, List.length_append, List.length_singleton]
      rw [dif_neg (by simp <;> omega), Seq.dropLast_eq, Seq.last_eq, ih t (by simp at h; omega), msbList_append]
      split <;> simp_all <;> unclip

theorem msbList_foldl (a : Nat) (t : List Bool) :
    t.foldl (fun v x => 2 * v + (if x then 1 else 0)) a = a * 2 ^ t.length + msbList t := by
  induction t generalizing a with
  | nil => simp [msbList]
  | cons y t ih =>
    simp only [List.foldl_cons, msbList] at ih ⊢
    rw [ih, ih (2 * 0 + if y = true then 1 else 0)]
    simp [Nat.pow_succ]; grind

theorem msbList_cons (x : Bool) (t : List Bool) :
    msbList (x :: t) = (if x then 2 ^ t.length else 0) + msbList t := by
  rw [msbList, List.foldl_cons, msbList_foldl]
  split <;> simp

theorem msbList_take (b : Deflate.Bits) (p n : Nat) (h : p + n ≤ b.size) :
    msbList ((b.toList.drop p).take n) = Deflate.msbVal b p n := by
  induction n generalizing p with
  | zero => simp [msbList, Deflate.msbVal]
  | succ n ih =>
    have hp : p < b.toList.length := by simp; omega
    rw [List.drop_eq_getElem_cons hp, List.take_succ_cons, msbList_cons, Deflate.msbVal,
      ← ih (p + 1) (by omega)]
    have hl : ((b.toList.drop (p + 1)).take n).length = n := by simp; omega
    simp [Array.getD, show p < b.size by omega, hl]

theorem codebits_eq (u : Unspec) (b : Deflate.Bits) (p l : Nat) (h : p + l ≤ b.size) :
    V.vdeflate.spec.codebits u b.toList p l = Deflate.msbVal b p l := by
  unfold V.vdeflate.spec.codebits
  simp only [IntRange.contains, show (0 : Int) ≤ l by omega, decide_true, dite_true]
  rw [show (p : Int) + l = ((p + l : Nat) : Int) by omega,
    Seq.subrange_eq _ p (p + l) (by omega) (by simp <;> omega), bits_val_eq,
    show p + l - p = l by omega, msbList_take b p l h]

/-! ## 3.2.2: canonical codes -/

/-- Code lengths as the Verus spec has them. -/
abbrev lensV (L : Deflate.Lens) : List Int := L.toList.map (fun x : Nat => (x : Int))

@[simp] theorem lensV_length (L : Deflate.Lens) : (lensV L).length = L.size := by simp

theorem index_lensV {r : IntRange} (u : Unspec) (L : Deflate.Lens) (n : Nat) (h : n < L.size) :
    Seq.index u (.int r) (α := Int) rfl (lensV L) n = (L[n] : Int) := by
  rw [Seq.index_eq u _ n (by simp <;> omega)]; simp

theorem count_len_eq (u : Unspec) (L : Deflate.Lens) (l upto : Nat) (h : upto ≤ L.size) :
    V.vdeflate.spec.count_len u (lensV L) l upto = ((L.toList.take upto).count l : Nat) := by
  induction upto with
  | zero => rw [V.vdeflate.spec.count_len]; simp [IntRange.contains]
  | succ k ih =>
    rw [V.vdeflate.spec.count_len]
    simp only [IntRange.contains, show (0 : Int) ≤ l by omega, decide_true, dite_true]
    rw [dif_neg (by simp <;> omega), show ((k + 1 : Nat) : Int) - 1 = ((k : Nat) : Int) by omega,
      ih (by omega), index_lensV u L k (by omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp <;> omega)]
    simp only [Option.toList_some, List.count_append, List.count_singleton, Array.getElem_toList]
    by_cases hk : L[k] = l
    · simp [hk]; unclip
    · have : (L[k] : Int) ≠ l := by omega
      clear ih
      simp [hk, this]; unclip

theorem bl_count_eq (u : Unspec) (L : Deflate.Lens) (l : Nat) :
    V.vdeflate.spec.bl_count u (lensV L) l = (Deflate.blCount L l : Nat) := by
  unfold V.vdeflate.spec.bl_count Deflate.blCount
  simp only [IntRange.contains, show (0 : Int) ≤ l by omega, decide_true, dite_true, Seq.len_list,
    lensV_length]
  rw [count_len_eq u L l L.size (by omega), List.take_of_length_le (by simp)]

theorem p2_eq (u : Unspec) (n : Nat) : V.vbits.bitspec.p2 u n = (2 ^ n : Nat) := by
  induction n with
  | zero => rw [V.vbits.bitspec.p2]; simp [IntRange.contains]
  | succ n ih =>
    rw [V.vbits.bitspec.p2]
    simp only [IntRange.contains, show (0 : Int) ≤ ((n + 1 : Nat) : Int) by omega, decide_true,
      dite_true]
    rw [dif_neg (by simp <;> omega), show ((n + 1 : Nat) : Int) - 1 = ((n : Nat) : Int) by omega,
      clip_nat u ((n : Nat) : Int) (by omega), ih]
    unclip; simp [Nat.pow_succ]; try omega

theorem next_code_eq (u : Unspec) (L : Deflate.Lens) (l : Nat) :
    V.vdeflate.spec.next_code u (lensV L) l = (Deflate.nextCode L l : Nat) := by
  induction l with
  | zero => rw [V.vdeflate.spec.next_code]; simp [IntRange.contains, Deflate.nextCode]
  | succ l ih =>
    rw [V.vdeflate.spec.next_code]
    simp only [IntRange.contains, show (0 : Int) ≤ ((l + 1 : Nat) : Int) by omega, decide_true,
      dite_true]
    cases l with
    | zero => simp [Deflate.nextCode]
    | succ k =>
      rw [dif_neg (by simp <;> omega), show ((k + 1 + 1 : Nat) : Int) - 1 = ((k + 1 : Nat) : Int) by omega,
        clip_nat u ((k + 1 : Nat) : Int) (by omega), ih, bl_count_eq]
      unclip; simp [Deflate.nextCode]

theorem code_of_eq (u : Unspec) (L : Deflate.Lens) (n : Nat) (h : n < L.size) :
    V.vdeflate.spec.code_of u (lensV L) n = (Deflate.codeOf L n : Nat) := by
  unfold V.vdeflate.spec.code_of Deflate.codeOf
  rw [index_lensV u L n h, next_code_eq, count_len_eq u L _ n (by omega)]
  unclip; simp [Array.getD, h]

/-- `find_n` from `n` finds what `findIdx?` finds in the code's entries from `n`. -/
theorem find_n_eq (u : Unspec) (L : Deflate.Lens) (b : Deflate.Bits) (p l : Nat)
    (hb : p + l ≤ b.size) (n : Nat) (hn : n ≤ L.size) :
    V.vdeflate.spec.find_n u (lensV L) b.toList p l n =
      Option.map (fun k : Nat => ((k + n : Nat) : Int))
        (((Deflate.code L).toList.drop n).findIdx? (· == (l, Deflate.msbVal b p l))) := by
  induction h : L.size - n generalizing n with
  | zero =>
    rw [V.vdeflate.spec.find_n]
    simp only [IntRange.contains, show (0 : Int) ≤ l by omega, decide_true, dite_true]
    rw [dif_pos (by simp <;> omega)]
    rw [List.drop_eq_nil_of_le (by simp [Deflate.code_size]; omega)]; rfl
  | succ k ih =>
    rw [V.vdeflate.spec.find_n]
    simp only [IntRange.contains, show (0 : Int) ≤ l by omega, decide_true, dite_true]
    rw [dif_neg (by simp <;> omega)]
    have hn' : n < (Deflate.code L).toList.length := by simp [Deflate.code_size]; omega
    rw [List.drop_eq_getElem_cons hn', List.findIdx?_cons, index_lensV u L n (by omega),
      code_of_eq u L n (by omega), codebits_eq u b p l hb]
    have he : (Deflate.code L).toList[n] = (L[n], Deflate.codeOf L n) := by
      simp [Deflate.code]
    rw [he]
    by_cases hp : L[n] = l ∧ Deflate.codeOf L n = Deflate.msbVal b p l
    · rw [dif_pos (by simp [hp.1, hp.2]), if_pos (by simp [hp.1, hp.2]), clip_nat u _ (by omega)]
      simp
    · rw [dif_neg (by simp <;> omega), if_neg (by simp <;> omega),
        show (n : Int) + 1 = ((n + 1 : Nat) : Int) by omega, ih (n + 1) (by omega) (by omega)]
      cases (List.findIdx? (fun x => x == (l, Deflate.msbVal b p l))
        (List.drop (n + 1) (Deflate.code L).toList)) <;> simp; omega

theorem find_n_zero (u : Unspec) (L : Deflate.Lens) (b : Deflate.Bits) (p l : Nat)
    (hb : p + l ≤ b.size) :
    V.vdeflate.spec.find_n u (lensV L) b.toList p l 0 =
      Option.map (fun k : Nat => (k : Int))
        ((Deflate.code L).toList.findIdx? (· == (l, Deflate.msbVal b p l))) := by
  have := find_n_eq u L b p l hb 0 (by omega)
  simpa using this

theorem symOfLen_eq (L : Deflate.Lens) (b : Deflate.Bits) (p l : Nat) :
    Deflate.symOfLen (Deflate.code L) b p l =
      ((Deflate.code L).toList.findIdx? (· == (l, Deflate.msbVal b p l))) := by
  unfold Deflate.symOfLen
  rw [← List.findIdx?_toArray, Array.toArray_toList]

theorem find_sym_eq (u : Unspec) (L : Deflate.Lens) (b : Deflate.Bits) (p l : Nat) (hl : 1 ≤ l) :
    V.vdeflate.spec.find_sym u (lensV L) b.toList p l =
      Option.map (fun x : Nat × Nat => ((x.1 : Int), (x.2 : Int)))
        (Deflate.decodeSym.go (Deflate.code L) b p l) := by
  induction l using Deflate.decodeSym.go.induct (Deflate.code L) b p with
  | case1 l h =>
    rw [V.vdeflate.spec.find_sym, Deflate.decodeSym.go]
    simp only [IntRange.contains, show (0 : Int) ≤ l by omega, decide_true, dite_true]
    rw [dif_pos (by simp [V.vdeflate.spec.maxbits, Deflate.maxBits] at h ⊢; omega), if_pos h]; rfl
  | case2 l h n hn =>
    rw [V.vdeflate.spec.find_sym, Deflate.decodeSym.go]
    simp only [IntRange.contains, show (0 : Int) ≤ l by omega, decide_true, dite_true]
    rw [dif_neg (by simp [V.vdeflate.spec.maxbits, Deflate.maxBits] at h ⊢; omega), if_neg h, hn]
    rw [find_n_zero u L b p l (by simp [Deflate.maxBits] at h; omega)]
    rw [symOfLen_eq] at hn
    simp [hn, someVal]
  | case3 l h hn ih =>
    rw [V.vdeflate.spec.find_sym, Deflate.decodeSym.go]
    simp only [IntRange.contains, show (0 : Int) ≤ l by omega, decide_true, dite_true]
    rw [dif_neg (by simp [V.vdeflate.spec.maxbits, Deflate.maxBits] at h ⊢; omega), if_neg h, hn]
    rw [find_n_zero u L b p l (by simp [Deflate.maxBits] at h; omega)]
    rw [symOfLen_eq] at hn
    simp only [hn, Option.map_none, Option.isSome_none, Bool.false_and, Bool.false_eq_true, dite_false]
    rw [show (l : Int) + 1 = ((l + 1 : Nat) : Int) by omega, clip_nat u ((l + 1 : Nat) : Int) (by omega), ih (by omega)]

theorem decode_sym_eq (u : Unspec) (L : Deflate.Lens) (b : Deflate.Bits) (p : Nat) :
    V.vdeflate.spec.decode_sym u (lensV L) b.toList p =
      Option.map (fun x : Nat × Nat => ((x.1 : Int), (x.2 : Int)))
        (Deflate.decodeSym (Deflate.code L) b p) := by
  unfold V.vdeflate.spec.decode_sym Deflate.decodeSym
  exact find_sym_eq u L b p 1 (by omega)

/-! ## Code validity -/

/-- One symbol's term of the Kraft sum. -/
def kterm (len : Nat) : Nat := if 1 ≤ len ∧ len ≤ Deflate.maxBits then 2 ^ (Deflate.maxBits - len) else 0

theorem kraft_eq (u : Unspec) (L : Deflate.Lens) (upto : Nat) (h : upto ≤ L.size) :
    V.vdeflate.spec.kraft u (lensV L) upto = (((L.toList.take upto).map kterm).sum : Nat) := by
  induction upto with
  | zero => rw [V.vdeflate.spec.kraft]; simp
  | succ k ih =>
    rw [V.vdeflate.spec.kraft]
    rw [dif_neg (by simp <;> omega), show ((k + 1 : Nat) : Int) - 1 = ((k : Nat) : Int) by omega,
      ih (by omega), index_lensV u L k (by omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp <;> omega)]
    simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Array.getElem_toList]
    unfold kterm Deflate.maxBits
    by_cases hk : 1 ≤ L[k] ∧ L[k] ≤ 15
    · rw [dif_pos (by simp; omega), if_pos hk,
        show (15 : Int) - (L[k] : Int) = ((15 - L[k] : Nat) : Int) by omega, clip_nat u ((15 - L[k] : Nat) : Int) (by omega),
        p2_eq]
      unclip; simp
    · rw [dif_neg (by simp; omega), if_neg hk]; simp; unclip

theorem kraft_full (u : Unspec) (L : Deflate.Lens) :
    V.vdeflate.spec.kraft u (lensV L) (Seq.len (lensV L)) = (Deflate.kraft L : Nat) := by
  rw [Seq.len_list, lensV_length, kraft_eq u L L.size (by omega), List.take_of_length_le (by simp)]
  rfl

theorem not_oversub_eq (u : Unspec) (L : Deflate.Lens) :
    V.vdeflate.spec.not_oversub u (lensV L) = Deflate.notOversub L := by
  unfold V.vdeflate.spec.not_oversub Deflate.notOversub
  rw [kraft_full, show (15 : Int) = ((15 : Nat) : Int) by rfl, p2_eq]
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, Deflate.maxBits, Nat.reducePow]
  constructor
  · intro h; exact decide_eq_true (by have := Int.ofNat_le.mp h; simpa using this)
  · intro h; exact Int.ofNat_le.mpr (by have := of_decide_eq_true h; simpa using this)

theorem complete_eq (u : Unspec) (L : Deflate.Lens) :
    V.vdeflate.spec.complete u (lensV L) = Deflate.complete L := by
  unfold V.vdeflate.spec.complete Deflate.complete
  rw [kraft_full, show (15 : Int) = ((15 : Nat) : Int) by rfl, p2_eq]
  rw [Bool.eq_iff_iff]; simp [Deflate.maxBits]; omega

theorem nonempty_eq (u : Unspec) (L : Deflate.Lens) :
    V.vdeflate.spec.nonempty u (lensV L) = !(L.all (· == 0)) := by
  unfold V.vdeflate.spec.nonempty
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.not_eq_true', Seq.len_list, lensV_length]
  constructor
  · rintro ⟨i, hi⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hi
    obtain ⟨⟨h0, h1⟩, hne⟩ := hi
    obtain ⟨k, rfl⟩ : ∃ k : Nat, i = k := ⟨i.toNat, by omega⟩
    rw [index_lensV u L k (by omega)] at hne
    rw [Bool.eq_false_iff]
    intro hall
    rw [Array.all_eq_true] at hall
    have := hall k (by omega)
    simp at this hne; omega
  · intro hall
    have : ∃ k, ∃ hk : k < L.size, L[k] ≠ 0 := by
      apply Classical.byContradiction
      intro hc
      rw [Bool.eq_false_iff] at hall
      apply hall
      rw [Array.all_eq_true]
      intro k hk
      simp only [beq_iff_eq]
      apply Classical.byContradiction
      intro hne
      exact hc ⟨k, hk, hne⟩
    obtain ⟨k, hk, hne⟩ := this
    refine ⟨k, ?_⟩
    rw [index_lensV u L k hk]
    simp; omega

theorem zlib_ok_eq (u : Unspec) (L : Deflate.Lens) (c : Bool) :
    V.vdeflate.spec.zlib_ok u (lensV L) c = Deflate.zlibOk L c := by
  unfold V.vdeflate.spec.zlib_ok Deflate.zlibOk
  rw [nonempty_eq, complete_eq, show (1 : Int) = ((1 : Nat) : Int) by rfl, bl_count_eq, kraft_full,
    show (14 : Int) = ((14 : Nat) : Int) by rfl, p2_eq]
  have e1 : decide ((Deflate.blCount L 1 : Int) = ((1 : Nat) : Int)) = (Deflate.blCount L 1 == 1) := by
    rw [Bool.eq_iff_iff]; simp; omega
  have e2 : decide ((Deflate.kraft L : Int) = ((2 ^ 14 : Nat) : Int)) =
      (Deflate.kraft L == 2 ^ (Deflate.maxBits - 1)) := by
    rw [Bool.eq_iff_iff]; simp [Deflate.maxBits]; omega
  rw [e1, e2]; simp

/-! ## 3.2.5, 3.2.6: the tables and the fixed codes -/

/-- The Verus spec's length and distance formulas, without `Unspec`. -/
def lenBaseF (s : Nat) : Nat :=
  if s ≤ 264 then s - 254 else if s ≤ 268 then 11 + 2 * (s - 265)
  else if s ≤ 272 then 19 + 4 * (s - 269) else if s ≤ 276 then 35 + 8 * (s - 273)
  else if s ≤ 280 then 67 + 16 * (s - 277) else if s ≤ 284 then 131 + 32 * (s - 281) else 258
def lenExtraF (s : Nat) : Nat := if s ≤ 264 ∨ s = 285 then 0 else (s - 261) / 4
def distBaseF (d : Nat) : Nat := if d < 4 then d + 1 else 2 ^ (d / 2 - 1) * (2 + d % 2) + 1
def distExtraF (d : Nat) : Nat := if d < 4 then 0 else d / 2 - 1

theorem len_base_eq (u : Unspec) (s : Nat) (h : 257 ≤ s) :
    V.vdeflate.spec.len_base u s = (lenBaseF s : Int) := by
  unfold V.vdeflate.spec.len_base lenBaseF
  rw [dif_pos (by simp [IntRange.contains])]
  simp only [clip, IntRange.contains, apply_ite (fun x : Nat => (x : Int))]
  repeat' split
  all_goals simp_all <;> omega

theorem len_extra_eq (u : Unspec) (s : Nat) :
    V.vdeflate.spec.len_extra u s = (lenExtraF s : Int) := by
  unfold V.vdeflate.spec.len_extra lenExtraF
  rw [dif_pos (by simp [IntRange.contains])]
  simp only [clip, ediv, IntRange.contains, apply_ite (fun x : Nat => (x : Int))]
  repeat' split
  all_goals simp_all <;> omega

theorem dist_extra_eq (u : Unspec) (d : Nat) :
    V.vdeflate.spec.dist_extra u d = (distExtraF d : Int) := by
  unfold V.vdeflate.spec.dist_extra distExtraF
  rw [dif_pos (by simp [IntRange.contains])]
  simp only [clip, ediv, IntRange.contains, apply_ite (fun x : Nat => (x : Int))]
  repeat' split
  all_goals simp_all <;> omega

theorem dist_base_eq (u : Unspec) (d : Nat) :
    V.vdeflate.spec.dist_base u d = (distBaseF d : Int) := by
  unfold V.vdeflate.spec.dist_base distBaseF
  simp only [IntRange.contains, show (0 : Int) ≤ d by omega, decide_true, dite_true]
  by_cases h : d < 4
  · rw [dif_pos (by simp; omega), if_pos h]; simp; unclip
  · rw [dif_neg (by simp; omega), if_neg h, ediv_ne u _ _ (by omega), emod_ne u _ _ (by omega),
      show (d : Int) / 2 - 1 = ((d / 2 - 1 : Nat) : Int) by omega, clip_nat u ((d / 2 - 1 : Nat) : Int) (by omega), p2_eq,
      show (d : Int) % 2 = ((d % 2 : Nat) : Int) by omega]
    unclip; simp

theorem lenTable_eq : ∀ k : Fin 29,
    Deflate.lenTable[k.val]? = some (lenBaseF (k.val + 257), lenExtraF (k.val + 257)) := by
  decide

theorem distTable_eq : ∀ k : Fin 30,
    Deflate.distTable[k.val]? = some (distBaseF k.val, distExtraF k.val) := by
  decide

theorem lenTable_none (k : Nat) (h : 29 ≤ k) : Deflate.lenTable[k]? = none := by
  simp [Deflate.lenTable]; omega

theorem distTable_none (k : Nat) (h : 30 ≤ k) : Deflate.distTable[k]? = none := by
  simp [Deflate.distTable]; omega

theorem fixedLit_size : Deflate.fixedLit.size = 288 := by
  unfold Deflate.fixedLit; exact Array.size_ofFn

theorem fixedLit_get (i : Nat) (h : i < Deflate.fixedLit.size) :
    Deflate.fixedLit[i] = if i < 144 then 8 else if i < 256 then 9 else if i < 280 then 7 else 8 := by
  simp only [Deflate.fixedLit, Array.getElem_ofFn]

theorem fixed_lit_eq (u : Unspec) : V.vdeflate.spec.fixed_lit u 0 = lensV Deflate.fixedLit := by
  unfold V.vdeflate.spec.fixed_lit
  rw [show (288 : Int) = ((288 : Nat) : Int) by rfl, Seq.new_eq]
  apply List.ext_getElem (by simp only [List.length_map, List.length_range, lensV_length, fixedLit_size, Array.length_toList])
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, fixedLit_get]
  repeat' split
  all_goals simp_all <;> omega

theorem fixed_dist_eq (u : Unspec) : V.vdeflate.spec.fixed_dist u 0 = lensV Deflate.fixedDist := by
  unfold V.vdeflate.spec.fixed_dist Deflate.fixedDist
  rw [show (32 : Int) = ((32 : Nat) : Int) by rfl, Seq.new_eq]
  apply List.ext_getElem (by simp only [List.length_map, List.length_range, lensV_length,
    Array.size_replicate, Array.length_toList])
  intro i h1 h2
  simp only [List.getElem_map, Array.getElem_toList, Array.getElem_replicate]
  rfl

/-! ## 3.2.3: LZ77 copies -/

/-- Output bytes as the Verus spec has them. -/
abbrev outV (o : Array UInt8) : List Int := o.toList.map (fun x => (x.toNat : Int))

theorem outV_push (o : Array UInt8) (x : UInt8) :
    Seq.push (outV o) (x.toNat : Int) = outV (o.push x) := by
  simp only [outV, Seq.push_eq, Array.toList_push, List.map_append, List.map_cons, List.map_nil]

theorem lz_copy_eq (u : Unspec) (o : Array UInt8) (d len : Nat) (hd : 1 ≤ d) (hdo : d ≤ o.size) :
    V.vdeflate.spec.lz_copy u (outV o) d len = outV (Deflate.lzCopy o d len) := by
  induction len generalizing o with
  | zero => rw [V.vdeflate.spec.lz_copy]; simp [IntRange.contains, Deflate.lzCopy]
  | succ n ih =>
    rw [V.vdeflate.spec.lz_copy]
    simp only [IntRange.contains, show (0 : Int) ≤ d by omega,
      show (0 : Int) ≤ ((n + 1 : Nat) : Int) by omega, decide_true, Bool.and_self, dite_true]
    rw [dif_neg (by simp <;> omega), show ((n + 1 : Nat) : Int) - 1 = ((n : Nat) : Int) by omega,
      clip_nat u _ (by omega), Seq.len_list,
      show ((outV o).length : Int) - d = ((o.size - d : Nat) : Int) by simp; omega,
      Seq.index_eq u _ _ (by simp; omega)]
    have hx : (outV o)[o.size - d]'(by simp; omega) = ((o.getD (o.size - d) 0).toNat : Int) := by
      simp [Array.getD, show o.size - d < o.size by omega]
    rw [hx, outV_push, ih _ (by simp; omega)]
    rfl

/-! ## Taking branches -/

theorem dite_neg_eq {c : Prop} [Decidable c] {α : Sort _} {t : c → α} {e : ¬c → α} {r : α}
    (h : ¬c) (k : e h = r) : dite c t e = r := by rw [dif_neg h]; exact k
theorem dite_pos_eq {c : Prop} [Decidable c] {α : Sort _} {t : c → α} {e : ¬c → α} {r : α}
    (h : c) (k : t h = r) : dite c t e = r := by rw [dif_pos h]; exact k

/-- Take the else branch of the `if h : c` the goal's left side starts with. -/
macro "dneg" : tactic =>
  `(tactic| (refine dite_neg_eq (by first | omega | (simp <;> (repeat' apply And.intro) <;> omega) | (simp; done)) ?_
             try dsimp only))
/-- Take its then branch. -/
macro "dpos" : tactic =>
  `(tactic| (refine dite_pos_eq (by first | omega | (simp <;> (repeat' apply And.intro) <;> omega) | (simp; done)) ?_
             try dsimp only))

/-! ## 3.2.3, 3.2.5: compressed data -/

/-- `inflate_syms` decodes a block's symbols as `Deflate.inflateSyms` does, given
the codes' lengths. -/
theorem inflate_syms_eq (u : Unspec) (lit dist : Deflate.Lens) (b : Deflate.Bits) (p : Nat)
    (o : Array UInt8) :
    V.vdeflate.spec.inflate_syms u (lensV lit) (lensV dist) b.toList p (outV o) =
      Option.map (fun r : Array UInt8 × Nat => (outV r.1, (r.2 : Int)))
        (Deflate.inflateSyms (Deflate.code lit) (Deflate.code dist) b p o) := by
  induction p, o using Deflate.inflateSyms.induct (Deflate.code lit) b with
  | case1 p o hd =>
    rw [V.vdeflate.spec.inflate_syms, Deflate.inflateSyms, decode_sym_eq, hd]
    simp
  | case2 p o s p1 hd hs hg ih =>
    rw [V.vdeflate.spec.inflate_syms, Deflate.inflateSyms, decode_sym_eq, hd]
    rw [Option.map_some, Option.isNone_some, someVal_some]
    dneg; dneg; dpos
    rw [clip_u8 u _ (by omega) (by omega)]
    simp only [hs, ite_true, hg, dite_true, true_and]
    rw [show (s : Int) = ((s.toUInt8).toNat : Int) by simp; omega, outV_push, ih]
  | case3 p o s p1 hd hs hg =>
    have := Deflate.decodeSym_spec hd
    exact absurd this.2 hg
  | case4 p o p1 hd hs =>
    rw [V.vdeflate.spec.inflate_syms, Deflate.inflateSyms, decode_sym_eq, hd]
    have := Deflate.decodeSym_spec hd
    rw [Option.map_some, Option.isNone_some, someVal_some]
    dneg; dneg; dneg; dpos
    simp
  | case5 p o s p1 hd hs h256 ih =>
    have hsp := Deflate.decodeSym_spec hd
    rw [V.vdeflate.spec.inflate_syms, Deflate.inflateSyms, decode_sym_eq, hd]
    rw [Option.map_some, Option.isNone_some, someVal_some]
    dneg; dneg; dneg; dneg
    rw [if_neg hs, if_neg h256]
    rcases Nat.lt_or_ge 285 s with h285 | h285
    · dpos
      rw [lenTable_none (s - 257) (by omega)]; rfl
    dneg
    have ht := lenTable_eq ⟨s - 257, by omega⟩
    simp only [show s - 257 + 257 = s by omega] at ht
    rw [ht, len_extra_eq, getbits_eq, len_base_eq u s (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    have hsp' := hsp
    cases hg1 : Deflate.getbits b p1 (lenExtraF s) with
    | none => dpos; rfl
    | some e =>
      have hg1' := Deflate.getbits_some hg1
      rw [Option.map_some, Option.isNone_some, someVal_some]
      dneg
      rw [← Int.natCast_add, decode_sym_eq]
      cases hd2 : Deflate.decodeSym (Deflate.code dist) b (p1 + lenExtraF s) with
      | none => dpos; rfl
      | some x =>
        obtain ⟨ds, p3⟩ := x
        have hsp2 := Deflate.decodeSym_spec hd2
        rw [Option.map_some, Option.isNone_some, someVal_some]
        dneg
        simp only [Option.bind_some]
        rcases Nat.lt_or_ge 29 ds with h29 | h29
        · dpos
          rw [distTable_none ds (by omega)]; rfl
        dneg
        have ht2 := distTable_eq ⟨ds, by omega⟩
        rw [ht2, dist_extra_eq, getbits_eq, dist_base_eq]
        simp only [Option.bind_some]
        cases hg2 : Deflate.getbits b p3 (distExtraF ds) with
        | none => dpos; rfl
        | some e2 =>
          have hg2' := Deflate.getbits_some hg2
          rw [Option.map_some, Option.isNone_some, someVal_some]
          dneg
          simp only [Option.bind_some]
          by_cases hdo : distBaseF ds + e2 ≤ o.size
          · rw [if_pos hdo]
            unclip
            have hp4 : p < p3 + distExtraF ds ∧ p3 + distExtraF ds ≤ b.size := by omega
            rw [dif_pos hp4]
            dneg
            have hd1 : 1 ≤ distBaseF ds := by unfold distBaseF; split <;> omega
            rw [← Int.natCast_add, ← Int.natCast_add, ← Int.natCast_add]
            unclip
            rw [lz_copy_eq u o _ _ (by omega) hdo]
            exact ih (lenBaseF s) e p3 (distBaseF ds) (distExtraF ds) e2 hp4
          · rw [if_neg hdo]
            unclip
            dpos
            rfl

theorem lsbVal_lt (b : Deflate.Bits) (p n : Nat) : Deflate.lsbVal b p n < 2 ^ n := by
  induction n generalizing p with
  | zero => simp [Deflate.lsbVal]
  | succ n ih => have := ih (p + 1); simp only [Deflate.lsbVal, Nat.pow_succ]; split <;> omega

/-! ## 3.2.7: the dynamic header -/

/-- The Verus spec's code length order, without `Unspec`. -/
def clOrderF (i : Nat) : Nat :=
  if i = 0 then 16 else if i = 1 then 17 else if i = 2 then 18 else if i = 3 then 0
  else if i % 2 = 0 then 8 + (i - 4) / 2 else 7 - (i - 5) / 2

theorem cl_order_eq (u : Unspec) (i : Nat) (h : i < 19) :
    V.vdeflate.spec.cl_order u i = (clOrderF i : Int) := by
  unfold V.vdeflate.spec.cl_order clOrderF
  rw [dif_pos (by simp [IntRange.contains])]
  simp only [clip, ediv, emod, IntRange.contains, apply_ite (fun x : Nat => (x : Int))]
  repeat' split
  all_goals simp_all <;> omega

theorem clOrder_eq : ∀ k : Fin 19, Deflate.clOrder.getD k.val 0 = clOrderF k.val := by decide

theorem lensV_set (acc : Deflate.Lens) (i v : Nat) :
    lensV (acc.set! i v) = (lensV acc).set i (v : Int) := by
  simp [lensV, Array.set!, Array.toList_setIfInBounds, List.map_set]

theorem read_cl_eq (u : Unspec) (b : Deflate.Bits) (p0 hclen : Nat) (hh : hclen ≤ 19) :
    ∀ i (acc : Deflate.Lens), i ≤ hclen → acc.size = 19 →
      V.vdeflate.spec.read_cl u b.toList ((p0 + 3 * i : Nat) : Int) hclen i (lensV acc) =
        Option.map (fun r : Deflate.Lens × Nat => (lensV r.1, (r.2 : Int)))
          (Deflate.readCL.go b p0 hclen i acc) := by
  intro i acc
  induction i, acc using Deflate.readCL.go.induct hclen with
  | case1 i acc hi ih =>
    intro hle hs
    rw [V.vdeflate.spec.read_cl, Deflate.readCL.go]
    have hg3 : V.vdeflate.spec.getbits u b.toList ((p0 + 3 * i : Nat) : Int) 3 =
        Option.map (fun v : Nat => (v : Int)) (Deflate.getbits b (p0 + 3 * i) 3) := getbits_eq u b _ 3
    rw [dif_pos (by simp [IntRange.contains]), dif_neg (by simp; omega), if_pos hi, hg3]
    cases hg : Deflate.getbits b (p0 + 3 * i) 3 with
    | none => simp
    | some v =>
      have hv := Deflate.getbits_some hg
      have hv8 : v < 8 := by rw [hv.2]; exact lsbVal_lt b _ 3
      rw [Option.map_some]
      dsimp only
      rw [Option.isNone_some, someVal_some]
      simp only [Bool.false_eq_true, dite_false, Option.bind_eq_bind, Option.bind_some]
      rw [cl_order_eq u i (by omega), clip_u8 u _ (by omega) (by omega),
        Seq.update_eq u _ _ _ (by simp; have := clOrder_eq ⟨i, by omega⟩; unfold clOrderF at this ⊢; simp at this; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega),
        ← clOrder_eq ⟨i, by omega⟩, ← lensV_set,
        show ((p0 + 3 * i : Nat) : Int) + 3 = ((p0 + 3 * (i + 1) : Nat) : Int) by omega,
        show (i : Int) + 1 = ((i + 1 : Nat) : Int) by omega]
      exact ih v (by omega) (by simp [Array.size_setIfInBounds, Array.set!, hs])
  | case2 i acc hi =>
    intro hle hs
    rw [V.vdeflate.spec.read_cl, Deflate.readCL.go]
    rw [dif_pos (by simp [IntRange.contains]), dif_pos (by simp; omega), if_neg hi]
    simp; omega

theorem lensV_append_replicate (u : Unspec) (acc : Deflate.Lens) (n v : Nat) :
    lensV (acc ++ Array.replicate n v) = Seq.add (lensV acc) (Seq.new u (.int (.u 8)) (α := Int) rfl n (fun _ => (v : Int))) := by
  rw [Seq.new_eq, Seq.add_eq]
  simp [lensV, Array.toList_append, List.map_const']

theorem last_lensV {r : IntRange} (u : Unspec) (acc : Deflate.Lens) (x : Nat) (h : acc.back? = some x) :
    Seq.last u (.int r) (α := Int) rfl (lensV acc) = (x : Int) := by
  have hpos : 0 < acc.size := by
    rcases Nat.eq_zero_or_pos acc.size with h0 | h0
    · simp [Array.back?, h0] at h
    · exact h0
  have hne : acc.toList ≠ [] := by
    intro he
    have : acc.toList.length = 0 := by rw [he]; rfl
    rw [Array.length_toList] at this; omega
  have hx : acc.toList.getLast hne = x := by
    rw [List.getLast_eq_getElem]
    simp only [Array.back?, Array.getElem?_eq_getElem (show acc.size - 1 < acc.size by omega),
      Option.some.injEq] at h
    simpa using h
  rw [lensV, ← List.dropLast_concat_getLast hne, List.map_append, List.map_cons, List.map_nil,
    Seq.last_eq, hx]

theorem read_lens_eq (u : Unspec) (cl : Deflate.Lens) (hcl : cl.size = 19) (b : Deflate.Bits)
    (total : Nat) : ∀ (p : Nat) (acc : Deflate.Lens),
    V.vdeflate.spec.read_lens u (lensV cl) b.toList p total (lensV acc) =
      Option.map (fun r : Deflate.Lens × Nat => (lensV r.1, (r.2 : Int)))
        (Deflate.readLens (Deflate.code cl) b p total acc) := by
  intro p acc
  induction p, acc using Deflate.readLens.induct (Deflate.code cl) b total with
  | case1 p acc ht =>
    rw [V.vdeflate.spec.read_lens, Deflate.readLens]
    rw [dif_pos (by simp [IntRange.contains]), dif_pos (by simp; omega), dif_pos ht]; rfl
  | case2 p acc ht hd =>
    rw [V.vdeflate.spec.read_lens, Deflate.readLens]
    rw [dif_pos (by simp [IntRange.contains]), dif_neg (by simp; omega), dif_neg ht, decode_sym_eq, hd]
    rfl
  | case3 p acc ht s p1 hd hs ih =>
    have hsp := Deflate.decodeSym_spec hd
    rw [V.vdeflate.spec.read_lens, Deflate.readLens]
    rw [dif_pos (by simp [IntRange.contains]), dif_neg (by simp; omega), dif_neg ht, decode_sym_eq, hd,
      Option.map_some]
    dsimp only
    rw [Option.isNone_some, someVal_some]
    dneg; dpos
    rw [clip_u8 u _ (by omega) (by omega), if_pos hs,
      show Seq.push (lensV acc) (s : Int) = lensV (acc.push s) by simp [lensV, Seq.push_eq], ih]
  | case4 p acc ht s p1 hd hs nb base ih =>
    have hsp := Deflate.decodeSym_spec hd
    rw [V.vdeflate.spec.read_lens, Deflate.readLens]
    rw [dif_pos (by simp [IntRange.contains]), dif_neg (by simp; omega), dif_neg ht, decode_sym_eq, hd,
      Option.map_some]
    dsimp only
    rw [Option.isNone_some, someVal_some]
    dneg; dneg
    rw [if_neg hs]
    rw [Deflate.code_size, hcl] at hsp
    rcases (show s = 16 ∨ s = 17 ∨ s = 18 by omega) with rfl | rfl | rfl
    · simp (config := { decide := true }) only [dite_true, dite_false, ite_true, ite_false,
        Bool.and_true] at ih ⊢
      rw [show (2 : Int) = ((2 : Nat) : Int) by rfl, getbits_eq]
      cases hg : Deflate.getbits b p1 2 with
      | none => rw [Option.map_none]; rfl
      | some e =>
        rw [Option.map_some]; try dsimp only
        rw [Option.isNone_some, someVal_some]
        dneg
        simp only [Option.bind_eq_bind, Option.bind_some]
        cases hb : acc.back? with
        | none =>
          have : acc.size = 0 := by
            rcases Nat.eq_zero_or_pos acc.size with h0 | h0
            · exact h0
            · simp [Array.back?, Array.getElem?_eq_getElem (show acc.size - 1 < acc.size by omega)] at hb
          have hacc : acc = #[] := Array.eq_empty_of_size_eq_zero this
          refine dite_pos_eq (by simp [hacc]) ?_
          rfl
        | some x =>
          have hpos : 0 < acc.size := by
            rcases Nat.eq_zero_or_pos acc.size with h0 | h0
            · simp [Array.back?, h0] at hb
            · exact h0
          have hacc : acc ≠ #[] := by intro h; simp [h] at hpos
          simp only [Option.bind_some]
          unclip
          by_cases hle : acc.size + (3 + e) ≤ total
          · refine dite_neg_eq (by simp [hacc]; omega) ?_
            rw [if_pos hle, last_lensV u acc x hb,
              show (3 : Int) + (e : Int) = ((3 + e : Nat) : Int) by omega,
              show (p1 : Int) + ((2 : Nat) : Int) = ((p1 + 2 : Nat) : Int) by omega,
              ← lensV_append_replicate]
            exact ih e x
          · refine dite_pos_eq (by simp [hacc]; omega) ?_
            rw [if_neg hle]; rfl
    · simp (config := { decide := true }) only [dite_true, dite_false, ite_true, ite_false,
        Bool.and_true] at ih ⊢
      have hgb : V.vdeflate.spec.getbits u b.toList (p1 : Int) 3 =
          Option.map (fun v : Nat => (v : Int)) (Deflate.getbits b p1 3) := getbits_eq u b p1 3
      rw [hgb]
      cases hg : Deflate.getbits b p1 3 with
      | none => rw [Option.map_none]; rfl
      | some e =>
        rw [Option.map_some]; try dsimp only
        rw [Option.isNone_some, someVal_some]
        dneg
        simp only [Option.bind_eq_bind, Option.bind_some]
        unclip
        by_cases hle : acc.size + (3 + e) ≤ total
        · refine dite_neg_eq (by simp; omega) ?_
          rw [if_pos hle,
            show (3 : Int) + (e : Int) = ((3 + e : Nat) : Int) by omega,
            show (p1 : Int) + (3 : Int) = ((p1 + 3 : Nat) : Int) by omega,
            show (fun (_ : Int) => (0 : Int)) = (fun _ => ((0 : Nat) : Int)) from rfl,
            ← lensV_append_replicate]
          exact ih e 0
        · refine dite_pos_eq (by simp; omega) ?_
          rw [if_neg hle]; rfl
    · simp (config := { decide := true }) only [dite_true, dite_false, ite_true, ite_false,
        Bool.and_true] at ih ⊢
      have hgb : V.vdeflate.spec.getbits u b.toList (p1 : Int) 7 =
          Option.map (fun v : Nat => (v : Int)) (Deflate.getbits b p1 7) := getbits_eq u b p1 7
      rw [hgb]
      cases hg : Deflate.getbits b p1 7 with
      | none => rw [Option.map_none]; rfl
      | some e =>
        rw [Option.map_some]; try dsimp only
        rw [Option.isNone_some, someVal_some]
        dneg
        simp only [Option.bind_eq_bind, Option.bind_some]
        unclip
        by_cases hle : acc.size + (11 + e) ≤ total
        · refine dite_neg_eq (by simp; omega) ?_
          rw [if_pos hle,
            show (11 : Int) + (e : Int) = ((11 + e : Nat) : Int) by omega,
            show (p1 : Int) + (7 : Int) = ((p1 + 7 : Nat) : Int) by omega,
            show (fun (_ : Int) => (0 : Int)) = (fun _ => ((0 : Nat) : Int)) from rfl,
            ← lensV_append_replicate]
          exact ih e 0
        · refine dite_pos_eq (by simp; omega) ?_
          rw [if_neg hle]; rfl


theorem readCL_go_size (b : Deflate.Bits) (p hclen : Nat) :
    ∀ i (acc : Deflate.Lens) cl q, acc.size = 19 →
      Deflate.readCL.go b p hclen i acc = some (cl, q) → cl.size = 19 := by
  intro i acc
  induction i, acc using Deflate.readCL.go.induct hclen with
  | case1 i acc hi ih =>
    intro cl q hs h
    rw [Deflate.readCL.go, if_pos hi] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, -, h⟩ := h
    exact ih v cl q (by simp [Array.set!, hs]) h
  | case2 i acc hi =>
    intro cl q hs h
    rw [Deflate.readCL.go, if_neg hi] at h
    simp at h; rw [← h.1]; exact hs

theorem readLens_size (c : Array (Nat × Nat)) (b : Deflate.Bits) (total : Nat) :
    ∀ p (acc : Deflate.Lens) lens r, acc.size ≤ total →
      Deflate.readLens c b p total acc = some (lens, r) → lens.size = total := by
  intro p acc
  induction p, acc using Deflate.readLens.induct c b total with
  | case1 p acc ht =>
    intro lens r hs h; rw [Deflate.readLens, dif_pos ht] at h; simp at h; rw [← h.1]; omega
  | case2 p acc ht hd =>
    intro lens r hs h; rw [Deflate.readLens, dif_neg ht, hd] at h; simp at h
  | case3 p acc ht s p1 hd hs ih =>
    intro lens r hle h
    rw [Deflate.readLens, dif_neg ht, hd] at h
    simp only [hs, ite_true] at h
    exact ih lens r (by simp; omega) h
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
      obtain ⟨v, -, h⟩ := h
      split at h
      · exact ih e v lens r (by simp; omega) h
      · simp at h

theorem guard_pos' {c : Prop} [Decidable c] (h : c) : (guard c : Option Unit) = some () := by
  simp [guard, h] <;> rfl
theorem guard_neg' {c : Prop} [Decidable c] (h : ¬c) : (guard c : Option Unit) = none := by
  simp [guard, h] <;> rfl

theorem lensV_extract (L : Deflate.Lens) (i j : Nat) (h : i ≤ j) (hj : j ≤ L.size) :
    Seq.subrange (lensV L) i j = lensV (L.extract i j) := by
  rw [Seq.subrange_eq _ i j h (by simp; omega)]
  simp [lensV, Array.toList_extract, List.extract, List.map_take, List.map_drop]

theorem lensV_extract0 (L : Deflate.Lens) (j : Nat) (hj : j ≤ L.size) :
    Seq.subrange (lensV L) 0 j = lensV (L.extract 0 j) := lensV_extract L 0 j (by omega) hj

theorem getbits_eq_at (u : Unspec) (b : Deflate.Bits) (p k n : Nat) :
    V.vdeflate.spec.getbits u b.toList ((p : Int) + (k : Int)) n =
      Option.map (fun v : Nat => (v : Int)) (Deflate.getbits b (p + k) n) := by
  rw [← Int.natCast_add]; exact getbits_eq u b (p + k) n

theorem dyn_header_eq (u : Unspec) (b : Deflate.Bits) (p : Nat) :
    V.vdeflate.spec.dyn_header u b.toList p =
      Option.map (fun r : Deflate.Lens × Deflate.Lens × Nat × Bool =>
          (lensV r.1, lensV r.2.1, (r.2.2.1 : Int), r.2.2.2))
        (Deflate.dynHeader b p) := by
  unfold V.vdeflate.spec.dyn_header Deflate.dynHeader
  have g1 : V.vdeflate.spec.getbits u b.toList (p : Int) 5 =
      Option.map (fun v : Nat => (v : Int)) (Deflate.getbits b p 5) := getbits_eq u b p 5
  have g2 : V.vdeflate.spec.getbits u b.toList ((p : Int) + 5) 5 =
      Option.map (fun v : Nat => (v : Int)) (Deflate.getbits b (p + 5) 5) := getbits_eq_at u b p 5 5
  have g3 : V.vdeflate.spec.getbits u b.toList ((p : Int) + 10) 4 =
      Option.map (fun v : Nat => (v : Int)) (Deflate.getbits b (p + 10) 4) := getbits_eq_at u b p 10 4
  rw [g1, g2, g3]
  cases h1 : Deflate.getbits b p 5 <;> cases h2 : Deflate.getbits b (p + 5) 5 <;>
    cases h3 : Deflate.getbits b (p + 10) 4
  all_goals try (simp; done)
  rename_i hlit hdist hclen
  have b1 := Deflate.getbits_some h1
  have b2 := Deflate.getbits_some h2
  have b3 := Deflate.getbits_some h3
  have hl32 : hlit < 32 := by rw [b1.2]; exact lsbVal_lt b _ 5
  have hd32 : hdist < 32 := by rw [b2.2]; exact lsbVal_lt b _ 5
  have hc16 : hclen < 16 := by rw [b3.2]; exact lsbVal_lt b _ 4
  rw [Option.map_some, Option.map_some, Option.map_some]
  dsimp only
  rw [someVal_some, someVal_some, someVal_some]
  dpos
  simp only [Option.bind_eq_bind, Option.bind_some]
  unclip
  rcases Nat.lt_or_ge 286 (hlit + 257) with hn | hn
  · dpos
    rw [guard_neg' (by omega)]; rfl
  dneg
  rw [guard_pos' hn, Option.bind_some]
  have hrc : V.vdeflate.spec.read_cl u b.toList ((p : Int) + 14) ((hclen : Int) + 4) 0
      (Seq.new u (.int (.u 8)) (α := Int) rfl 19 fun _ => 0) =
      Option.map (fun r : Deflate.Lens × Nat => (lensV r.1, (r.2 : Int)))
        (Deflate.readCL b (p + 14) (hclen + 4)) := by
    have := read_cl_eq u b (p + 14) (hclen + 4) (by omega) 0 (Array.replicate 19 0) (by omega) (by simp)
    rw [show (Seq.new u (.int (.u 8)) (α := Int) rfl 19 fun _ => (0 : Int)) = lensV (Array.replicate 19 0) by
          rw [show (19 : Int) = ((19 : Nat) : Int) by rfl, Seq.new_eq]; simp [lensV, List.map_const'],
      show (p : Int) + 14 = ((p + 14 + 3 * 0 : Nat) : Int) by omega,
      show (hclen : Int) + 4 = ((hclen + 4 : Nat) : Int) by omega,
      show (0 : Int) = ((0 : Nat) : Int) by rfl, this]
    rfl
  rw [hrc]
  cases hR : Deflate.readCL b (p + 14) (hclen + 4) with
  | none => dpos; rfl
  | some x =>
    obtain ⟨cl, q⟩ := x
    have hcl : cl.size = 19 := readCL_go_size b (p + 14) (hclen + 4) 0 _ cl q (by simp) hR
    rw [Option.bind_some]
    try dsimp only
    rw [Option.map_some]
    try dsimp only
    rw [Option.isNone_some, someVal_some]
    dneg
    try dsimp only
    rw [not_oversub_eq]
    by_cases hov : Deflate.notOversub cl = true
    · dneg
      rw [guard_pos' hov, Option.bind_some]
      try dsimp only
      have hrl := read_lens_eq u cl hcl b (hlit + 257 + (hdist + 1)) q #[]
      rw [show (hlit : Int) + 257 + ((hdist : Int) + 1) = ((hlit + 257 + (hdist + 1) : Nat) : Int) by omega,
        show (Seq.empty : List Int) = lensV #[] from rfl, hrl]
      cases hL : Deflate.readLens (Deflate.code cl) b q (hlit + 257 + (hdist + 1)) #[] with
      | none => dpos; rfl
      | some y =>
        obtain ⟨lens, r⟩ := y
        have hsz := readLens_size _ b _ q #[] lens r (by simp) hL
        rw [Option.map_some]
        try dsimp only
        rw [Option.isNone_some, someVal_some]
        dneg
        rw [Option.bind_some]
        try dsimp only
        rw [show (hlit : Int) + 257 = ((hlit + 257 : Nat) : Int) by omega,
          lensV_extract0 lens (hlit + 257) (by omega),
          lensV_extract lens (hlit + 257) (hlit + 257 + (hdist + 1)) (by omega) (by omega)]
        have hi : Seq.index u (.int (.u 8)) (α := Int) rfl (lensV (lens.extract 0 (hlit + 257))) 256 =
            (((lens.extract 0 (hlit + 257))[256]'(by simp; omega) : Nat) : Int) :=
          index_lensV u _ 256 (by simp; omega)
        rw [hi, not_oversub_eq, not_oversub_eq, zlib_ok_eq, zlib_ok_eq, zlib_ok_eq]
        have h256 : 256 < (lens.extract 0 (hlit + 257)).size := by simp; omega
        have hg : (lens.extract 0 (hlit + 257)).getD 256 0 = (lens.extract 0 (hlit + 257))[256]'h256 := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h256]; rfl
        by_cases g1 : (lens.extract 0 (hlit + 257)).getD 256 0 ≠ 0
        · have g1' : (lens.extract 0 (hlit + 257))[256]'h256 ≠ 0 := hg ▸ g1
          by_cases g2 : (Deflate.notOversub (lens.extract 0 (hlit + 257)) &&
              Deflate.notOversub (lens.extract (hlit + 257) (hlit + 257 + (hdist + 1)))) = true
          · rw [Bool.and_eq_true] at g2
            refine dite_neg_eq ?side ?main
            case side =>
              intro hc
              simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
              rcases hc with (hc | hc) | hc
              · omega
              · rw [g2.1] at hc; exact Bool.noConfusion hc
              · rw [g2.2] at hc; exact Bool.noConfusion hc
            case main =>
              rw [guard_pos' g1, Option.bind_some, guard_pos' (Bool.and_eq_true _ _ ▸ g2), Option.bind_some]
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
              congr 1
              rw [decide_eq_decide]; constructor <;> intro <;> omega
          · refine dite_pos_eq ?side ?main
            case side =>
              simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
              rw [Bool.and_eq_true] at g2
              cases h : Deflate.notOversub (lens.extract 0 (hlit + 257)) with
              | false => left; right; rfl
              | true =>
                right
                cases h' : Deflate.notOversub (lens.extract (hlit + 257) (hlit + 257 + (hdist + 1))) with
                | false => rfl
                | true => exact absurd ⟨h, h'⟩ g2
            case main =>
              rw [guard_pos' g1, Option.bind_some, guard_neg' g2]; rfl
        · refine dite_pos_eq ?side ?main
          case side =>
            simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
            left; left
            have : (lens.extract 0 (hlit + 257))[256]'h256 = 0 := by rw [← hg]; simpa using g1
            rw [this]; rfl
          case main =>
            rw [guard_neg' g1]; rfl
    · refine dite_pos_eq (by simpa using hov) ?_
      rw [guard_neg' hov]; rfl

/-! ## 3.2.4: stored blocks -/

theorem stored_byte (u : Unspec) (b : Deflate.Bits) (a : Nat) (h : a + 8 ≤ b.size) :
    clip u (.u 8) (V.vbits.lsb.lval u (Seq.subrange b.toList (a : Int) ((a + 8 : Nat) : Int))) =
      (((Deflate.lsbVal b a 8).toUInt8).toNat : Int) := by
  rw [Seq.subrange_eq _ a (a + 8) (by omega) (by simp; omega), lval_eq,
    show a + 8 - a = 8 by omega, lsbList_take b a 8 h]
  have := lsbVal_lt b a 8
  rw [clip_u8 u _ (by omega) (by omega)]
  simp; omega

theorem stored_eq (u : Unspec) (b : Deflate.Bits) (p : Nat) :
    V.vdeflate.spec.stored u b.toList p =
      Option.map (fun r : Array UInt8 × Nat => (outV r.1, (r.2 : Int))) (Deflate.stored b p) := by
  unfold V.vdeflate.spec.stored Deflate.stored
  have hq : (if h3 : decide (emod u (p : Int) 8 = 0) = true then (p : Int) else (p : Int) + (8 - emod u p 8)) =
      (((p + 7) / 8 * 8 : Nat) : Int) := by
    rw [emod_ne u _ _ (by omega)]
    split
    · rename_i h; simp at h; omega
    · rename_i h; simp at h; omega
  dsimp only
  rw [hq]
  generalize (p + 7) / 8 * 8 = q
  have g1 : V.vdeflate.spec.getbits u b.toList (q : Int) 16 =
      Option.map (fun v : Nat => (v : Int)) (Deflate.getbits b q 16) := getbits_eq u b q 16
  have g2 : V.vdeflate.spec.getbits u b.toList ((q : Int) + 16) 16 =
      Option.map (fun v : Nat => (v : Int)) (Deflate.getbits b (q + 16) 16) := getbits_eq_at u b q 16 16
  rw [g1, g2]
  cases h1 : Deflate.getbits b q 16 <;> cases h2 : Deflate.getbits b (q + 16) 16
  all_goals try (simp; done)
  rename_i len nlen
  rw [Option.map_some, Option.map_some]
  try dsimp only
  rw [someVal_some, someVal_some]
  dpos
  simp only [Option.bind_eq_bind, Option.bind_some]
  unclip
  by_cases c1 : len + nlen = 65535
  · rw [guard_pos' c1, Option.bind_some]
    by_cases c2 : q + 32 + 8 * len ≤ b.size
    · rw [guard_pos' c2, Option.bind_some]
      refine dite_neg_eq (by simp; omega) ?_
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rw [Seq.new_eq]
        apply List.ext_getElem (by simp)
        intro k hk1 hk2
        simp only [List.length_map, List.length_range] at hk1
        simp only [List.getElem_map, List.getElem_range, outV, Array.getElem_toList, Array.getElem_ofFn]
        rw [show (q : Int) + 32 + 8 * (k : Int) = ((q + 32 + 8 * k : Nat) : Int) by omega,
          show (q : Int) + 40 + 8 * (k : Int) = ((q + 32 + 8 * k + 8 : Nat) : Int) by omega,
          stored_byte u b _ (by omega)]
      · omega
    · rw [guard_neg' c2]; refine dite_pos_eq (by simp; omega) ?_; rfl
  · rw [guard_neg' c1]; refine dite_pos_eq (by simp; omega) ?_; rfl

/-! ## 3.2.3: blocks and the stream -/

theorem outV_append (o bytes : Array UInt8) : Seq.add (outV o) (outV bytes) = outV (o ++ bytes) := by
  simp [outV, Seq.add_eq, Array.toList_append]

theorem block_eq (u : Unspec) (b : Deflate.Bits) (p btype : Nat) (o : Array UInt8) :
    V.vdeflate.spec.block u b.toList p btype (outV o) =
      Option.map (fun r : Array UInt8 × Nat × Bool => (outV r.1, (r.2.1 : Int), r.2.2))
        (Deflate.block b p btype o) := by
  unfold V.vdeflate.spec.block
  rw [dif_pos (by simp [IntRange.contains])]
  rcases (show btype = 0 ∨ btype = 1 ∨ btype = 2 ∨ 3 ≤ btype by omega) with rfl | rfl | rfl | h3
  · dpos
    simp only [Deflate.block, Option.bind_eq_bind]
    rw [stored_eq]
    cases hs : Deflate.stored b p with
    | none => rfl
    | some x =>
      obtain ⟨bytes, q⟩ := x
      rw [Option.map_some]; try dsimp only
      rw [Option.isNone_some, someVal_some]
      refine dite_neg_eq (by simp) ?_
      simp [outV_append]
  · dneg; dpos
    simp only [Deflate.block, Option.bind_eq_bind]
    rw [fixed_lit_eq, fixed_dist_eq, inflate_syms_eq]
    cases hs : Deflate.inflateSyms (Deflate.code Deflate.fixedLit) (Deflate.code Deflate.fixedDist) b p o with
    | none => rfl
    | some x =>
      obtain ⟨o', q⟩ := x
      rw [Option.map_some]; try dsimp only
      rw [Option.isNone_some, someVal_some]
      refine dite_neg_eq (by simp) ?_
      simp
  · dneg; dneg; dpos
    simp only [Deflate.block, Option.bind_eq_bind]
    rw [dyn_header_eq]
    cases hd : Deflate.dynHeader b p with
    | none => rfl
    | some x =>
      obtain ⟨lit, dist, q, z⟩ := x
      rw [Option.map_some]; try dsimp only
      rw [Option.isNone_some, someVal_some]
      refine dite_neg_eq (by simp) ?_
      try dsimp only
      rw [inflate_syms_eq, Option.bind_some]
      cases hs : Deflate.inflateSyms (Deflate.code lit) (Deflate.code dist) b q o with
      | none => rfl
      | some y =>
        obtain ⟨o', r⟩ := y
        rw [Option.map_some]; try dsimp only
        rw [Option.isNone_some, someVal_some]
        refine dite_neg_eq (by simp) ?_
        simp
  · dneg; dneg; dneg
    obtain ⟨k, rfl⟩ : ∃ k, btype = k + 3 := ⟨btype - 3, by omega⟩
    rfl

theorem inflate_blocks_eq (u : Unspec) (b : Deflate.Bits) (p : Nat) (o : Array UInt8) (z : Bool) :
    V.vdeflate.spec.inflate_blocks u b.toList p (outV o) z =
      Option.map (fun r : Array UInt8 × Nat × Bool => (outV r.1, (r.2.1 : Int), r.2.2))
        (Deflate.inflateBlocks b p o z) := by
  induction p, o, z using Deflate.inflateBlocks.induct b with
  | case1 p o z ih =>
    rw [V.vdeflate.spec.inflate_blocks, Deflate.inflateBlocks]
    have g1 : V.vdeflate.spec.getbits u b.toList (p : Int) 1 =
        Option.map (fun v : Nat => (v : Int)) (Deflate.getbits b p 1) := getbits_eq u b p 1
    have g2 : V.vdeflate.spec.getbits u b.toList ((p : Int) + 1) 2 =
        Option.map (fun v : Nat => (v : Int)) (Deflate.getbits b (p + 1) 2) := getbits_eq_at u b p 1 2
    rw [g1, g2]
    cases h1 : Deflate.getbits b p 1 <;> cases h2 : Deflate.getbits b (p + 1) 2
    all_goals try (simp; done)
    rename_i bfinal btype
    rw [Option.map_some, Option.map_some]
    try dsimp only
    rw [someVal_some, someVal_some]
    dpos
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [show (p : Int) + 3 = ((p + 3 : Nat) : Int) by omega, block_eq]
    cases hb : Deflate.block b (p + 3) btype o with
    | none => rfl
    | some x =>
      obtain ⟨o', q, z'⟩ := x
      have hq := Deflate.guard_blocks hb
      rw [Option.map_some]; try dsimp only
      rw [Option.isNone_some, someVal_some]
      dneg
      try dsimp only
      rw [Option.bind_some]
      try dsimp only
      by_cases hf : bfinal = 1
      · refine dite_pos_eq (by simp; omega) ?_
        rw [if_pos hf]; rfl
      · refine dite_neg_eq (by simp; omega) ?_
        rw [if_neg hf]
        dneg
        rw [dif_pos hq]
        exact ih o' q z' hq

/-- **vdeflate's Verus spec is the Lean spec.** For every choice of what Verus
leaves unspecified, `vdeflate::spec::inflate` (translated from Verus's VIR)
decodes exactly the streams `Deflate.inflate` decodes, to the same data, the
same bit count and the same zlib flag. -/
theorem verus_inflate_eq (u : Unspec) (b : Deflate.Bits) :
    V.vdeflate.spec.inflate u b.toList =
      Option.map (fun d : Deflate.Decoded => (outV d.out, (d.bits : Int), d.zlib))
        (Deflate.inflate b) := by
  unfold V.vdeflate.spec.inflate Deflate.inflate
  rw [show (0 : Int) = ((0 : Nat) : Int) by rfl, show (Seq.empty : List Int) = outV #[] from rfl,
    inflate_blocks_eq]
  cases h : Deflate.inflateBlocks b 0 #[] true with
  | none => rfl
  | some x =>
    obtain ⟨o, q, z⟩ := x
    rw [Option.map_some]; try dsimp only
    rw [Option.isNone_some, someVal_some]
    refine dite_neg_eq (by simp) ?_
    try dsimp only
    rw [clip_nat u _ (by omega)]
    rfl

end Bridge
