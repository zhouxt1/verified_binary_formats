import Lspec.Deflate.PuffExport

/-!
# What `vpuff/` imports into Rocq for puff's whole inflate

`PuffExport.lean` covers the Huffman decoder. This file adds the rest of the
spec in the same style (equations between computable values, `Bool`
conditions, one unfolding equation per definition), and the facts about the
spec that the C proof needs:

* puff's checks on the code lengths are `zlibOk` (`zlibOk_cl_eq`,
  `zlibOk_lit_eq`), in terms of the counts `cnt` and the Kraft sum `kr` that
  puff's `construct()` computes;
* outputs only grow (`inflateSyms_size`, `inflateBlocks_size`), so running
  out of output space early means the spec's output does not fit either;
* once a block is outside what zlib accepts, so is the stream
  (`inflateBlocks_false`).

`vpuff/export.sh` lists the declarations to export; keep the two in step.
-/

namespace Deflate.InflateExport
open Deflate Deflate.Puff

theorem blt_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  simpa [Nat.blt_eq] using h
theorem blt_of_not_lt {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (Deflate.Puff.Export.blt_true hb) h

/-! ## The length and distance tables, as formulas -/

/-- Base length of length symbol `257 + i`. -/
def lenBase (i : Nat) : Nat :=
  if i < 8 then i + 3 else if i = 28 then 258 else 2 ^ (i / 4 - 1) * (4 + i % 4) + 3
/-- Extra bits of length symbol `257 + i`. -/
def lenExtra (i : Nat) : Nat := if i < 8 then 0 else if i = 28 then 0 else i / 4 - 1
/-- Base distance of distance symbol `i`. -/
def distBase (i : Nat) : Nat := if i < 4 then i + 1 else 2 ^ (i / 2 - 1) * (2 + i % 2) + 1
/-- Extra bits of distance symbol `i`. -/
def distExtra (i : Nat) : Nat := if i < 4 then 0 else i / 2 - 1

theorem lenTable_get (i : Nat) :
    lenTable[i]? = bif Nat.blt i 29 then some (lenBase i, lenExtra i) else none := by
  have all : ∀ j, j < 29 → lenTable[j]? = some (lenBase j, lenExtra j) := by decide
  by_cases h : i < 29
  · rw [blt_of_lt h, all i h]; rfl
  · rw [blt_of_not_lt h]; simp [lenTable]; omega

theorem distTable_get (i : Nat) :
    distTable[i]? = bif Nat.blt i 30 then some (distBase i, distExtra i) else none := by
  have all : ∀ j, j < 30 → distTable[j]? = some (distBase j, distExtra j) := by decide
  by_cases h : i < 30
  · rw [blt_of_lt h, all i h]; rfl
  · rw [blt_of_not_lt h]; simp [distTable]; omega

/-! ## puff's checks on code lengths are zlib's -/

theorem count_eq_blCount (lens : Lens) (l : Nat) : lens.toList.count l = blCount lens l := rfl

/-- A length of 1..15 contributes a positive amount to the Kraft sum. -/
theorem kraft_list_pos (L : List Nat) (x : Nat) (hx : x ∈ L) (h1 : 1 ≤ x) (h15 : x ≤ maxBits) :
    2 ^ (maxBits - x) ≤ (L.map fun len => if 1 ≤ len ∧ len ≤ maxBits then 2 ^ (maxBits - len) else 0).sum := by
  induction L with
  | nil => cases hx
  | cons y L ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [if_pos ⟨h1, h15⟩]; omega
    · have := ih hx; omega

/-- With every length at most 1, the Kraft sum counts the length-1 codes. -/
theorem kraft_le1 (L : List Nat) (h : ∀ x ∈ L, x ≤ 1) :
    (L.map fun len => if 1 ≤ len ∧ len ≤ maxBits then 2 ^ (maxBits - len) else 0).sum =
      L.count 1 * 2 ^ 14 := by
  induction L with
  | nil => rfl
  | cons y L ih =>
    rw [List.map_cons, List.sum_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      List.count_cons]
    have hy := h y (List.mem_cons_self ..)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> simp [maxBits] <;> omega

theorem count01_le (L : List Nat) : L.count 0 + L.count 1 ≤ L.length := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.count_cons, List.length_cons]
    by_cases y0 : y = 0
    · subst y0; simp; omega
    · by_cases y1 : y = 1
      · subst y1; simp; omega
      · simp [beq_iff_eq, y0, y1]; omega

/-- Lengths are all at most 1 exactly when they are all 0 or 1 by count. -/
theorem count01 (L : List Nat) : (∀ x ∈ L, x ≤ 1) ↔ L.count 0 + L.count 1 = L.length := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.count_cons, List.length_cons, ih]
    have hc := count01_le L
    by_cases y0 : y = 0
    · subst y0; simp; omega
    · by_cases y1 : y = 1
      · subst y1; simp; omega
      · have : ¬ y ≤ 1 := by omega
        simp [this, beq_iff_eq, y0, y1]; omega

/-- `kraft` on a list. -/
def kraftL (L : List Nat) : Nat :=
  (L.map fun len => if 1 ≤ len ∧ len ≤ maxBits then 2 ^ (maxBits - len) else 0).sum

theorem kraft_eq_kraftL (lens : Lens) : kraft lens = kraftL lens.toList := rfl

theorem kraftL_cons (y : Nat) (L : List Nat) :
    kraftL (y :: L) = (if 1 ≤ y ∧ y ≤ maxBits then 2 ^ (maxBits - y) else 0) + kraftL L := by
  simp [kraftL]

theorem all0_list (L : List Nat) : L.all (· == 0) = (L.count 0 == L.length) := by
  induction L with
  | nil => rfl
  | cons y L ih =>
    have := List.count_le_length (a := 0) (l := L)
    by_cases y0 : y = 0
    · subst y0; simp [ih]
    · have h1 : (L.count 0 == L.length + 1) = false := by
        simp only [beq_eq_false_iff_ne]; omega
      simp [y0, List.count_cons, h1]

theorem zlibOk_all0 (lens : Lens) : lens.all (· == 0) = (blCount lens 0 == lens.size) := by
  rw [← Array.all_toList, all0_list]; simp [blCount]

/-- The Kraft sum counts each length-1 code as 2^14 and each code of 2..15
bits as at least 1. -/
theorem kraft_ge (L : List Nat) :
    L.count 1 * 2 ^ 14 + (L.filter fun x => 2 ≤ x ∧ x ≤ maxBits).length ≤ kraftL L := by
  induction L with
  | nil => simp [kraftL]
  | cons y L ih =>
    rw [kraftL_cons, List.count_cons, List.filter_cons]
    by_cases y1 : y = 1
    · subst y1
      have e3 : (1 ≤ 1 ∧ 1 ≤ maxBits) := by decide
      have e2 : ¬ (2 ≤ 1 ∧ 1 ≤ maxBits) := by decide
      rw [if_pos e3]
      have h1 : ((1 : Nat) == 1) = true := rfl
      have h2 : ¬ (decide (2 ≤ 1 ∧ 1 ≤ maxBits) = true) := by decide
      rw [if_pos h1, if_neg h2]
      have : maxBits - 1 = 14 := rfl
      rw [this]
      clear this e2 e3 h1 h2
      generalize List.count 1 L = c at *
      generalize (List.filter (fun x => decide (2 ≤ x ∧ x ≤ maxBits)) L).length = f at *
      generalize kraftL L = k at *
      generalize (2 : Nat) ^ 14 = t at *
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · have e1 : (y == 1) = false := by simpa using y1
      simp only [e1, Bool.false_eq_true, if_false, Nat.add_zero, decide_eq_true_eq]
      by_cases hy : 2 ≤ y ∧ y ≤ maxBits
      · have : 1 ≤ 2 ^ (maxBits - y) := Nat.one_le_two_pow
        rw [if_pos hy, if_pos ⟨by omega, hy.2⟩, List.length_cons]
        simp only [Nat.reducePow] at ih ⊢
        generalize 2 ^ (maxBits - y) = t at *
        omega
      · rw [if_neg hy]
        simp only [Nat.reducePow] at ih ⊢
        generalize (if 1 ≤ y ∧ y ≤ maxBits then 2 ^ (maxBits - y) else 0) = t at *
        omega

theorem kraftL_le1 (L : List Nat) (h : ∀ x ∈ L, x ≤ 1) : kraftL L = L.count 1 * 2 ^ 14 := by
  induction L with
  | nil => rfl
  | cons y L ih =>
    rw [kraftL_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.count_cons]
    have hy := h y (List.mem_cons_self ..)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> simp [maxBits] <;> omega

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem ble_false_of_lt {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hb : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hb) (by omega)

theorem decide_le_ble (a b : Nat) : decide (a ≤ b) = Nat.ble a b := by
  cases h : Nat.ble a b
  · exact decide_eq_false (fun h' => by rw [Nat.ble_eq_true_of_le h'] at h; cases h)
  · exact decide_eq_true (Nat.le_of_ble_eq_true h)

theorem notOversub_ble (lens : Lens) : notOversub lens = Nat.ble (kraft lens) 32768 := by
  unfold notOversub; rw [decide_le_ble]; rfl

/-- puff accepts a literal/length or distance code (`dynamic()`: construct()
must not fail, and an incomplete code must be a single length-1 code) exactly
when the spec does and zlib does. Code lengths are at most 15. -/
theorem puff_lit_ok (lens : Lens) (h15 : ∀ i, lens.getD i 0 ≤ maxBits) :
    (notOversub lens && zlibOk lens false) =
      (Nat.ble (kr (blCount lens) maxBits) 32768 &&
        (Nat.beq (kr (blCount lens) maxBits) 32768 ||
          Nat.beq (blCount lens 0 + blCount lens 1) lens.size)) := by
  have hL : ∀ x ∈ lens.toList, x ≤ maxBits := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < lens.size := by simpa using hi
    have := h15 i; simpa [Array.getD, hi'] using this
  -- the facts about the lengths the Boolean argument needs
  have h01 : lens.toList.count 0 + lens.toList.count 1 = lens.toList.length →
      kraftL lens.toList = lens.toList.count 1 * 2 ^ 14 :=
    fun h => kraftL_le1 _ ((count01 _).mpr h)
  have hF : (lens.toList.filter fun x => 2 ≤ x ∧ x ≤ maxBits).length = 0 →
      lens.toList.count 0 + lens.toList.count 1 = lens.toList.length := by
    intro hz
    apply (count01 lens.toList).mp
    intro x hx
    have := hL x hx
    rcases Nat.lt_or_ge 1 x with hx1 | hx1
    · have hmem : x ∈ lens.toList.filter fun x => 2 ≤ x ∧ x ≤ maxBits :=
        List.mem_filter.mpr ⟨hx, by simp; omega⟩
      rw [List.length_eq_zero_iff] at hz
      rw [hz] at hmem; cases hmem
    · exact hx1
  have hk := kraft_ge lens.toList
  have hc := count01_le lens.toList
  rw [← kraft_eq_kr, notOversub_ble]
  unfold zlibOk complete
  rw [zlibOk_all0, kraft_eq_kraftL]
  unfold blCount
  have hsize : lens.size = lens.toList.length := by simp
  rw [hsize]
  generalize kraftL lens.toList = K at *
  generalize lens.toList.count 0 = c0 at *
  generalize lens.toList.count 1 = c1 at *
  generalize (lens.toList.filter fun x => 2 ≤ x ∧ x ≤ maxBits).length = F at *
  generalize lens.toList.length = n at *
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_false,
    Bool.true_and, Nat.ble_eq, Nat.beq_eq, maxBits]
  simp only [decide_eq_true_iff, Nat.reducePow, Nat.reduceSub] at *
  by_cases e : c0 + c1 = n
  · have := h01 e
    omega
  · have : F ≠ 0 := fun hz => e (hF hz)
    omega

/-- puff accepts the code length code (construct() must return 0: complete or
empty) exactly when the spec does and zlib does. -/
theorem puff_cl_ok (lens : Lens) :
    (notOversub lens && zlibOk lens true) =
      (Nat.beq (kr (blCount lens) maxBits) 32768 || Nat.beq (blCount lens 0) lens.size) := by
  have h0K : lens.toList.count 0 = lens.toList.length → kraftL lens.toList = 0 := by
    intro h
    have hc := count01_le lens.toList
    rw [kraftL_le1 _ ((count01 _).mpr (by omega))]
    have : lens.toList.count 1 = 0 := by omega
    rw [this]
  rw [← kraft_eq_kr, notOversub_ble]
  unfold zlibOk complete
  rw [zlibOk_all0, kraft_eq_kraftL]
  unfold blCount
  have hsize : lens.size = lens.toList.length := by simp
  rw [hsize]
  generalize kraftL lens.toList = K at *
  generalize lens.toList.count 0 = c0 at *
  generalize lens.toList.length = n at *
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_true,
    Bool.false_and, Bool.or_false, Nat.beq_eq, maxBits]
  simp only [decide_eq_true_iff, Nat.reducePow, Nat.ble_eq] at *
  by_cases e : c0 = n
  · have := h0K e
    omega
  · omega

/-! ## Bits -/

theorem getbits_eq (b : Bits) (p n : Nat) :
    getbits b p n = bif Nat.ble (p + n) b.size then some (lsbVal b p n) else none := by
  unfold getbits
  cases h : Nat.ble (p + n) b.size
  · rw [if_neg (fun h' => by rw [Nat.ble_eq_true_of_le h'] at h; cases h)]; rfl
  · rw [if_pos (Nat.le_of_ble_eq_true h)]; rfl

theorem lsbVal_zero (b : Bits) (p : Nat) : lsbVal b p 0 = 0 := rfl
theorem lsbVal_succ (b : Bits) (p n : Nat) :
    lsbVal b p (n + 1) = (bif b.getD p false then 1 else 0) + 2 * lsbVal b (p + 1) n := by
  rw [lsbVal]; cases b.getD p false <;> rfl

theorem bitsOf_size (bytes : Array UInt8) : (bitsOf bytes).size = bytes.size * 8 := by
  simp [bitsOf]

theorem bitsOf_getD (bytes : Array UInt8) (q : Nat) :
    (bitsOf bytes).getD q false =
      bif Nat.blt q (bytes.size * 8) then byteBit (fun i => (bytes.getD i 0).toNat) q else false := by
  cases h : Nat.blt q (bytes.size * 8)
  · have : ¬ q < (bitsOf bytes).size := by
      rw [bitsOf_size]; exact fun h' => by rw [blt_of_lt h'] at h; cases h
    simp [Array.getD, this]
  · rw [Puff.bitsOf_getD bytes q (by rw [bitsOf_size]; exact Deflate.Puff.Export.blt_true h)]; rfl

/-! ## Arrays and lists -/

theorem push_mk {α : Type} (l : List α) (x : α) : (Array.mk l).push x = Array.mk (l ++ [x]) := by
  apply Array.ext'; simp
theorem append_mk {α : Type} (l l' : List α) : Array.mk l ++ Array.mk l' = Array.mk (l ++ l') := by
  simp
theorem replicate_mk {α : Type} (n : Nat) (x : α) :
    Array.replicate n x = Array.mk (List.replicate n x) := rfl
theorem setD_mk {α : Type} (l : List α) (i : Nat) (x : α) :
    (Array.mk l).set! i x = Array.mk (l.set i x) := by
  simp [Array.set!, Array.setIfInBounds]
  intro h; rw [List.set_eq_of_length_le h]
theorem extract_mk {α : Type} (l : List α) (a b : Nat) :
    (Array.mk l).extract a b = Array.mk ((l.drop a).take (b - a)) := by
  apply Array.ext'; simp [List.extract_eq_take_drop]
theorem back_mk {α : Type} (l : List α) : (Array.mk l).back? = l.getLast? := by
  simp
theorem mk_toList {α : Type} (a : Array α) : Array.mk a.toList = a := rfl

/-! ## The output copy -/

theorem lzCopy_zero (out : Array UInt8) (d : Nat) : lzCopy out d 0 = out := rfl
theorem lzCopy_succ (out : Array UInt8) (d n : Nat) :
    lzCopy out d (n + 1) = lzCopy (out.push (out.getD (out.size - d) 0)) d n := rfl

/-! ## One step of each part of the spec -/

theorem bif_and_eq {α : Type} (P Q : Prop) [Decidable P] [Decidable Q] (x y : α) :
    (if P ∧ Q then x else y) = (bif decide P && decide Q then x else y) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem dite_and_eq {α : Type} (P Q : Prop) [Decidable P] [Decidable Q] (x : P ∧ Q → α) (y : α) :
    (if h : P ∧ Q then x h else y) = (if h : P ∧ Q then x h else y) := rfl

theorem decide_lt_blt (a b : Nat) : decide (a < b) = Nat.blt a b := by
  cases h : Nat.blt a b
  · exact decide_eq_false (fun h' => by rw [blt_of_lt h'] at h; cases h)
  · exact decide_eq_true (Deflate.Puff.Export.blt_true h)

theorem decide_eq_beq (a b : Nat) : decide (a = b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · exact decide_eq_false (Nat.ne_of_beq_eq_false h)
  · exact decide_eq_true (Nat.eq_of_beq_eq_true h)

theorem inflateSyms_eq (lit dist : Array (Nat × Nat)) (b : Bits) (p : Nat) (out : Array UInt8) :
    inflateSyms lit dist b p out =
      match decodeSym lit b p with
      | none => none
      | some (s, p1) =>
        bif Nat.blt s 256 then
          (bif Nat.blt p p1 && Nat.ble p1 b.size then
            inflateSyms lit dist b p1 (out.push s.toUInt8) else none)
        else bif Nat.beq s 256 then some (out, p1)
        else match lenTable[s - 257]? with
          | none => none
          | some (base, extra) =>
            match getbits b p1 extra with
            | none => none
            | some e =>
              match decodeSym dist b (p1 + extra) with
              | none => none
              | some (ds, p3) =>
                match distTable[ds]? with
                | none => none
                | some (dbase, dextra) =>
                  match getbits b p3 dextra with
                  | none => none
                  | some e2 =>
                    bif Nat.ble (dbase + e2) out.size then
                      (bif Nat.blt p (p3 + dextra) && Nat.ble (p3 + dextra) b.size then
                        inflateSyms lit dist b (p3 + dextra) (lzCopy out (dbase + e2) (base + e))
                      else none)
                    else none := by
  rw [inflateSyms]
  rcases decodeSym lit b p with _ | ⟨s, p1⟩
  · rfl
  · simp only
    by_cases hs : s < 256
    · rw [if_pos hs, blt_of_lt hs, cond_true]
      by_cases hc : p < p1 ∧ p1 ≤ b.size
      · rw [dif_pos hc, blt_of_lt hc.1, Nat.ble_eq_true_of_le hc.2]; rfl
      · rw [dif_neg hc]
        cases h1 : Nat.blt p p1 <;> cases h2 : Nat.ble p1 b.size <;> try rfl
        exact absurd ⟨Deflate.Puff.Export.blt_true h1, Nat.le_of_ble_eq_true h2⟩ hc
    · rw [if_neg hs, blt_of_not_lt hs, cond_false]
      by_cases h256 : s = 256
      · rw [if_pos h256, h256]; rfl
      · rw [if_neg h256, beq_false_of_ne h256, cond_false]
        rcases lenTable[s - 257]? with _ | ⟨base, extra⟩
        · rfl
        · simp only [Option.bind_eq_bind, Option.bind]
          rcases getbits b p1 extra with _ | e
          · rfl
          · simp only
            rcases decodeSym dist b (p1 + extra) with _ | ⟨ds, p3⟩
            · rfl
            · simp only
              rcases distTable[ds]? with _ | ⟨dbase, dextra⟩
              · rfl
              · simp only
                rcases getbits b p3 dextra with _ | e2
                · rfl
                · simp only
                  by_cases hd : dbase + e2 ≤ out.size
                  · rw [if_pos hd, Nat.ble_eq_true_of_le hd, cond_true]
                    by_cases hc : p < p3 + dextra ∧ p3 + dextra ≤ b.size
                    · rw [dif_pos hc, blt_of_lt hc.1, Nat.ble_eq_true_of_le hc.2]; rfl
                    · rw [dif_neg hc]
                      cases h1 : Nat.blt p (p3 + dextra) <;>
                        cases h2 : Nat.ble (p3 + dextra) b.size <;> try rfl
                      exact absurd ⟨Deflate.Puff.Export.blt_true h1, Nat.le_of_ble_eq_true h2⟩ hc
                  · rw [if_neg hd, ble_false_of_lt (by omega), cond_false]

/-- The bytes of a stored block, `n` of them from bit `q`. -/
def bytesAt (b : Bits) (q : Nat) : Nat → List UInt8
  | 0 => []
  | n + 1 => (lsbVal b q 8).toUInt8 :: bytesAt b (q + 8) n

theorem bytesAt_zero (b : Bits) (q : Nat) : bytesAt b q 0 = [] := rfl
theorem bytesAt_succ (b : Bits) (q n : Nat) :
    bytesAt b q (n + 1) = (lsbVal b q 8).toUInt8 :: bytesAt b (q + 8) n := rfl

theorem ofFn_bytesAt_list (b : Bits) : ∀ n q,
    List.ofFn (fun j : Fin n => (lsbVal b (q + 8 * j.val) 8).toUInt8) = bytesAt b q n
  | 0, _ => rfl
  | n + 1, q => by
    rw [List.ofFn_succ, bytesAt_succ]
    have e : (fun i : Fin n => (lsbVal b (q + 8 * (Fin.succ i).val) 8).toUInt8) =
        (fun i : Fin n => (lsbVal b (q + 8 + 8 * i.val) 8).toUInt8) := by
      funext i; rw [Fin.val_succ, show q + 8 * (i.val + 1) = q + 8 + 8 * i.val by omega]
    rw [e, ofFn_bytesAt_list b n (q + 8)]
    simp

theorem ofFn_bytesAt (b : Bits) (q n : Nat) :
    Array.ofFn (n := n) (fun j => (lsbVal b (q + 8 * j.val) 8).toUInt8) = Array.mk (bytesAt b q n) := by
  apply Array.ext'; rw [Array.toList_ofFn, ofFn_bytesAt_list]

theorem stored_eq (b : Bits) (p : Nat) :
    stored b p =
      match getbits b ((p + 7) / 8 * 8) 16 with
      | none => none
      | some len =>
        match getbits b ((p + 7) / 8 * 8 + 16) 16 with
        | none => none
        | some nlen =>
          bif Nat.beq (len + nlen) 65535 && Nat.ble ((p + 7) / 8 * 8 + 32 + 8 * len) b.size then
            some (Array.mk (bytesAt b ((p + 7) / 8 * 8 + 32) len), (p + 7) / 8 * 8 + 32 + 8 * len)
          else none := by
  unfold stored
  cases h1 : getbits b ((p + 7) / 8 * 8) 16 with
  | none => simp [h1]
  | some len =>
    cases h2 : getbits b ((p + 7) / 8 * 8 + 16) 16 with
    | none => simp [h1, h2]
    | some nlen =>
      simp only [h1, h2, Option.bind_eq_bind, Option.bind, guard, failure]
      by_cases c1 : len + nlen = 65535
      · by_cases c2 : (p + 7) / 8 * 8 + 32 + 8 * len ≤ b.size
        · simp [c1, c2, Nat.ble_eq_true_of_le c2, Nat.beq_refl, ofFn_bytesAt]
        · simp [c1, c2, InflateExport.ble_false_of_lt (show b.size < (p + 7) / 8 * 8 + 32 + 8 * len by omega), Nat.beq_refl]
      · simp [c1, InflateExport.beq_false_of_ne c1]

theorem readCL_def (b : Bits) (p hclen : Nat) :
    readCL b p hclen = readCL.go b p hclen 0 (Array.replicate 19 0) := rfl

theorem readCL_go_eq (b : Bits) (p hclen i : Nat) (acc : Lens) :
    readCL.go b p hclen i acc =
      bif Nat.blt i hclen then
        (match getbits b (p + 3 * i) 3 with
         | none => none
         | some v => readCL.go b p hclen (i + 1) (acc.set! (clOrder.getD i 0) v))
      else some (acc, p + 3 * hclen) := by
  rw [readCL.go]
  by_cases h : i < hclen
  · rw [if_pos h, blt_of_lt h, cond_true]
    simp only [Option.bind_eq_bind, Option.bind]
    rcases getbits b (p + 3 * i) 3 <;> rfl
  · rw [if_neg h, blt_of_not_lt h]; rfl

theorem readLens_eq (cl : Array (Nat × Nat)) (b : Bits) (p total : Nat) (acc : Lens) :
    readLens cl b p total acc =
      bif Nat.ble total acc.size then some (acc, p)
      else match decodeSym cl b p with
        | none => none
        | some (s, p1) =>
          bif Nat.blt s 16 then readLens cl b p1 total (acc.push s)
          else
            match getbits b p1 (bif Nat.beq s 16 then 2 else bif Nat.beq s 17 then 3 else 7) with
            | none => none
            | some e =>
              match (bif Nat.beq s 16 then acc.back? else some 0) with
              | none => none
              | some v =>
                bif Nat.ble (acc.size + ((bif Nat.beq s 18 then 11 else 3) + e)) total then
                  readLens cl b (p1 + (bif Nat.beq s 16 then 2 else bif Nat.beq s 17 then 3 else 7))
                    total (acc ++ Array.replicate ((bif Nat.beq s 18 then 11 else 3) + e) v)
                else none := by
  rw [readLens]
  by_cases ht : total ≤ acc.size
  · rw [dif_pos ht, Nat.ble_eq_true_of_le ht]; rfl
  · rw [dif_neg ht, InflateExport.ble_false_of_lt (by omega), cond_false]
    cases hd : decodeSym cl b p with
    | none => simp
    | some sp =>
      obtain ⟨s, p1⟩ := sp
      simp only
      by_cases h16 : s < 16
      · simp [h16, blt_of_lt h16]
      · rw [blt_of_not_lt h16, cond_false]
        simp only [h16, if_false, Option.bind_eq_bind, Option.bind]
        by_cases e16 : s = 16
        · subst e16
          cases hg : getbits b p1 2 with
          | none => simp [hg]
          | some e =>
            cases hb : acc.back? with
            | none => simp [hg, hb]
            | some v =>
              by_cases hr : acc.size + (3 + e) ≤ total
              · simp [hg, hb, hr, Nat.ble_eq_true_of_le hr]
              · simp [hg, hb, hr, InflateExport.ble_false_of_lt (show total < acc.size + (3 + e) by omega)]
        · by_cases e17 : s = 17
          · subst e17
            cases hg : getbits b p1 3 with
            | none => simp [hg]
            | some e =>
              by_cases hr : acc.size + (3 + e) ≤ total
              · simp [hg, hr, Nat.ble_eq_true_of_le hr]
              · simp [hg, hr, InflateExport.ble_false_of_lt (show total < acc.size + (3 + e) by omega)]
          · have b16 : Nat.beq s 16 = false := InflateExport.beq_false_of_ne e16
            have b17 : Nat.beq s 17 = false := InflateExport.beq_false_of_ne e17
            by_cases e18 : s = 18
            · subst e18
              cases hg : getbits b p1 7 with
              | none => simp [hg]
              | some e =>
                by_cases hr : acc.size + (11 + e) ≤ total
                · simp [hg, hr, Nat.ble_eq_true_of_le hr]
                · simp [hg, hr, InflateExport.ble_false_of_lt (show total < acc.size + (11 + e) by omega)]
            · have b18 : Nat.beq s 18 = false := InflateExport.beq_false_of_ne e18
              rw [b16, b17, b18]
              simp only [e16, e17, e18, if_false, cond_false]
              cases hg : getbits b p1 7 with
              | none => simp [hg]
              | some e =>
                by_cases hr : acc.size + (3 + e) ≤ total
                · simp [hg, hr, Nat.ble_eq_true_of_le hr]
                · simp [hg, hr, InflateExport.ble_false_of_lt (show total < acc.size + (3 + e) by omega)]

theorem dynHeader_eq (b : Bits) (p : Nat) :
    dynHeader b p =
      match getbits b p 5 with
      | none => none
      | some hlit =>
        match getbits b (p + 5) 5 with
        | none => none
        | some hdist =>
          match getbits b (p + 10) 4 with
          | none => none
          | some hclen =>
            bif Nat.ble (hlit + 257) 286 then
              match readCL b (p + 14) (hclen + 4) with
              | none => none
              | some (cl, q) =>
                bif notOversub cl then
                  match readLens (code cl) b q (hlit + 257 + (hdist + 1)) #[] with
                  | none => none
                  | some (lens, r) =>
                    bif !(Nat.beq ((lens.extract 0 (hlit + 257)).getD 256 0) 0) &&
                        (notOversub (lens.extract 0 (hlit + 257)) &&
                          notOversub (lens.extract (hlit + 257) (hlit + 257 + (hdist + 1)))) then
                      some (lens.extract 0 (hlit + 257), lens.extract (hlit + 257) (hlit + 257 + (hdist + 1)), r,
                        zlibOk cl true && zlibOk (lens.extract 0 (hlit + 257)) false &&
                          zlibOk (lens.extract (hlit + 257) (hlit + 257 + (hdist + 1))) false &&
                          Nat.ble (hdist + 1) 30)
                    else none
                else none
            else none := by
  unfold dynHeader
  simp only [Option.bind_eq_bind, Option.bind, guard, failure]
  cases h1 : getbits b p 5 with
  | none => rfl
  | some hlit =>
    cases h2 : getbits b (p + 5) 5 with
    | none => rfl
    | some hdist =>
      cases h3 : getbits b (p + 10) 4 with
      | none => rfl
      | some hclen =>
        simp only
        by_cases c1 : hlit + 257 ≤ 286
        · rw [if_pos c1, Nat.ble_eq_true_of_le c1, cond_true]
          cases h4 : readCL b (p + 14) (hclen + 4) with
          | none => rfl
          | some clq =>
            obtain ⟨cl, q⟩ := clq
            simp only
            cases hn : notOversub cl
            · simp
            · simp only [if_true, cond_true]
              cases h5 : readLens (code cl) b q (hlit + 257 + (hdist + 1)) #[] with
              | none => rfl
              | some lr =>
                obtain ⟨lens, r⟩ := lr
                simp only
                by_cases c2 : (lens.extract 0 (hlit + 257)).getD 256 0 ≠ 0
                · rw [if_pos c2, InflateExport.beq_false_of_ne c2]
                  simp only [Bool.not_false, Bool.true_and]
                  cases (notOversub (lens.extract 0 (hlit + 257)) &&
                      notOversub (lens.extract (hlit + 257) (hlit + 257 + (hdist + 1)))) <;>
                    simp [decide_le_ble] <;> rfl
                · rw [if_neg c2]
                  have : (lens.extract 0 (hlit + 257)).getD 256 0 = 0 := by omega
                  rw [this]; rfl
        · rw [if_neg c1, InflateExport.ble_false_of_lt (by omega)]; rfl

theorem block_eq (b : Bits) (p btype : Nat) (out : Array UInt8) :
    block b p btype out =
      bif Nat.beq btype 0 then
        (match stored b p with
         | none => none
         | some (bytes, q) => some (out ++ bytes, q, true))
      else bif Nat.beq btype 1 then
        (match inflateSyms (code fixedLit) (code fixedDist) b p out with
         | none => none
         | some (o, q) => some (o, q, true))
      else bif Nat.beq btype 2 then
        (match dynHeader b p with
         | none => none
         | some (lit, dist, q, z) =>
           match inflateSyms (code lit) (code dist) b q out with
           | none => none
           | some (o, r) => some (o, r, z))
      else none := by
  unfold block
  match btype with
  | 0 => simp only [Option.bind_eq_bind, Option.bind]; cases stored b p <;> rfl
  | 1 => simp only [Option.bind_eq_bind, Option.bind]; cases inflateSyms (code fixedLit) (code fixedDist) b p out <;> rfl
  | 2 =>
    simp only [Option.bind_eq_bind, Option.bind]
    cases dynHeader b p with
    | none => rfl
    | some x =>
      obtain ⟨lit, dist, q, z⟩ := x
      cases h : inflateSyms (code lit) (code dist) b q out <;> simp [h]
  | n + 3 => rfl

theorem inflateBlocks_eq (b : Bits) (p : Nat) (out : Array UInt8) (zl : Bool) :
    inflateBlocks b p out zl =
      match getbits b p 1 with
      | none => none
      | some bfinal =>
        match getbits b (p + 1) 2 with
        | none => none
        | some btype =>
          match block b (p + 3) btype out with
          | none => none
          | some (o, q, z) =>
            bif Nat.beq bfinal 1 then some (o, q, zl && z)
            else bif Nat.blt p q && Nat.ble q b.size then inflateBlocks b q o (zl && z)
            else none := by
  rw [inflateBlocks]
  simp only [Option.bind_eq_bind, Option.bind]
  cases h1 : getbits b p 1 with
  | none => rfl
  | some bfinal =>
    cases h2 : getbits b (p + 1) 2 with
    | none => rfl
    | some btype =>
      dsimp only
      cases h3 : block b (p + 3) btype out with
      | none => rfl
      | some x =>
        obtain ⟨o, q, z⟩ := x
        dsimp only
        by_cases e1 : bfinal = 1
        · subst e1; simp
        · rw [InflateExport.beq_false_of_ne e1, cond_false]
          simp only [e1, if_false]
          by_cases hc : p < q ∧ q ≤ b.size
          · rw [dif_pos hc, blt_of_lt hc.1, Nat.ble_eq_true_of_le hc.2]; rfl
          · rw [dif_neg hc]
            cases e2 : Nat.blt p q <;> cases e3 : Nat.ble q b.size <;> try rfl
            exact absurd ⟨Deflate.Puff.Export.blt_true e2, Nat.le_of_ble_eq_true e3⟩ hc

theorem zlibOk_eq (lens : Lens) (c : Bool) :
    zlibOk lens c =
      (Nat.beq (blCount lens 0) lens.size || Nat.beq (Puff.kr (blCount lens) maxBits) 32768 ||
        (!c && Nat.beq (blCount lens 1) 1 && Nat.beq (Puff.kr (blCount lens) maxBits) 16384)) := by
  unfold zlibOk complete
  rw [zlibOk_all0, Deflate.Puff.kraft_eq_kr]
  have e : ∀ a b : Nat, (a == b) = Nat.beq a b := fun a b => by
    cases h : Nat.beq a b
    · simp [Nat.ne_of_beq_eq_false h]
    · simp [Nat.eq_of_beq_eq_true h]
  simp only [e]; rfl

theorem fixedLit_size : fixedLit.size = 288 := by simp [fixedLit]

theorem fixedLit_getD (i : Nat) :
    fixedLit.getD i 0 =
      bif Nat.blt i 144 then 8 else bif Nat.blt i 256 then 9 else bif Nat.blt i 280 then 7
      else bif Nat.blt i 288 then 8 else 0 := by
  unfold fixedLit
  by_cases h : i < 288
  · simp only [Array.getD, Array.size_ofFn, h, dite_true, Array.getElem_ofFn]
    by_cases a : i < 144
    · simp [a, blt_of_lt a]
    · by_cases b : i < 256
      · simp [a, b, blt_of_not_lt a, blt_of_lt b]
      · by_cases c : i < 280
        · simp [a, b, c, blt_of_not_lt a, blt_of_not_lt b, blt_of_lt c]
        · simp [a, b, c, blt_of_not_lt a, blt_of_not_lt b, blt_of_not_lt c, blt_of_lt h]
  · simp only [Array.getD, Array.size_ofFn, h, dite_false]
    simp [blt_of_not_lt h, blt_of_not_lt (show ¬ i < 144 by omega), blt_of_not_lt (show ¬ i < 256 by omega),
      blt_of_not_lt (show ¬ i < 280 by omega)]

theorem fixedDist_eq : fixedDist = Array.mk (List.replicate 32 5) := rfl

/-! ## The fixed distance code

The spec's fixed distance code has 32 symbols (`fixedDist`); puff builds it
with 30. Symbols 30 and 31 mean nothing (`distTable`), so where the spec
decodes them and then fails, puff fails to decode. The two codes agree on
every other symbol: -/

theorem codeOf_rep5 (k n : Nat) (hn : n < k) : codeOf (Array.replicate k 5) n = n := by
  unfold codeOf
  have hg : (Array.replicate k 5).getD n 0 = 5 := by simp [Array.getD, hn]
  rw [hg]
  have hnc : nextCode (Array.replicate k 5) 5 = 0 := by
    have hb : ∀ l, 1 ≤ l → l < 5 → blCount (Array.replicate k 5) l = 0 := by
      intro l h1 h2; simp [blCount, List.count_replicate]; omega
    simp only [nextCode, hb 1 (by omega) (by omega), hb 2 (by omega) (by omega),
      hb 3 (by omega) (by omega), hb 4 (by omega) (by omega)]
  dsimp only
  rw [hnc, Nat.zero_add]
  simp [List.take_replicate, List.count_replicate]; omega

theorem decodeSym_dist30 (b : Bits) (p : Nat) :
    decodeSym (code (Array.replicate 30 5)) b p =
      match decodeSym (code fixedDist) b p with
      | none => none
      | some (ds, q) => bif Nat.blt ds 30 then some (ds, q) else none := by
  apply Option.ext
  intro ⟨s, q⟩
  rw [decodeSym_code_iff]
  simp only [Array.getElem_replicate]
  constructor
  · rintro ⟨hs, h1, h15, rfl, hb, hc⟩
    have hs' : s < 30 := by simpa using hs
    have h32 : decodeSym (code fixedDist) b p = some (s, p + 5) := by
      rw [decodeSym_code_iff]
      refine ⟨by simp [fixedDist]; omega, by simp [fixedDist], by simp [fixedDist, maxBits], ?_, ?_, ?_⟩
      · simp [fixedDist]
      · simpa [fixedDist] using hb
      · have e1 := codeOf_rep5 30 s hs'
        have e2 := codeOf_rep5 32 s (by omega)
        simp only [fixedDist] at *
        rw [e2]; rw [e1] at hc; simpa using hc
    rw [h32]; simp [blt_of_lt hs']
  · intro h
    cases h32 : decodeSym (code fixedDist) b p with
    | none => rw [h32] at h; cases h
    | some x =>
      obtain ⟨ds, q'⟩ := x
      rw [h32] at h
      simp only at h
      by_cases hds : ds < 30
      · rw [blt_of_lt hds] at h
        simp only [cond_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hs, h1, h15, hq, hb, hc⟩ := (decodeSym_code_iff _ _ _ _ _).mp h32
        refine ⟨by simpa using hds, by simp, by simp [maxBits], ?_, ?_, ?_⟩
        · simpa [fixedDist] using hq
        · simpa [fixedDist] using hb
        · have e1 := codeOf_rep5 30 ds hds
          have e2 := codeOf_rep5 32 ds (by omega)
          simp only [fixedDist] at *
          rw [e1]; rw [e2] at hc; simpa using hc
      · rw [blt_of_not_lt hds] at h; cases h

theorem inflate_def (b : Bits) :
    inflate b = match inflateBlocks b 0 #[] true with
      | none => none
      | some (out, bits, zlib) => some { out, bits, zlib } := by
  unfold inflate; simp only [Option.bind_eq_bind, Option.bind]
  cases inflateBlocks b 0 #[] true <;> rfl

theorem inflateBytes_def (bytes : Array UInt8) : inflateBytes bytes = inflate (bitsOf bytes) := rfl

/-- A decoded symbol is one of the alphabet's, and its code takes at least one
bit, all within the stream. -/
theorem decodeSym_bounds (lens : Lens) (b : Bits) (p s q : Nat)
    (h : decodeSym (code lens) b p = some (s, q)) :
    (Nat.blt p q && Nat.ble q b.size && Nat.blt s lens.size) = true := by
  obtain ⟨hs, h1, _, rfl, hb, _⟩ := (decodeSym_code_iff lens b p s q).mp h
  simp only [Bool.and_eq_true]
  exact ⟨⟨blt_of_lt (by omega), Nat.ble_eq_true_of_le hb⟩, blt_of_lt hs⟩

end Deflate.InflateExport
