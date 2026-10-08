import Lspec.Deflate.Puff

/-!
# What `vpuff/` imports into Rocq

`vpuff/` imports the spec and the puff model into Rocq with rocq-lean-import.
Lean's theorems arrive there as axioms (their statements, which Lean has
proved), so this file states the facts the Rocq proofs need in the form that
is easiest to use there:

* equations between computable values only. A Lean `Prop` becomes an `SProp`
  in Rocq, and of the `SProp`s only equality can be turned back into an
  ordinary proposition;
* conditions as `Bool` (`bif`, `Nat.ble`, `Nat.blt`, `Nat.beq`) rather than
  decidable `Prop`s, so Rocq can case on them;
* one unfolding equation per recursive definition, so Rocq never has to
  reduce Lean's compiled recursors.

`vpuff/export.sh` lists the declarations to export; keep the two in step.
-/

namespace Deflate.Puff.Export

/-! ## Natural numbers -/

theorem ble_true (n m : Nat) (h : n ≤ m) : Nat.ble n m = true := Nat.ble_eq_true_of_le h
theorem le_of_ble (n m : Nat) (h : Nat.ble n m = true) : n ≤ m := Nat.le_of_ble_eq_true h

theorem blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h
theorem blt_false {a b : Nat} (h : Nat.blt a b = false) : ¬ a < b := fun h' => by
  have : Nat.ble (a + 1) b = true := Nat.ble_eq_true_of_le h'
  rw [show Nat.blt a b = Nat.ble (a + 1) b from rfl, this] at h; cases h

theorem div_add_mod (a b : Nat) : b * (a / b) + a % b = a := Nat.div_add_mod a b
theorem mod_lt (a b : Nat) (h : Nat.ble 1 b = true) : Nat.ble (a % b + 1) b = true :=
  Nat.ble_eq_true_of_le (Nat.mod_lt a (Nat.le_of_ble_eq_true h))

theorem testBit_eq (x i : Nat) : x.testBit i = Nat.beq (x / 2 ^ i % 2) 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  cases h : Nat.beq (x / 2 ^ i % 2) 1
  · have := Nat.ne_of_beq_eq_false h; simp [this]
  · have := Nat.eq_of_beq_eq_true h; simp [this]

theorem uint8_toNat_ofNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  simp

theorem uint8_toNat_zero : (0 : UInt8).toNat = 0 := rfl

/-! ## Arrays -/

/-- `List.getD` by plain recursion. (`List.getD` itself goes through the list
`GetElem?` instance, whose `getElem!` panics with a message, and that brings
Lean's strings into the export.) -/
def lgetD {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | x :: _, 0, _ => x
  | _ :: l, i + 1, d => lgetD l i d

theorem getD_mk {α : Type} (l : List α) (i : Nat) (d : α) :
    (Array.mk l).getD i d = lgetD l i d := by
  induction l generalizing i with
  | nil => simp [Array.getD, lgetD]
  | cons x l ih =>
    cases i with
    | zero => simp [Array.getD, lgetD]
    | succ i => rw [lgetD, ← ih]; simp [Array.getD]

theorem lgetD_nil {α : Type} (i : Nat) (d : α) : lgetD ([] : List α) i d = d := by
  cases i <;> rfl
theorem lgetD_zero {α : Type} (x : α) (l : List α) (d : α) : lgetD (x :: l) 0 d = x := rfl
theorem lgetD_succ {α : Type} (x : α) (l : List α) (i : Nat) (d : α) :
    lgetD (x :: l) (i + 1) d = lgetD l i d := rfl

theorem size_mk {α : Type} (l : List α) : (Array.mk l).size = l.length := rfl

/-! ## The spec's verdict on lengths -/

theorem notOversub_eq (lens : Lens) :
    notOversub lens = Nat.ble (kr (blCount lens) maxBits) 32768 := by
  rw [notOversub, ← kraft_eq_kr, show (2 : Nat) ^ maxBits = 32768 from rfl]
  cases h : Nat.ble (kraft lens) 32768
  · have : ¬ kraft lens ≤ 32768 := fun h' => by
      rw [Nat.ble_eq_true_of_le h'] at h; cases h
    simp [this]
  · simp [Nat.le_of_ble_eq_true h]

/-! ## Unfolding the model -/

theorem cnt_zero (len : Nat → Nat) (l : Nat) : cnt len 0 l = 0 := rfl
theorem cnt_succ (len : Nat → Nat) (n l : Nat) :
    cnt len (n + 1) l = cnt len n l + (bif Nat.beq (len n) l then 1 else 0) := by
  rw [cnt]; cases h : Nat.beq (len n) l
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

theorem offs_zero (count : Nat → Nat) : offs count 0 = 0 := rfl
theorem offs_one (count : Nat → Nat) : offs count 1 = 0 := rfl
theorem offs_succ (count : Nat → Nat) (l : Nat) :
    offs count (l + 2) = offs count (l + 1) + count (l + 1) := rfl

theorem kr_zero (count : Nat → Nat) : kr count 0 = 0 := rfl
theorem kr_succ (count : Nat → Nat) (L : Nat) : kr count (L + 1) = 2 * kr count L + count (L + 1) := rfl

theorem go_zero (count symbol : Nat → Nat) (bit : Nat → Bool) (nbits p len cd first index : Nat) :
    go count symbol bit nbits p 0 len cd first index = none := rfl

theorem go_succ (count symbol : Nat → Nat) (bit : Nat → Bool) (nbits p k len cd first index : Nat) :
    go count symbol bit nbits p (k + 1) len cd first index =
      bif Nat.blt nbits (p + len) then none
      else bif Nat.blt (cd + (bif bit (p + len - 1) then 1 else 0)) (first + count len) then
        some (symbol (index + (cd + (bif bit (p + len - 1) then 1 else 0) - first)), p + len)
      else go count symbol bit nbits p k (len + 1)
        (2 * (cd + (bif bit (p + len - 1) then 1 else 0))) (2 * (first + count len))
        (index + count len) := by
  rw [go]
  have hb : (if bit (p + len - 1) then 1 else 0) = (bif bit (p + len - 1) then 1 else 0) := by
    cases bit (p + len - 1) <;> rfl
  simp only [hb]
  cases h1 : Nat.blt nbits (p + len)
  · rw [if_neg (blt_false h1), cond_false]
    cases h2 : Nat.blt (cd + (bif bit (p + len - 1) then 1 else 0)) (first + count len)
    · rw [if_neg (blt_false h2), cond_false]
    · rw [if_pos (blt_true h2), cond_true]
  · rw [if_pos (blt_true h1), cond_true]

theorem decode_def (count symbol : Nat → Nat) (bit : Nat → Bool) (nbits p : Nat) :
    decode count symbol bit nbits p = go count symbol bit nbits p 15 1 0 0 0 := rfl

theorem byteBit_def (byte : Nat → Nat) (q : Nat) : byteBit byte q = (byte (q / 8)).testBit (q % 8) := rfl

end Deflate.Puff.Export
