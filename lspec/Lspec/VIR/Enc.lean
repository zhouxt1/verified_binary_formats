import Lspec.VIR.Sem

/-!
# Shallow values in the VIR semantics

`enc τ x` is the VIR value of a Lean value `x : τ.denote`, and `Oracle.ofUnspec u` is the
oracle whose unspecified values are those of a shallow-model `u`. The lemmas below say how
each VIR node evaluates when its parts evaluate to encodings of shallow values. The
per-function validation proofs (generated) are built from them. Nothing here is trusted.
-/

namespace VIR

open VModel (IntRange VTy Unspec)

mutual
def enc : (τ : VTy) → τ.denote → Val
  | .int _, x => .int x
  | .bool, b => .bool b
  | .seq t, xs => .seq (xs.map (enc t))
  | .opt t, o => .opt (o.map (enc t))
  | .tup ts, x => .tup (encTup ts x)
def encTup : (ts : List VTy) → VTy.denoteTup ts → List Val
  | [], _ => []
  | [t], x => [enc t x]
  | t :: t2 :: ts, x => enc t x.1 :: encTup (t2 :: ts) x.2
end

/-- The oracle of a shallow-model `Unspec`. -/
def Oracle.ofUnspec (u : Unspec) : Oracle where
  arb τ := enc τ (u.arb τ)
  clip := u.clip
  div0 := u.div0
  mod0 := u.mod0

mutual
theorem enc_inj : ∀ (τ : VTy) (x y : τ.denote), enc τ x = enc τ y → x = y
  | .int _, x, y, h => by simp only [enc] at h; injection h
  | .bool, x, y, h => by simp only [enc] at h; injection h
  | .seq t, xs, ys, h => by
    simp only [enc] at h
    injection h with h
    induction xs generalizing ys with
    | nil => cases ys <;> simp_all
    | cons a as ih =>
      cases ys with
      | nil => simp at h
      | cons b bs =>
        simp only [List.map_cons, List.cons.injEq] at h
        rw [enc_inj t a b h.1, ih bs h.2]
  | .opt t, x, y, h => by
    simp only [enc] at h
    injection h with h
    cases x <;> cases y <;> simp at h ⊢
    exact enc_inj t _ _ h
  | .tup ts, x, y, h => by
    simp only [enc] at h
    injection h with h
    exact encTup_inj ts x y h
theorem encTup_inj : ∀ (ts : List VTy) (x y : VTy.denoteTup ts), encTup ts x = encTup ts y → x = y
  | [], x, y, _ => rfl
  | [t], x, y, h => by simp only [encTup] at h; injection h with h; exact enc_inj t x y h
  | t :: t2 :: ts, x, y, h => by
    simp only [encTup] at h
    injection h with h1 h2
    exact Prod.ext (enc_inj t _ _ h1) (encTup_inj (t2 :: ts) _ _ h2)
end

/-! ## Types of encodings -/

mutual
theorem hasTy_enc : ∀ (τ : VTy) (y : τ.denote), HasTy τ (enc τ y) ↔ VTy.wt τ y
  | .int _, y => by simp [enc, HasTy, VTy.wt]
  | .bool, y => by simp [enc, HasTy, VTy.wt]
  | .seq t, ys => by
    simp only [enc, HasTy, VTy.wt, List.mem_map]
    exact ⟨fun h y hy => (hasTy_enc t y).1 (h _ ⟨y, hy, rfl⟩),
      fun h v ⟨y, hy, e⟩ => e ▸ (hasTy_enc t y).2 (h y hy)⟩
  | .opt t, o => by
    cases o with
    | none => simp [enc, HasTy, VTy.wt]
    | some y => simp only [enc, Option.map_some, HasTy, VTy.wt, Option.mem_def, Option.some.injEq,
        forall_eq']; exact hasTy_enc t y
  | .tup ts, y => by simp only [enc, HasTy, VTy.wt]; exact hasTys_encTup ts y
theorem hasTys_encTup : ∀ (ts : List VTy) (y : VTy.denoteTup ts), HasTys ts (encTup ts y) ↔ VTy.wtTup ts y
  | [], _ => by simp [encTup, HasTys, VTy.wtTup]
  | [t], y => by simp only [encTup, HasTys, VTy.wtTup, and_true]; exact hasTy_enc t y
  | t :: t2 :: ts, y => by
    simp only [encTup, HasTys, VTy.wtTup]
    exact and_congr (hasTy_enc t y.1) (hasTys_encTup (t2 :: ts) y.2)
end

mutual
theorem enc_surj : ∀ (τ : VTy) (v : Val), HasTy τ v → ∃ y : τ.denote, enc τ y = v
  | .int _, .int i, _ => ⟨i, rfl⟩
  | .bool, .bool b, _ => ⟨b, rfl⟩
  | .seq t, .seq vs, h => by
    induction vs with
    | nil => exact ⟨[], rfl⟩
    | cons v vs ih =>
      simp only [HasTy, List.mem_cons, forall_eq_or_imp] at h
      obtain ⟨y, hy⟩ := enc_surj t v h.1
      obtain ⟨ys, hys⟩ := ih h.2
      refine ⟨y :: ys, ?_⟩
      simp only [enc, Val.seq.injEq] at hys ⊢
      simp [hy, hys]
  | .opt _, .opt none, _ => ⟨none, rfl⟩
  | .opt t, .opt (some v), h => by
    obtain ⟨y, hy⟩ := enc_surj t v h
    exact ⟨some y, by simp [enc, hy]⟩
  | .tup ts, .tup vs, h => by
    obtain ⟨y, hy⟩ := encTup_surj ts vs h
    exact ⟨y, by simp [enc, hy]⟩
  | .int _, .bool _, h | .int _, .seq _, h | .int _, .opt _, h | .int _, .tup _, h
  | .int _, .clo _ _ _, h => by simp [HasTy] at h
  | .bool, .int _, h | .bool, .seq _, h | .bool, .opt _, h | .bool, .tup _, h
  | .bool, .clo _ _ _, h => by simp [HasTy] at h
  | .seq _, .int _, h | .seq _, .bool _, h | .seq _, .opt _, h | .seq _, .tup _, h
  | .seq _, .clo _ _ _, h => by simp [HasTy] at h
  | .opt _, .int _, h | .opt _, .bool _, h | .opt _, .seq _, h | .opt _, .tup _, h
  | .opt _, .clo _ _ _, h => by simp [HasTy] at h
  | .tup _, .int _, h | .tup _, .bool _, h | .tup _, .seq _, h | .tup _, .opt _, h
  | .tup _, .clo _ _ _, h => by simp [HasTy] at h
theorem encTup_surj : ∀ (ts : List VTy) (vs : List Val), HasTys ts vs →
    ∃ y : VTy.denoteTup ts, encTup ts y = vs
  | [], [], _ => ⟨(), rfl⟩
  | [t], [v], h => by
    obtain ⟨y, hy⟩ := enc_surj t v h.1
    exact ⟨y, by simp [encTup, hy]⟩
  | t :: t2 :: ts, v :: vs, h => by
    obtain ⟨y, hy⟩ := enc_surj t v h.1
    obtain ⟨z, hz⟩ := encTup_surj (t2 :: ts) vs h.2
    exact ⟨(y, z), by simp [encTup, hy, hz]⟩
  | [], _ :: _, h | _ :: _, [], h => by simp [HasTys] at h
  | [_], _ :: _ :: _, h => by simp [HasTys] at h
end

/-! ## `Seq` operations on encodings -/

namespace Seqs

open VModel.Seq

variable {α β : Type}

theorem len_map (f : α → β) (s : List α) : len (s.map f) = len s := by simp [len_eq]

theorem indexWith_map (f : α → β) (d : α) (s : List α) (i : Int) :
    indexWith (f d) (s.map f) i = f (indexWith d s i) := by
  induction s generalizing i with
  | nil => rfl
  | cons x t ih => simp only [List.map_cons, indexWith]; split <;> simp [ih]

theorem push_map (f : α → β) (s : List α) (a : α) : push (s.map f) (f a) = (push s a).map f := by
  simp [push_eq]

theorem add_map (f : α → β) (s t : List α) : add (s.map f) (t.map f) = (add s t).map f := by
  simp [add_eq]

theorem subrange_map (f : α → β) (s : List α) (i j : Int) :
    subrange (s.map f) i j = (subrange s i j).map f := by
  induction s generalizing i j with
  | nil => rfl
  | cons x t ih => simp only [List.map_cons, subrange]; split <;> (try split) <;> simp [ih]

theorem dropLast_map (f : α → β) (s : List α) : dropLast (s.map f) = (dropLast s).map f := by
  simp only [dropLast, subrange_map, len_map]

theorem updateWith_map (f : α → β) (d : List α) (s : List α) (i : Int) (a : α) :
    updateWith (d.map f) (s.map f) i (f a) = (updateWith d s i a).map f := by
  unfold updateWith
  rw [len_map]
  split
  · rfl
  · rename_i h
    clear h
    induction s generalizing i with
    | nil => rfl
    | cons x t ih => simp only [List.map_cons, updateWith.go]; split <;> simp [ih]

theorem newWith_map (f : α → β) (d : List α) (n : Int) (g : Int → α) :
    newWith (d.map f) n (fun i => f (g i)) = (newWith d n g).map f := by
  unfold newWith
  split
  · rfl
  · generalize n.toNat = m
    induction m with
    | zero => rfl
    | succ m ih => simp [newWith.go, ih, push_eq]

end Seqs

end VIR
