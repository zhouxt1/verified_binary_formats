import Lspec.Deflate.Theorems

/-!
# The "not reached" guards

The spec's recursions carry guards such as `p < p1 ∧ p1 ≤ b.size` that exist
only so that their measures are evident. These theorems show the guards hold
whenever they are tested, so they never change a verdict.
-/

namespace Deflate

theorem getbits_some {b : Bits} {p n v : Nat} (h : getbits b p n = some v) :
    p + n ≤ b.size ∧ v = lsbVal b p n := by
  unfold getbits at h
  split at h
  · simp at h; exact ⟨by omega, h.symm⟩
  · simp at h

/-- A compressed block's symbols end after they start, inside the stream. -/
theorem inflateSyms_bounds (lit dist : Array (Nat × Nat)) (b : Bits) (p : Nat) (out : Array UInt8) :
    ∀ o q, inflateSyms lit dist b p out = some (o, q) → p < q ∧ q ≤ b.size := by
  induction p, out using inflateSyms.induct lit b with
  | case1 p out hd =>
    intro o q h; rw [inflateSyms.eq_1] at h; simp [hd] at h
  | case2 p out s p1 hd hs hg ih =>
    intro o q h; rw [inflateSyms.eq_1] at h; simp [hd, hs, hg] at h
    have := ih o q h; omega
  | case3 p out s p1 hd hs hg =>
    intro o q h; rw [inflateSyms.eq_1] at h; simp [hd, hs, hg] at h
  | case4 p out p1 hd =>
    intro o q h; rw [inflateSyms.eq_1] at h; simp [hd] at h
    obtain ⟨-, rfl⟩ := h
    have := decodeSym_spec hd; omega
  | case5 p out s p1 hd hs h256 ih =>
    intro o q h
    rw [inflateSyms.eq_1] at h
    simp only [hd, hs, h256, ite_false] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨base, extra⟩, -, h⟩ := h
    obtain ⟨e, -, h⟩ := h
    obtain ⟨⟨ds, p3⟩, -, h⟩ := h
    obtain ⟨⟨dbase, dextra⟩, -, h⟩ := h
    obtain ⟨e2, -, h⟩ := h
    split at h
    · split at h
      · exact (fun ⟨a, b⟩ => ⟨by omega, b⟩) (ih base e p3 dbase dextra e2 ‹_› o q h)
      · simp at h
    · simp at h

/-- A literal's guard: a symbol's code is at least one bit, inside the
stream. -/
theorem guard_literal {lit : Array (Nat × Nat)} {b : Bits} {p s p1 : Nat}
    (h : decodeSym lit b p = some (s, p1)) : p < p1 ∧ p1 ≤ b.size :=
  (decodeSym_spec h).2

/-- A length/distance pair's guard: its extra bits were read, so they are
inside the stream, and they end after the pair's lit/length code began. -/
theorem guard_pair {lit dist : Array (Nat × Nat)} {b : Bits} {p s p1 extra ds p3 dextra e2 : Nat}
    (h1 : decodeSym lit b p = some (s, p1)) (h2 : decodeSym dist b (p1 + extra) = some (ds, p3))
    (h3 : getbits b p3 dextra = some e2) : p < p3 + dextra ∧ p3 + dextra ≤ b.size := by
  have := decodeSym_spec h1
  have := decodeSym_spec h2
  have := getbits_some h3
  omega

theorem guard_some {c : Prop} [Decidable c] {u : Unit} : (guard c : Option Unit) = some u ↔ c := by
  unfold guard; split <;> simp_all <;> rfl

theorem stored_bounds {b : Bits} {p : Nat} {bytes : Array UInt8} {q : Nat}
    (h : stored b p = some (bytes, q)) : p < q ∧ q ≤ b.size := by
  unfold stored at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨len, -, nlen, -, u, -, u2, hg, h⟩ := h
  rw [guard_some] at hg
  simp at h
  obtain ⟨-, rfl⟩ := h
  constructor <;> omega

theorem readCL_go_pos (b : Bits) (p hclen : Nat) :
    ∀ i acc cl q, readCL.go b p hclen i acc = some (cl, q) → q = p + 3 * hclen := by
  intro i acc
  induction i, acc using readCL.go.induct hclen with
  | case1 i acc hi ih =>
    intro cl q h
    rw [readCL.go] at h
    simp only [hi, ite_true, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, -, h⟩ := h
    exact ih v cl q h
  | case2 i acc hi =>
    intro cl q h
    rw [readCL.go] at h
    simp [hi] at h
    exact h.2.symm

theorem readLens_ge (cl : Array (Nat × Nat)) (b : Bits) (total : Nat) :
    ∀ p acc lens r, readLens cl b p total acc = some (lens, r) → p ≤ r := by
  intro p acc
  induction p, acc using readLens.induct cl b total with
  | case1 p acc ht =>
    intro lens r h; rw [readLens] at h; simp [ht] at h; omega
  | case2 p acc ht hd =>
    intro lens r h; rw [readLens] at h; simp [ht, hd] at h
  | case3 p acc ht s p1 hd hs ih =>
    intro lens r h; rw [readLens] at h; simp [ht, hd, hs] at h
    have := ih lens r h; have := decodeSym_spec hd; omega
  | case4 p acc ht s p1 hd hs nb base ih =>
    intro lens r h
    have := decodeSym_spec hd
    rw [readLens] at h
    simp only [ht, hd, hs, dite_false, ite_false, Option.bind_eq_bind] at h
    rw [Option.bind_eq_some_iff] at h
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
      · have := ih e v lens r h; omega
      · simp at h

theorem dynHeader_ge {b : Bits} {p : Nat} {lit dist : Lens} {q : Nat} {z : Bool}
    (h : dynHeader b p = some (lit, dist, q, z)) : p ≤ q := by
  unfold dynHeader at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨hlit, -, hdist, -, hclen, -, u, -, ⟨cl, q1⟩, hcl, u2, -, ⟨lens, r⟩, hl, h⟩ := h
  have h1 := readCL_go_pos b (p + 14) (hclen + 4) _ _ _ _ hcl
  have h2 := readLens_ge _ _ _ _ _ _ _ hl
  obtain ⟨_, -, _, -, h⟩ := h
  simp at h h2
  omega

theorem block_bounds {b : Bits} {p t : Nat} {out o : Array UInt8} {q : Nat} {z : Bool}
    (h : block b p t out = some (o, q, z)) : p < q ∧ q ≤ b.size := by
  unfold block at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨bytes, q'⟩, hs, h⟩ := h
    simp at h; obtain ⟨-, rfl, -⟩ := h
    exact stored_bounds hs
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨o', q'⟩, hs, h⟩ := h
    simp at h; obtain ⟨-, rfl, -⟩ := h
    exact inflateSyms_bounds _ _ _ _ _ _ _ hs
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨lit, dist, q', zl⟩, hd, h⟩ := h
    obtain ⟨⟨o', r⟩, hs, h⟩ := h
    simp at h; obtain ⟨-, rfl, -⟩ := h
    have h3 := inflateSyms_bounds _ _ _ _ _ _ _ hs
    have h4 := dynHeader_ge hd
    simp only at h3 h4 ⊢
    omega
  · simp at h

/-- The guard between blocks: a block, header included, ends after it starts,
inside the stream. -/
theorem guard_blocks {b : Bits} {p t : Nat} {out o : Array UInt8} {q : Nat} {z : Bool}
    (h : block b (p + 3) t out = some (o, q, z)) : p < q ∧ q ≤ b.size := by
  have := block_bounds h; omega

end Deflate
