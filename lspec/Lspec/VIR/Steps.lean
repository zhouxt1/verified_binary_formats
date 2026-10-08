import Lspec.VIR.Enc

/-!
# One lemma per VIR node

Each lemma says what a node evaluates to when its parts evaluate to encodings of shallow
values: the shallow model's meaning of the node, encoded. Validation proofs (generated, see
`vir2lean.py --validate`) chain them along a function's body. Not trusted.
-/

namespace VIR

open VModel (IntRange VTy Unspec)

/-- Pointwise relation of two lists. -/
inductive All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : All2 R [] []
  | cons {a b as bs} : R a b → All2 R as bs → All2 R (a :: as) (b :: bs)

variable {P : Prog} {u : Unspec} {ρ : Env}

local notation "𝒪" => Oracle.ofUnspec u

/-- Lists of evaluations, for a node's arguments. -/
theorem forall₂_eval {es : List Expr} {vs : List Val} (h : All2 (Eval P 𝒪 ρ) es vs) :
    vs.length = es.length ∧ ∀ k (hk : k < es.length), Eval P 𝒪 ρ es[k] vs[k]! := by
  induction h with
  | nil => simp
  | cons h1 _ ih =>
    refine ⟨by simp [ih.1], fun k hk => ?_⟩
    cases k with
    | zero => simpa using h1
    | succ k => simpa using ih.2 k (by simp at hk; omega)

theorem ev_int (i : Int) : Eval P 𝒪 ρ (.int i) (.int i) := Eval.int
theorem ev_bool (b : Bool) : Eval P 𝒪 ρ (.bool b) (enc .bool b) := Eval.bool
theorem ev_var {x : String} {v : Val} (h : ρ.lookup x = some v) : Eval P 𝒪 ρ (.var x) v := Eval.var h

theorem ev_lett {x : String} {init body : Expr} {v w : Val} (h1 : Eval P 𝒪 ρ init v)
    (h2 : Eval P 𝒪 ((x, v) :: ρ) body w) : Eval P 𝒪 ρ (.lett x init body) w := Eval.lett h1 h2

theorem ev_dite {c t e : Expr} {τ : VTy} {sc : Bool} {st : sc = true → τ.denote}
    {se : ¬sc = true → τ.denote} (hc : Eval P 𝒪 ρ c (.bool sc))
    (ht : ∀ h : sc = true, Eval P 𝒪 ρ t (enc τ (st h)))
    (he : ∀ h : ¬sc = true, Eval P 𝒪 ρ e (enc τ (se h))) :
    Eval P 𝒪 ρ (.ite c t e) (enc τ (if h : sc = true then st h else se h)) := by
  cases sc with
  | true => exact Eval.iteT hc (ht rfl)
  | false => exact Eval.iteF hc (he (by simp))

theorem ev_call {f : String} {args : List Expr} {vs : List Val} {v : Val}
    (h : All2 (Eval P 𝒪 ρ) args vs) (hr : RunsTo P 𝒪 f vs v) : Eval P 𝒪 ρ (.call f args) v := by
  obtain ⟨hl, hk⟩ := forall₂_eval h
  obtain ⟨d, hd, hp, hb | ⟨hi, rfl⟩⟩ := hr
  · exact Eval.call vs d hl hk hd hp hb.1 hb.2
  · exact Eval.callBad vs d hl hk hd hi

theorem runs_intro {f : String} {d : FnDef} {vs : List Val} {v : Val} (hf : P.find f = some d)
    (hl : d.params.length = vs.length)
    (hb : invOk d.params vs → Eval P 𝒪 ((d.params.map (·.1)).zip vs) d.body v)
    (ha : ¬invOk d.params vs → v = (Oracle.ofUnspec u).arb d.ret) : RunsTo P 𝒪 f vs v := by
  by_cases hi : invOk d.params vs
  · exact ⟨d, hf, hl, .inl ⟨hi, hb hi⟩⟩
  · exact ⟨d, hf, hl, .inr ⟨hi, ha hi⟩⟩

/-! ## `Seq` operations -/

theorem ev_prim {p : Prim} {t : VTy} {args : List Expr} {vs : List Val} {v : Val}
    (h : All2 (Eval P 𝒪 ρ) args vs) (hp : p ≠ .new) (hv : primVal 𝒪 p t vs = some v) :
    Eval P 𝒪 ρ (.prim p t args) v := by
  obtain ⟨hl, hk⟩ := forall₂_eval h
  exact Eval.prim vs hl hk hp hv

open VModel.Seq Seqs in
theorem ev_empty {t : VTy} : Eval P 𝒪 ρ (.prim .empty t []) (enc (.seq t) (VModel.Seq.empty)) :=
  ev_prim .nil (by decide) rfl

theorem ev_len {t : VTy} {a : Expr} {xs : List t.denote}
    (h : Eval P 𝒪 ρ a (enc (.seq t) xs)) :
    Eval P 𝒪 ρ (.prim .len t [a]) (.int (VModel.Seq.len xs)) :=
  ev_prim (.cons h .nil) (by decide) (by simp [primVal, enc, Seqs.len_map])

theorem ev_index {t : VTy} {a i : Expr} {xs : List t.denote} {j : Int}
    (ha : Eval P 𝒪 ρ a (enc (.seq t) xs)) (hi : Eval P 𝒪 ρ i (.int j)) :
    Eval P 𝒪 ρ (.prim .index t [a, i]) (enc t (VModel.Seq.index u t rfl xs j)) :=
  ev_prim (.cons ha (.cons hi .nil)) (by decide) (by
    simp only [primVal, enc, VModel.Seq.index, Oracle.ofUnspec, VModel.arbAt]
    rw [Seqs.indexWith_map])

theorem ev_last {t : VTy} {a : Expr} {xs : List t.denote} (ha : Eval P 𝒪 ρ a (enc (.seq t) xs)) :
    Eval P 𝒪 ρ (.prim .last t [a]) (enc t (VModel.Seq.last u t rfl xs)) :=
  ev_prim (.cons ha .nil) (by decide) (by
    simp only [primVal, enc, VModel.Seq.last, VModel.Seq.index, Oracle.ofUnspec, VModel.arbAt]
    rw [Seqs.len_map, Seqs.indexWith_map])

theorem ev_push {t : VTy} {a b : Expr} {xs : List t.denote} {x : t.denote}
    (ha : Eval P 𝒪 ρ a (enc (.seq t) xs)) (hb : Eval P 𝒪 ρ b (enc t x)) :
    Eval P 𝒪 ρ (.prim .push t [a, b]) (enc (.seq t) (VModel.Seq.push xs x)) :=
  ev_prim (.cons ha (.cons hb .nil)) (by decide) (by simp [primVal, enc, Seqs.push_map])

theorem ev_update {t : VTy} {a i b : Expr} {xs : List t.denote} {j : Int} {x : t.denote}
    (ha : Eval P 𝒪 ρ a (enc (.seq t) xs)) (hi : Eval P 𝒪 ρ i (.int j))
    (hb : Eval P 𝒪 ρ b (enc t x)) :
    Eval P 𝒪 ρ (.prim .update t [a, i, b]) (enc (.seq t) (VModel.Seq.update u t rfl xs j x)) :=
  ev_prim (.cons ha (.cons hi (.cons hb .nil))) (by decide) (by
    simp only [primVal, enc, VModel.Seq.update, Oracle.arbSeq, Oracle.ofUnspec, VModel.arbAt]
    rw [Seqs.updateWith_map])

theorem ev_subrange {t : VTy} {a i j : Expr} {xs : List t.denote} {i' j' : Int}
    (ha : Eval P 𝒪 ρ a (enc (.seq t) xs)) (hi : Eval P 𝒪 ρ i (.int i'))
    (hj : Eval P 𝒪 ρ j (.int j')) :
    Eval P 𝒪 ρ (.prim .subrange t [a, i, j]) (enc (.seq t) (VModel.Seq.subrange xs i' j')) :=
  ev_prim (.cons ha (.cons hi (.cons hj .nil))) (by decide) (by simp [primVal, enc, Seqs.subrange_map])

theorem ev_add {t : VTy} {a b : Expr} {xs ys : List t.denote}
    (ha : Eval P 𝒪 ρ a (enc (.seq t) xs)) (hb : Eval P 𝒪 ρ b (enc (.seq t) ys)) :
    Eval P 𝒪 ρ (.prim .add t [a, b]) (enc (.seq t) (VModel.Seq.add xs ys)) :=
  ev_prim (.cons ha (.cons hb .nil)) (by decide) (by simp [primVal, enc, Seqs.add_map])

theorem ev_dropLast {t : VTy} {a : Expr} {xs : List t.denote} (ha : Eval P 𝒪 ρ a (enc (.seq t) xs)) :
    Eval P 𝒪 ρ (.prim .dropLast t [a]) (enc (.seq t) (VModel.Seq.dropLast xs)) :=
  ev_prim (.cons ha .nil) (by decide) (by simp [primVal, enc, Seqs.dropLast_map])

theorem ev_skip {t : VTy} {a n : Expr} {xs : List t.denote} {n' : Int}
    (ha : Eval P 𝒪 ρ a (enc (.seq t) xs)) (hn : Eval P 𝒪 ρ n (.int n')) :
    Eval P 𝒪 ρ (.prim .skip t [a, n]) (enc (.seq t) (VModel.Seq.skip xs n')) :=
  ev_prim (.cons ha (.cons hn .nil)) (by decide) (by
    simp [primVal, enc, VModel.Seq.skip, Seqs.subrange_map, Seqs.len_map])

theorem ev_take {t : VTy} {a n : Expr} {xs : List t.denote} {n' : Int}
    (ha : Eval P 𝒪 ρ a (enc (.seq t) xs)) (hn : Eval P 𝒪 ρ n (.int n')) :
    Eval P 𝒪 ρ (.prim .take t [a, n]) (enc (.seq t) (VModel.Seq.take xs n')) :=
  ev_prim (.cons ha (.cons hn .nil)) (by decide) (by
    simp [primVal, enc, VModel.Seq.take, Seqs.subrange_map])

theorem newWith_go_get {α : Type} (f : Int → α) (m j : Nat)
    (h : j < (VModel.Seq.newWith.go f m).length) : (VModel.Seq.newWith.go f m)[j] = f j := by
  induction m generalizing j with
  | zero => simp [VModel.Seq.newWith.go] at h
  | succ m ih =>
    simp only [VModel.Seq.newWith.go, VModel.Seq.push_eq]
    rw [List.getElem_append]
    split
    · exact ih j _
    · rename_i h'
      rw [VModel.Seq.new_go_length] at h'
      simp only [VModel.Seq.push_eq, List.length_append, List.length_singleton,
        VModel.Seq.new_go_length] at h
      simp only [List.getElem_singleton]; congr; omega

theorem ev_new {t : VTy} {n body : Expr} {x : String} {k : Int} {g : Int → t.denote}
    (hn : Eval P 𝒪 ρ n (.int k))
    (hg : ∀ i : Int, Eval P 𝒪 ((x, .int i) :: ρ) body (enc t (g i))) :
    Eval P 𝒪 ρ (.prim .new t [n, .lam x body]) (enc (.seq t) (VModel.Seq.new u t rfl k g)) := by
  simp only [VModel.Seq.new, VModel.arbAt]
  rw [show enc (.seq t) (VModel.Seq.newWith (u.arb (.seq t)) k g) =
      .seq (VModel.Seq.newWith ((u.arb (.seq t)).map (enc t)) k (fun i => enc t (g i))) by
    simp only [enc]; rw [Seqs.newWith_map]]
  by_cases hk : k < 0
  · simp only [VModel.Seq.newWith, hk, if_true]
    have := Eval.newNeg (P := P) (O := 𝒪) (ρ := ρ) (t := t) (x := x) (body := body) hn hk
    simpa [Oracle.ofUnspec, enc] using this
  · simp only [VModel.Seq.newWith, hk, if_false]
    refine Eval.new _ hn (by omega) (VModel.Seq.new_go_length _ _) (fun j hj => ?_)
    have hj' : j < k.toNat := by rw [VModel.Seq.new_go_length] at hj; exact hj
    have e := newWith_go_get (fun i => enc t (g i)) k.toNat j hj
    rw [e]
    exact hg j

/-! ## Data -/

theorem ev_someField {t : VTy} {e : Expr} {o : Option t.denote} (h : Eval P 𝒪 ρ e (enc (.opt t) o)) :
    Eval P 𝒪 ρ (.someField e t) (enc t (VModel.someVal u t rfl o)) := by
  cases o with
  | none => exact Eval.someFieldNone h
  | some x => exact Eval.someFieldSome h

theorem ev_tupField {e : Expr} {i : Nat} {vs : List Val} {v : Val} (h : Eval P 𝒪 ρ e (.tup vs))
    (hv : vs[i]? = some v) : Eval P 𝒪 ρ (.tupField e i) v := Eval.tupField h hv

theorem ev_tuple {es : List Expr} {vs : List Val} (h : All2 (Eval P 𝒪 ρ) es vs) :
    Eval P 𝒪 ρ (.tuple es) (.tup vs) := by
  obtain ⟨hl, hk⟩ := forall₂_eval h
  exact Eval.tuple vs hl hk

theorem ev_some {t : VTy} {e : Expr} {x : t.denote} (h : Eval P 𝒪 ρ e (enc t x)) :
    Eval P 𝒪 ρ (.some e) (enc (.opt t) (some x)) := Eval.some h

theorem ev_none {t : VTy} : Eval P 𝒪 ρ .none (enc (.opt t) none) := Eval.none

theorem ev_isSome (t : VTy) {e : Expr} {o : Option t.denote} (h : Eval P 𝒪 ρ e (enc (.opt t) o)) :
    Eval P 𝒪 ρ (.isSome e) (enc .bool o.isSome) := by
  have := Eval.isSome h; cases o <;> simpa [enc] using this

theorem ev_isNone (t : VTy) {e : Expr} {o : Option t.denote} (h : Eval P 𝒪 ρ e (enc (.opt t) o)) :
    Eval P 𝒪 ρ (.isNone e) (enc .bool o.isNone) := by
  have := Eval.isNone h; cases o <;> simpa [enc] using this

theorem ev_isTuple {e : Expr} {v : Val} (h : Eval P 𝒪 ρ e v) : Eval P 𝒪 ρ (.isTuple e) (enc .bool true) :=
  Eval.isTuple h

/-! ## Quantifiers -/

open Classical in
/-- A body's meaning lifted from shallow values to VIR values: `f` at the value's preimage. -/
noncomputable def liftB (τ : VTy) (f : τ.denote → Bool) (v : Val) : Bool :=
  if h : ∃ y, enc τ y = v then f h.choose else false

theorem liftB_enc (τ : VTy) (f : τ.denote → Bool) (y : τ.denote) : liftB τ f (enc τ y) = f y := by
  have h : ∃ y', enc τ y' = enc τ y := ⟨y, rfl⟩
  simp only [liftB, h, dite_true]
  rw [enc_inj τ _ _ h.choose_spec]

open Classical in
theorem ev_exT (τ : VTy) {x : String} {body : Expr} (f : τ.denote → Bool)
    (h : ∀ y, Eval P 𝒪 ((x, enc τ y) :: ρ) body (enc .bool (f y))) :
    Eval P 𝒪 ρ (.ex x τ body) (enc .bool (decide (∃ y, VTy.wt τ y ∧ f y = true))) := by
  have e := Eval.ex (P := P) (O := 𝒪) (ρ := ρ) (t := τ) (x := x) (body := body) (liftB τ f)
    (fun v hv => by obtain ⟨y, rfl⟩ := enc_surj τ v hv; rw [liftB_enc]; exact h y)
  show Eval P 𝒪 ρ _ (.bool _)
  suffices hd : (∃ v, HasTy τ v ∧ liftB τ f v = true) ↔ ∃ y, VTy.wt τ y ∧ f y = true by
    rw [← decide_eq_decide.2 hd]; exact e
  constructor
  · rintro ⟨v, hv, hf⟩
    obtain ⟨y, rfl⟩ := enc_surj τ v hv
    exact ⟨y, (hasTy_enc τ y).1 hv, by rwa [liftB_enc] at hf⟩
  · rintro ⟨y, hy, hf⟩
    exact ⟨enc τ y, (hasTy_enc τ y).2 hy, by rwa [liftB_enc]⟩

open Classical in
theorem ev_allT (τ : VTy) {x : String} {body : Expr} (f : τ.denote → Bool)
    (h : ∀ y, Eval P 𝒪 ((x, enc τ y) :: ρ) body (enc .bool (f y))) :
    Eval P 𝒪 ρ (.all x τ body) (enc .bool (decide (∀ y, VTy.wt τ y → f y = true))) := by
  have e := Eval.all (P := P) (O := 𝒪) (ρ := ρ) (t := τ) (x := x) (body := body) (liftB τ f)
    (fun v hv => by obtain ⟨y, rfl⟩ := enc_surj τ v hv; rw [liftB_enc]; exact h y)
  show Eval P 𝒪 ρ _ (.bool _)
  suffices hd : (∀ v, HasTy τ v → liftB τ f v = true) ↔ ∀ y, VTy.wt τ y → f y = true by
    rw [← decide_eq_decide.2 hd]; exact e
  constructor
  · intro hall y hy
    have := hall (enc τ y) ((hasTy_enc τ y).2 hy)
    rwa [liftB_enc] at this
  · intro hall v hv
    obtain ⟨y, rfl⟩ := enc_surj τ v hv
    rw [liftB_enc]; exact hall y ((hasTy_enc τ y).1 hv)

open Classical in
theorem ev_ex {x : String} {body : Expr} (f : Int → Bool)
    (h : ∀ i : Int, Eval P 𝒪 ((x, .int i) :: ρ) body (enc .bool (f i))) :
    Eval P 𝒪 ρ (.ex x (.int .int) body) (enc .bool (decide (∃ i, f i = true))) := by
  have := ev_exT (.int .int) f h
  simpa [VTy.wt, IntRange.contains] using this

open Classical in
theorem ev_all {x : String} {body : Expr} (f : Int → Bool)
    (h : ∀ i : Int, Eval P 𝒪 ((x, .int i) :: ρ) body (enc .bool (f i))) :
    Eval P 𝒪 ρ (.all x (.int .int) body) (enc .bool (decide (∀ i, f i = true))) := by
  have := ev_allT (.int .int) f h
  simpa [VTy.wt, IntRange.contains] using this

/-! ## Operators -/

theorem ev_not {e : Expr} {b : Bool} (h : Eval P 𝒪 ρ e (enc .bool b)) :
    Eval P 𝒪 ρ (.un .not e) (enc .bool (!b)) := Eval.not h

theorem ev_clip {r : IntRange} {e : Expr} {i : Int} (h : Eval P 𝒪 ρ e (.int i)) :
    Eval P 𝒪 ρ (.un (.clip r) e) (.int (VModel.clip u r i)) := by
  have := Eval.clip (r := r) h
  simpa [VModel.clip, Oracle.ofUnspec, enc] using this

theorem ev_iadd {a b : Expr} {x y : Int}
    (ha : Eval P 𝒪 ρ a (.int x)) (hb : Eval P 𝒪 ρ b (.int y)) :
    Eval P 𝒪 ρ (.bin .add a b) (.int (x + y)) := Eval.bin ha hb rfl

theorem ev_isub {a b : Expr} {x y : Int}
    (ha : Eval P 𝒪 ρ a (.int x)) (hb : Eval P 𝒪 ρ b (.int y)) :
    Eval P 𝒪 ρ (.bin .sub a b) (.int (x - y)) := Eval.bin ha hb rfl

theorem ev_imul {a b : Expr} {x y : Int}
    (ha : Eval P 𝒪 ρ a (.int x)) (hb : Eval P 𝒪 ρ b (.int y)) :
    Eval P 𝒪 ρ (.bin .mul a b) (.int (x * y)) := Eval.bin ha hb rfl

theorem ev_ediv {a b : Expr} {x y : Int}
    (ha : Eval P 𝒪 ρ a (.int x)) (hb : Eval P 𝒪 ρ b (.int y)) :
    Eval P 𝒪 ρ (.bin .ediv a b) (.int (VModel.ediv u x y)) := Eval.bin ha hb rfl

theorem ev_emod {a b : Expr} {x y : Int}
    (ha : Eval P 𝒪 ρ a (.int x)) (hb : Eval P 𝒪 ρ b (.int y)) :
    Eval P 𝒪 ρ (.bin .emod a b) (.int (VModel.emod u x y)) := Eval.bin ha hb rfl

theorem ev_band {a b : Expr} {x y : Int}
    (ha : Eval P 𝒪 ρ a (.int x)) (hb : Eval P 𝒪 ρ b (.int y)) :
    Eval P 𝒪 ρ (.bin .band a b) (.int (VModel.band x y)) := Eval.bin ha hb rfl

theorem ev_shr {a b : Expr} {x y : Int}
    (ha : Eval P 𝒪 ρ a (.int x)) (hb : Eval P 𝒪 ρ b (.int y)) :
    Eval P 𝒪 ρ (.bin .shr a b) (.int (VModel.shr x y)) := Eval.bin ha hb rfl

theorem ev_bxor {a b : Expr} {x y : Int}
    (ha : Eval P 𝒪 ρ a (.int x)) (hb : Eval P 𝒪 ρ b (.int y)) :
    Eval P 𝒪 ρ (.bin .bxor a b) (.int (VModel.bxor x y)) := Eval.bin ha hb rfl

theorem ev_le {a b : Expr} {x y : Int}
    (ha : Eval P 𝒪 ρ a (.int x)) (hb : Eval P 𝒪 ρ b (.int y)) :
    Eval P 𝒪 ρ (.bin .le a b) (enc .bool (decide (x ≤ y))) := Eval.bin ha hb rfl

theorem ev_lt {a b : Expr} {x y : Int}
    (ha : Eval P 𝒪 ρ a (.int x)) (hb : Eval P 𝒪 ρ b (.int y)) :
    Eval P 𝒪 ρ (.bin .lt a b) (enc .bool (decide (x < y))) := Eval.bin ha hb rfl

theorem ev_ge {a b : Expr} {x y : Int}
    (ha : Eval P 𝒪 ρ a (.int x)) (hb : Eval P 𝒪 ρ b (.int y)) :
    Eval P 𝒪 ρ (.bin .ge a b) (enc .bool (decide (x ≥ y))) := Eval.bin ha hb rfl

theorem ev_gt {a b : Expr} {x y : Int}
    (ha : Eval P 𝒪 ρ a (.int x)) (hb : Eval P 𝒪 ρ b (.int y)) :
    Eval P 𝒪 ρ (.bin .gt a b) (enc .bool (decide (x > y))) := Eval.bin ha hb rfl

theorem ev_eq (τ : VTy) {a b : Expr} {x y : τ.denote} [DecidableEq τ.denote]
    (ha : Eval P 𝒪 ρ a (enc τ x)) (hb : Eval P 𝒪 ρ b (enc τ y)) :
    Eval P 𝒪 ρ (.bin .eq a b) (enc .bool (decide (x = y))) := by
  refine Eval.bin ha hb ?_
  simp only [binVal, enc, Option.some.injEq, Val.bool.injEq]
  rw [decide_eq_decide]
  exact ⟨enc_inj τ x y, fun h => h ▸ rfl⟩

theorem ev_ne (τ : VTy) {a b : Expr} {x y : τ.denote} [DecidableEq τ.denote]
    (ha : Eval P 𝒪 ρ a (enc τ x)) (hb : Eval P 𝒪 ρ b (enc τ y)) :
    Eval P 𝒪 ρ (.bin .ne a b) (enc .bool (decide (x ≠ y))) := by
  refine Eval.bin ha hb ?_
  simp only [binVal, enc, Option.some.injEq, Val.bool.injEq]
  rw [decide_eq_decide]
  exact ⟨fun h hxy => h (hxy ▸ rfl), fun h he => h (enc_inj τ x y he)⟩

theorem ev_and {a b : Expr} {x y : Bool}
    (ha : Eval P 𝒪 ρ a (enc .bool x)) (hb : Eval P 𝒪 ρ b (enc .bool y)) :
    Eval P 𝒪 ρ (.log .and a b) (enc .bool (x && y)) := Eval.log ha hb

theorem ev_or {a b : Expr} {x y : Bool}
    (ha : Eval P 𝒪 ρ a (enc .bool x)) (hb : Eval P 𝒪 ρ b (enc .bool y)) :
    Eval P 𝒪 ρ (.log .or a b) (enc .bool (x || y)) := Eval.log ha hb

theorem ev_implies {a b : Expr} {x y : Bool}
    (ha : Eval P 𝒪 ρ a (enc .bool x)) (hb : Eval P 𝒪 ρ b (enc .bool y)) :
    Eval P 𝒪 ρ (.log .implies a b) (enc .bool (!x || y)) := Eval.log ha hb

end VIR

/-- A recursive call's measure decrease, in a validation proof. Not trusted. -/
macro "vir_valid_dec" : tactic =>
  `(tactic| first
    | omega
    | (simp_all [VIR.invOk, VIR.enc, VModel.IntRange.contains, VModel.clip, VModel.Seq.len_eq,
        VModel.Seq.push_eq, VModel.Seq.add_eq]; omega)
    | (simp_all [VIR.invOk, VIR.enc, VModel.IntRange.contains, VModel.clip, VModel.Seq.len_eq,
        VModel.Seq.push_eq, VModel.Seq.add_eq]; (repeat' split) <;> omega))
