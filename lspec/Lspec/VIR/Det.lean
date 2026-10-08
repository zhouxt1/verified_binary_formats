import Lspec.VIR.Sem

/-!
# The VIR semantics is deterministic

`Eval.det`: an expression evaluates to at most one value, so `Eval` (and `RunsTo`) define
partial functions. A proved property of the trusted semantics.
-/

namespace VIR

theorem list_eq_of_get {vs ws : List Val} (hv : vs.length = ws.length)
    (h : ∀ k (hk : k < vs.length), vs[k]! = ws[k]!) : vs = ws := by
  apply List.ext_getElem hv
  intro k h1 h2
  have := h k h1
  simp only [getElem!_def, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at this
  exact this

theorem Eval.det {P : Prog} {O : Oracle} {ρ : Env} {e : Expr} {v w : Val}
    (h1 : Eval P O ρ e v) (h2 : Eval P O ρ e w) : v = w := by
  induction h1 generalizing w with
  | int => cases h2; rfl
  | bool => cases h2; rfl
  | var h => cases h2; rename_i h'; rw [h] at h'; exact Option.some.inj h'
  | tupField _ hv ih =>
    cases h2 with
    | tupField h' hv' => have := ih h'; injection this with this; subst this; rw [hv] at hv'; exact Option.some.inj hv'
  | someFieldSome _ ih =>
    cases h2 with
    | someFieldSome h' => have := ih h'; injection this with this; exact Option.some.inj this
    | someFieldNone h' => have := ih h'; injection this with this; cases this
  | someFieldNone _ ih =>
    cases h2 with
    | someFieldSome h' => have := ih h'; injection this with this; cases this
    | someFieldNone h' => rfl
  | lett _ _ ih1 ih2 =>
    cases h2 with
    | lett h1' h2' => have := ih1 h1'; subst this; exact ih2 h2'
  | iteT _ _ ihc iht =>
    cases h2 with
    | iteT _ h' => exact iht h'
    | iteF hc' _ => have := ihc hc'; cases this
  | iteF _ _ ihc ihe =>
    cases h2 with
    | iteT hc' _ => have := ihc hc'; cases this
    | iteF _ h' => exact ihe h'
  | call vs d hl hk hd hp hi hb ihk ihb =>
    cases h2 with
    | call vs' d' hl' hk' hd' hp' hi' hb' =>
      have hv : vs = vs' := list_eq_of_get (by omega) fun k hk2 => ihk k (by omega) (hk' k (by omega))
      subst hv
      rw [hd] at hd'; cases hd'
      exact ihb hb'
    | callBad vs' d' hl' hk' hd' hi' =>
      have hv : vs = vs' := list_eq_of_get (by omega) fun k hk2 => ihk k (by omega) (hk' k (by omega))
      subst hv
      rw [hd] at hd'; cases hd'
      exact absurd hi hi'
  | callBad vs d hl hk hd hi ihk =>
    cases h2 with
    | call vs' d' hl' hk' hd' hp' hi' hb' =>
      have hv : vs = vs' := list_eq_of_get (by omega) fun k hk2 => ihk k (by omega) (hk' k (by omega))
      subst hv
      rw [hd] at hd'; cases hd'
      exact absurd hi' hi
    | callBad vs' d' hl' hk' hd' hi' =>
      rw [hd] at hd'; cases hd'; rfl
  | prim vs hl hk hp hv ihk =>
    cases h2 with
    | prim vs' hl' hk' hp' hv' =>
      have he : vs = vs' := list_eq_of_get (by omega) fun k hk2 => ihk k (by omega) (hk' k (by omega))
      subst he
      rw [hv] at hv'; exact Option.some.inj hv'
    | new => exact absurd rfl hp
    | newNeg => exact absurd rfl hp
  | new vs hn hk hl hb ihn ihb =>
    cases h2 with
    | prim _ _ _ hp _ => exact absurd rfl hp
    | new vs' hn' hk' hl' hb' =>
      have := ihn hn'; injection this with this; subst this
      congr 1
      apply List.ext_getElem (by omega)
      intro j h1 h2
      exact ihb j h1 (hb' j h2)
    | newNeg hn' hk' => have := ihn hn'; injection this with this; subst this; omega
  | newNeg hn hk ihn =>
    cases h2 with
    | prim _ _ _ hp _ => exact absurd rfl hp
    | new vs' hn' hk' hl' hb' => have := ihn hn'; injection this with this; subst this; omega
    | newNeg _ _ => rfl
  | tuple vs hl hk ihk =>
    cases h2 with
    | tuple vs' hl' hk' =>
      congr 1
      exact list_eq_of_get (by omega) fun k hk2 => ihk k (by omega) (hk' k (by omega))
  | some _ ih => cases h2 with | some h' => rw [ih h']
  | none => cases h2; rfl
  | ex f hf ih =>
    cases h2 with
    | ex g hg =>
      have e : ∀ v, HasTy _ v → f v = g v := fun v hv => by have := ih v hv (hg v hv); injection this
      congr 2
      exact propext ⟨fun ⟨v, hv, h⟩ => ⟨v, hv, (e v hv) ▸ h⟩, fun ⟨v, hv, h⟩ => ⟨v, hv, (e v hv) ▸ h⟩⟩
  | all f hf ih =>
    cases h2 with
    | all g hg =>
      have e : ∀ v, HasTy _ v → f v = g v := fun v hv => by have := ih v hv (hg v hv); injection this
      congr 2
      exact propext ⟨fun h v hv => (e v hv) ▸ h v hv, fun h v hv => (e v hv) ▸ h v hv⟩
  | not _ ih => cases h2 with | not h' => have := ih h'; injection this with this; subst this; rfl
  | clip _ ih => cases h2 with | clip h' => have := ih h'; injection this with this; subst this; rfl
  | bin _ _ hv iha ihb =>
    cases h2 with
    | bin ha' hb' hv' => have := iha ha'; subst this; have := ihb hb'; subst this; rw [hv] at hv'; exact Option.some.inj hv'
  | log _ _ iha ihb =>
    cases h2 with
    | log ha' hb' =>
      have := iha ha'; injection this with this; subst this
      have := ihb hb'; injection this with this; subst this; rfl
  | isSome _ ih => cases h2 with | isSome h' => have := ih h'; injection this with this; subst this; rfl
  | isNone _ ih => cases h2 with | isNone h' => have := ih h'; injection this with this; subst this; rfl
  | isTuple _ _ => cases h2; rfl

theorem RunsTo.det {P : Prog} {O : Oracle} {f : String} {vs : List Val} {v w : Val}
    (h1 : RunsTo P O f vs v) (h2 : RunsTo P O f vs w) : v = w := by
  obtain ⟨d, hd, hp, hb | ⟨hi, rfl⟩⟩ := h1 <;> obtain ⟨d', hd', hp', hb' | ⟨hi', rfl⟩⟩ := h2 <;>
    (rw [hd] at hd'; cases hd')
  · exact hb.2.det hb'.2
  · exact absurd hb.1 hi'
  · exact absurd hb'.1 hi
  · rfl

end VIR
