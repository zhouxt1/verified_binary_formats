import Lspec.Bridge.DeflateEq

/-!
# The rest of vdeflate's contracts, in Lean spec terms

vdeflate's exec functions state their contracts with a few spec functions besides
`spec::inflate`: the decoders say `inflate(lbits(buf@))`, and the compressors say
`deflate_ok(data@, o@)`, which needs `is_prefix` too. Here each is shown equal, in the
shallow model, to its Lean reading: `lbits` is the RFC's packing `Deflate.bitsOf`, and
`deflate_ok` is `CompressesTo` below. `VerusDeep.lean` states the results against the VIR
semantics. Nothing here is trusted.
-/

namespace Bridge

open VModel

/-- What vdeflate's compressors promise of their output `o` on input `data`: its bits,
followed by anything, decode to `data` by the Lean spec, ending at a bit `q` inside the last
byte of `o`, and zlib accepts the stream too. "Followed by anything" lets the output be
concatenated or padded. -/
def CompressesTo (data o : Array UInt8) : Prop :=
  ∃ q : Nat, (q + 7) / 8 = o.size ∧
    ∀ b : Deflate.Bits, (Deflate.bitsOf o).toList <+: b.toList →
      Deflate.inflate b = some { out := data, bits := q, zlib := true }

theorem lbit_eq (u : Unspec) (b : UInt8) (i : Nat) (hi : i < 8) :
    V.vbits.lsb.lbit u (b.toNat : Int) (i : Int) = b.toNat.testBit i := by
  have hb := b.toNat_lt
  have hs : b.toNat >>> i ≤ b.toNat := Nat.shiftRight_le _ _
  have hci : clip u (.u 8) (i : Int) = i := clip_of_contains u _ _ (by simp [IntRange.contains]; omega)
  have e1 : shr (b.toNat : Int) (i : Int) = ((b.toNat >>> i : Nat) : Int) := by
    unfold shr; rw [Int.toNat_natCast, Int.toNat_natCast]
  generalize hm : b.toNat >>> i = m at hs e1
  have hcm : clip u (.u 8) (m : Int) = m := clip_of_contains u _ _ (by simp [IntRange.contains]; omega)
  have e2 : band (m : Int) 1 = ((m % 2 : Nat) : Int) := by
    unfold band; rw [Int.toNat_natCast, show (1 : Int).toNat = 1 from rfl, Nat.and_one_is_mod]
  have h2 : m % 2 < 2 := Nat.mod_lt _ (by decide)
  have hc2 : clip u (.u 8) ((m % 2 : Nat) : Int) = ((m % 2 : Nat) : Int) :=
    clip_of_contains u _ _ (by simp [IntRange.contains]; omega)
  unfold V.vbits.lsb.lbit
  rw [dif_pos (by simp [IntRange.contains]; omega), hci, e1, hcm, e2, hc2]
  simp only [Nat.testBit, Nat.and_comm 1, Nat.and_one_is_mod, hm]
  rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
  · have : m % 2 = 0 := by omega
    simp [this]
  · simp [h]

theorem lbits_eq (u : Unspec) (s : Array UInt8) :
    V.vbits.lsb.lbits u (outV s) = (Deflate.bitsOf s).toList := by
  unfold V.vbits.lsb.lbits
  rw [Seq.len_list, show ((outV s).length : Int) * 8 = ((s.size * 8 : Nat) : Int) by simp [outV],
    clip_nat u _ (by omega), Seq.new_eq]
  apply List.ext_getElem (by simp [Deflate.bitsOf])
  intro k h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, Deflate.bitsOf, Array.toList_ofFn,
    List.getElem_ofFn]
  rw [ediv_ne u _ _ (by omega), emod_ne u _ _ (by omega),
    show (k : Int) / 8 = ((k / 8 : Nat) : Int) by omega,
    show (k : Int) % 8 = ((k % 8 : Nat) : Int) by omega,
    Seq.index_eq u _ _ (by simp [outV]; omega)]
  simp only [outV, List.getElem_map, Array.getElem_toList]
  exact lbit_eq u _ _ (by omega)

theorem is_prefix_eq (u : Unspec) (b1 b2 : List Bool) :
    V.vdeflate.step.is_prefix u b1 b2 = decide (b1 <+: b2) := by
  unfold V.vdeflate.step.is_prefix
  rw [Bool.eq_iff_iff]
  simp only [Seq.len_list, Bool.and_eq_true, decide_eq_true_eq, List.prefix_iff_eq_take]
  constructor
  · rintro ⟨hl, hall⟩
    apply List.ext_getElem (by simp; omega)
    intro k hk1 hk2
    have := hall k
    simp only [Seq.len_list, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp,
      decide_eq_true_eq, decide_eq_false_iff_not] at this
    rcases this with h | h
    · omega
    · rw [Seq.index_eq u _ k hk1, Seq.index_eq u _ k (by omega)] at h
      simp [h]
  · intro h
    have hl : b1.length ≤ b2.length := by
      have := congrArg List.length h; simp at this; omega
    refine ⟨by omega, fun i => ?_⟩
    simp only [Seq.len_list, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp,
      decide_eq_true_eq, decide_eq_false_iff_not]
    by_cases hi : 0 ≤ i ∧ i < b1.length
    · right
      obtain ⟨k, rfl⟩ : ∃ k : Nat, i = k := ⟨i.toNat, by omega⟩
      rw [Seq.index_eq u _ k (by omega), Seq.index_eq u _ k (by omega)]
      have : b1[k]'(by omega) = (List.take b1.length b2)[k]'(by simp; omega) := by
        simp only [← h]
      rw [this, List.getElem_take]
    · left; omega

theorem map_inj_of {α β : Type} {f : α → β} (hf : ∀ x y, f x = f y → x = y) :
    ∀ {l1 l2 : List α}, l1.map f = l2.map f → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf _ _ h.1, map_inj_of hf h.2]

theorem outV_inj {a b : Array UInt8} (h : outV a = outV b) : a = b := by
  apply Array.toList_inj.1
  exact map_inj_of (fun x y (e : (x.toNat : Int) = y.toNat) => UInt8.toNat_inj.1 (by omega)) h

open Classical in
theorem deflate_ok_eq (u : Unspec) (data o : Array UInt8) :
    V.vdeflate.enc2.deflate_ok u (outV data) (outV o) = decide (CompressesTo data o) := by
  unfold V.vdeflate.enc2.deflate_ok V.vdeflate.enc2.inflate_q CompressesTo
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, VTy.wt, IntRange.contains, Bool.and_eq_true,
    Seq.len_list, outV, List.length_map, Array.length_toList, implies_true, forall_const,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, hlen, hall⟩
    obtain ⟨n, rfl⟩ : ∃ n : Nat, q = n := ⟨q.toNat, by omega⟩
    refine ⟨n, ?_, fun b hb => ?_⟩
    · rw [clip_nat u _ (by omega), ediv_ne u _ _ (by omega)] at hlen; omega
    · have := hall b.toList
      rw [show (List.map (fun x : UInt8 => (x.toNat : Int)) o.toList) = outV o from rfl,
        lbits_eq, is_prefix_eq, verus_inflate_eq] at this
      simp only [decide_eq_false_iff_not] at this
      rcases this with h | h
      · exact absurd hb h
      · cases hd : Deflate.inflate b with
        | none => rw [hd] at h; simp at h
        | some d =>
          rw [hd] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2, h3⟩ := h
          have : d.out = data := outV_inj h1
          cases d; simp_all; omega
  · rintro ⟨n, hlen, hall⟩
    refine ⟨n, by omega, ?_, fun b => ?_⟩
    · rw [clip_nat u _ (by omega), ediv_ne u _ _ (by omega)]
      exact ⟨by simp, by omega⟩
    · rw [show (List.map (fun x : UInt8 => (x.toNat : Int)) o.toList) = outV o from rfl,
        lbits_eq, is_prefix_eq]
      by_cases hb : (Deflate.bitsOf o).toList <+: b
      · right
        have := hall ⟨b⟩ hb
        rw [show b = (Array.mk b).toList from rfl, verus_inflate_eq, this]
        simp [outV]
      · left; simpa using hb

end Bridge
