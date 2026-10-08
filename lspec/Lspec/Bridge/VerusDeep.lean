import Lspec.Bridge.VDeflateValid
import Lspec.Bridge.ContractsEq
import Lspec.VIR.Det

/-!
# vdeflate's Verus spec, by the VIR semantics, is the Lean spec

`verus_spec_eq` states the bridge against the trusted definition of Verus spec code, the
VIR semantics `VIR.RunsTo`/`VIR.Eval`, on `V.vdeflateProg`, which Lean reads from Verus's own
VIR. The generated shallow definitions (`VDeflate.lean`) appear nowhere in the statement.
They are a proved stepping stone (`VDeflateValid.lean`, `DeflateEq.lean`).

The statement holds for every well-typed oracle, which covers every choice of the values
Verus leaves unspecified, as long as each has its type.

The other spec functions in vdeflate's contracts get the same treatment: `lbits` (so the
decoders' `inflate(lbits(buf@))` is `Deflate.inflateBytes`, `verus_inflate_bytes_eq`) and
`deflate_ok`, the compressors' promise (`verus_deflate_ok_eq`, which is `CompressesTo`).
-/

namespace Bridge

open VIR VModel

/-- Unspecified values of the right types, as Verus's are (its `has_type` invariants and the
prelude's clip axioms). -/
structure WellTyped (O : Oracle) : Prop where
  arb : ∀ τ, ∃ x : τ.denote, O.arb τ = enc τ x
  clip : ∀ (r : IntRange) (x : Int), IntRange.contains r (O.clip r x) = true

/-- Every well-typed oracle is that of some shallow-model `Unspec`. -/
theorem exists_unspec (O : Oracle) (h : WellTyped O) : ∃ u : Unspec, VIR.Oracle.ofUnspec u = O := by
  refine ⟨{ arb := fun τ => (h.arb τ).choose, clip := O.clip, clip_ok := h.clip,
            div0 := O.div0, mod0 := O.mod0 }, ?_⟩
  cases O with
  | mk arb clip div0 mod0 =>
    simp only [VIR.Oracle.ofUnspec, VIR.Oracle.mk.injEq, and_true]
    funext τ
    exact ((h.arb τ).choose_spec).symm

/-- **vdeflate's Verus spec is the Lean spec.** By the VIR semantics, `vdeflate::spec::inflate`
on the bits `b` runs to exactly one value, the Lean spec's result: the decoded data, the bits
used, and the zlib flag, or `None`. -/
theorem verus_spec_eq (O : Oracle) (hO : WellTyped O) (b : Deflate.Bits) (v : Val) :
    RunsTo V.vdeflateProg O "vdeflate::spec::inflate" [enc (.seq .bool) b.toList] v ↔
      v = enc (.opt (.tup [.seq (.int (.u 8)), .int .nat, .bool]))
        ((Deflate.inflate b).map fun d => (outV d.out, (d.bits : Int), d.zlib)) := by
  obtain ⟨u, rfl⟩ := exists_unspec O hO
  have h := V.«runs».«vdeflate».«spec».«inflate» u b.toList
  rw [verus_inflate_eq] at h
  exact ⟨fun hv => hv.det h, fun hv => hv ▸ h⟩

/-- **`lbits` is RFC 1951's packing of bytes into bits.** -/
theorem verus_lbits_eq (O : Oracle) (hO : WellTyped O) (s : Array UInt8) (v : Val) :
    RunsTo V.vdeflateProg O "vbits::lsb::lbits" [enc (.seq (.int (.u 8))) (outV s)] v ↔
      v = enc (.seq .bool) (Deflate.bitsOf s).toList := by
  obtain ⟨u, rfl⟩ := exists_unspec O hO
  have h := V.«runs».«vbits».«lsb».«lbits» u (outV s)
  rw [lbits_eq] at h
  exact ⟨fun hv => hv.det h, fun hv => hv ▸ h⟩

/-- **The decoders' contract, `inflate(lbits(buf@))`, is the Lean spec on bytes.** Whatever
`lbits` gives on the bytes `s`, `spec::inflate` on it runs to exactly the result of
`Deflate.inflateBytes s`. -/
theorem verus_inflate_bytes_eq (O : Oracle) (hO : WellTyped O) (s : Array UInt8) (w v : Val)
    (hw : RunsTo V.vdeflateProg O "vbits::lsb::lbits" [enc (.seq (.int (.u 8))) (outV s)] w) :
    RunsTo V.vdeflateProg O "vdeflate::spec::inflate" [w] v ↔
      v = enc (.opt (.tup [.seq (.int (.u 8)), .int .nat, .bool]))
        ((Deflate.inflateBytes s).map fun d => (outV d.out, (d.bits : Int), d.zlib)) := by
  rw [(verus_lbits_eq O hO s w).1 hw]
  exact verus_spec_eq O hO (Deflate.bitsOf s) v

open Classical in
/-- **The compressors' contract, `deflate_ok(data@, o@)`, is `CompressesTo data o`**: by the
VIR semantics it runs to exactly the truth value of `CompressesTo`. -/
theorem verus_deflate_ok_eq (O : Oracle) (hO : WellTyped O) (data o : Array UInt8) (v : Val) :
    RunsTo V.vdeflateProg O "vdeflate::enc2::deflate_ok"
        [enc (.seq (.int (.u 8))) (outV data), enc (.seq (.int (.u 8))) (outV o)] v ↔
      v = .bool (decide (CompressesTo data o)) := by
  obtain ⟨u, rfl⟩ := exists_unspec O hO
  have h := V.«runs».«vdeflate».«enc2».«deflate_ok» u (outV data) (outV o)
  rw [deflate_ok_eq] at h
  exact ⟨fun hv => hv.det h, fun hv => hv ▸ h⟩

end Bridge
