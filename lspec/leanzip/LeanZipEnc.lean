import Zip.Spec.DeflateRoundtrip
import LeanZipEq

/-!
# lean-zip's compressor against the Lean spec

lean-zip proves its compressor `deflateRaw` writes exactly one stream that its own spec
decodes to the input (`isValidStreamFor_deflateRaw`). With `LeanZipEq.leanzip_goR_eq`
that becomes a statement about `LeanZipSpec.inflate`, and with
`LeanZipSpec.inflate_spec` one about this spec, `Deflate.inflateBytes`.
-/

namespace LeanZipEnc

open Deflate.Spec Zip.Native.Deflate

/-- lean-zip's compressor, judged by lean-zip's reading in this spec's terms. -/
theorem leanzip_deflateRaw_leanZipSpec (data : ByteArray) (level : UInt8) :
    ∃ d, LeanZipSpec.inflate (Deflate.bitsOf (deflateRaw data level).data) = some d ∧
      d.out = data.data ∧ (deflateRaw data level).size * 8 < d.bits + 8 := by
  obtain ⟨rem, h, hr⟩ := isValidStreamFor_deflateRaw data level
  rw [LeanZipEq.leanzip_goR_eq] at h
  cases hd : LeanZipSpec.inflate (Deflate.bitsOf (deflateRaw data level).data) with
  | none => simp [hd] at h
  | some d =>
    simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨d, rfl, Array.toList_inj.mp h1, ?_⟩
    rw [← h2, List.length_drop, bytesToBits_length] at hr
    omega

/-- **lean-zip's compressor, judged by the Lean spec**: for any input and level, the
spec decodes `deflateRaw`'s output to the input, and the stream ends in the last byte. -/
theorem leanzip_deflateRaw (data : ByteArray) (level : UInt8) :
    ∃ d, Deflate.inflateBytes (deflateRaw data level).data = some d ∧
      d.out = data.data ∧ (deflateRaw data level).size * 8 < d.bits + 8 := by
  obtain ⟨d, h, h1, h2⟩ := leanzip_deflateRaw_leanZipSpec data level
  exact ⟨d, LeanZipSpec.inflate_spec h, h1, h2⟩

end LeanZipEnc
