import Lspec.Bridge.VerusDeep
import Lspec.Bridge.WrapEq

/-!
# vdeflate's zlib and gzip contracts, by the VIR semantics, are the Lean spec's

As `VerusDeep.lean` does for `inflate`: each statement is about the trusted VIR semantics
(`VIR.RunsTo` on `V.vdeflateProg`, read from Verus's own VIR), for every well-typed oracle.
The generated shallow definitions and `WrapEq.lean` are only the proof.

These are the spec functions in the contracts of `inflate_zlib`, `inflate_zlib_dict`,
`inflate_gzip` and `inflate_gzip_file` (and the streaming `ZInflater`'s, which are stated
with the same functions).
-/

namespace Bridge

open VIR VModel

/-- The type of `zlib_decode`'s and `gzip_decode`'s result: the data, the bytes taken, the
zlib flag. -/
abbrev unwrappedTy : VTy := .opt (.tup [.seq (.int (.u 8)), .int .int, .bool])

/-- A Lean result as a Verus value. -/
def unwrappedV (r : Option Deflate.Unwrapped) : Option (List Int × Int × Bool) :=
  r.map fun r => (outV r.out, (r.used : Int), r.zlib)

/-- **`zlib_decode` is RFC 1950 without a preset dictionary**, `Deflate.zlibDecode`. -/
theorem verus_zlib_decode_eq (O : Oracle) (hO : WellTyped O) (s : Array UInt8) (v : Val) :
    RunsTo V.vdeflateProg O "vdeflate::wrap::zlib_decode" [enc (.seq (.int (.u 8))) (outV s)] v ↔
      v = enc unwrappedTy (unwrappedV (Deflate.zlibDecode s)) := by
  obtain ⟨u, rfl⟩ := exists_unspec O hO
  have h := V.«runs».«vdeflate».«wrap».«zlib_decode» u (outV s)
  rw [zlib_decode_eq] at h
  exact ⟨fun hv => hv.det h, fun hv => hv ▸ h⟩

/-- **`zlib_decode_dict` is RFC 1950 with the preset dictionary `dict`**,
`Deflate.zlibDecodeDict`. -/
theorem verus_zlib_decode_dict_eq (O : Oracle) (hO : WellTyped O) (s dict : Array UInt8) (v : Val) :
    RunsTo V.vdeflateProg O "vdeflate::wrap::zlib_decode_dict"
        [enc (.seq (.int (.u 8))) (outV s), enc (.seq (.int (.u 8))) (outV dict)] v ↔
      v = enc unwrappedTy (unwrappedV (Deflate.zlibDecodeDict s dict)) := by
  obtain ⟨u, rfl⟩ := exists_unspec O hO
  have h := V.«runs».«vdeflate».«wrap».«zlib_decode_dict» u (outV s) (outV dict)
  rw [zlib_decode_dict_eq] at h
  exact ⟨fun hv => hv.det h, fun hv => hv ▸ h⟩

/-- **`gzip_decode` is one RFC 1952 member**, `Deflate.gzipDecode`. -/
theorem verus_gzip_decode_eq (O : Oracle) (hO : WellTyped O) (s : Array UInt8) (v : Val) :
    RunsTo V.vdeflateProg O "vdeflate::wrap::gzip_decode" [enc (.seq (.int (.u 8))) (outV s)] v ↔
      v = enc unwrappedTy (unwrappedV (Deflate.gzipDecode s)) := by
  obtain ⟨u, rfl⟩ := exists_unspec O hO
  have h := V.«runs».«vdeflate».«wrap».«gzip_decode» u (outV s)
  rw [gzip_decode_eq] at h
  exact ⟨fun hv => hv.det h, fun hv => hv ▸ h⟩

/-- **`gzip_file` is an RFC 1952 file, members to the end**, `Deflate.gzipFile`. -/
theorem verus_gzip_file_eq (O : Oracle) (hO : WellTyped O) (s : Array UInt8) (v : Val) :
    RunsTo V.vdeflateProg O "vdeflate::wrap::gzip_file" [enc (.seq (.int (.u 8))) (outV s)] v ↔
      v = enc (.opt (.seq (.int (.u 8)))) ((Deflate.gzipFile s).map outV) := by
  obtain ⟨u, rfl⟩ := exists_unspec O hO
  have h := V.«runs».«vdeflate».«wrap».«gzip_file» u (outV s)
  rw [gzip_file_eq] at h
  exact ⟨fun hv => hv.det h, fun hv => hv ▸ h⟩

end Bridge
