import Zip.Native.Inflate
import Zip.Native.DeflateDynamic

/-! Timing driver for the vdeflate comparison: best of `reps` runs.
    lztime inflate <raw-deflate-file> <expected-size> [reps]
    lztime deflate <file> <level> [reps] -/

def bestOf (reps : Nat) (f : Unit → IO Nat) : IO (Nat × Nat) := do
  let mut best := 0
  let mut r := 0
  for i in [0:reps] do
    let t0 ← IO.monoNanosNow
    r ← f ()
    let t1 ← IO.monoNanosNow
    if i == 0 || t1 - t0 < best then best := t1 - t0
  return (r, best)

def main (args : List String) : IO Unit := do
  match args with
  | ["inflate", path, n, reps] =>
    let c ← IO.FS.readBinFile path
    let sz := n.toNat!
    let (r, t) ← bestOf reps.toNat! fun _ => do
      let o ← IO.lazyPure fun _ => Zip.Native.Inflate.inflate c (sizeHint := sz)
      match o with
      | .ok o => pure o.size
      | .error e => throw (IO.userError s!"inflate failed: {e}")
    IO.println s!"{path} {r} {(Float.ofNat sz) / (Float.ofNat t) * 1000.0}"
  | ["deflate", path, lv, reps] =>
    let d ← IO.FS.readBinFile path
    let (r, t) ← bestOf reps.toNat! fun _ => do
      let o ← IO.lazyPure fun _ => Zip.Native.Deflate.deflateRaw d lv.toNat!.toUInt8
      pure o.size
    IO.println s!"{path} {d.size} {r} {(Float.ofNat d.size) / (Float.ofNat t) * 1000.0}"
  | _ => throw (IO.userError "usage: lztime inflate FILE N REPS | lztime deflate FILE LEVEL REPS")
