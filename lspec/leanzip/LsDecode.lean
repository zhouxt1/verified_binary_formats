import Zip.Spec.Deflate

/-! Batch driver: lean-zip's spec decoder `Deflate.Spec.decode.goR` on raw
DEFLATE files, one path per stdin line; prints `PATH ok LEN BITS FNV` or
`PATH bad`. -/

def fnv (s : List UInt8) : UInt64 :=
  s.foldl (fun h x => (h ^^^ x.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

def hex16 (x : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let path := line.trimAsciiEnd.toString
  if !path.isEmpty then
    let data ← IO.FS.readBinFile path
    let bits := Deflate.Spec.bytesToBits data
    match Deflate.Spec.decode.goR bits [] with
    | some (out, rest) =>
      stdout.putStrLn s!"{path} ok {out.length} {bits.length - rest.length} {hex16 (fnv out)}"
    | none => stdout.putStrLn s!"{path} bad"
    stdout.flush
  loop stdin stdout

def main : IO Unit := do loop (← IO.getStdin) (← IO.getStdout)
