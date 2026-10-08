import Lspec

/-! `lspec`: run the Lean specs on files.

    lspec deflate FILE         decode a raw DEFLATE stream; print the verdict
    lspec deflate --batch      one path per stdin line; print
                               `PATH ok ZLIB LEN BITS FNV` or `PATH bad`,
                               as `vdeflate-tool --batch` does
    lspec wrap --batch         lines `zlib PATH`, `gzip PATH`, `gzipfile PATH`
                               or `zlibdict PATH DICTPATH`; print what
                               `vdeflate-tool --batch-wrap` does:
                               `PATH ok ZLIB LEN USED FNV` (`PATH ok LEN FNV`
                               for gzipfile) or `PATH bad`
-/

/-- FNV-1a, 64-bit: the digest difftest/deflate compares outputs by. -/
def fnv (s : Array UInt8) : UInt64 :=
  s.foldl (fun h x => (h ^^^ x.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

def hex16 (x : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

def verdict (data : Array UInt8) : String :=
  match Deflate.inflateBytes data with
  | some r => s!"ok {if r.zlib then 1 else 0} {r.out.size} {r.bits} {hex16 (fnv r.out)}"
  | none => "bad"

partial def batch (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let path := line.trimAsciiEnd.toString
  if !path.isEmpty then
    let data ← IO.FS.readBinFile path
    stdout.putStrLn s!"{path} {verdict data.data}"
    stdout.flush
  batch stdin stdout

def unwrapped (path : String) : Option Deflate.Unwrapped → String
  | some u => s!"{path} ok {if u.zlib then 1 else 0} {u.out.size} {u.used} {hex16 (fnv u.out)}"
  | none => s!"{path} bad"

partial def wrapBatch (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let words := (line.trimAsciiEnd.toString.splitOn " ").filter (· ≠ "")
  let out ← match words with
    | ["zlib", path] => do
      let s ← IO.FS.readBinFile path
      pure (unwrapped path (Deflate.zlibDecode s.data))
    | ["gzip", path] => do
      let s ← IO.FS.readBinFile path
      pure (unwrapped path (Deflate.gzipDecode s.data))
    | ["zlibdict", path, dpath] => do
      let s ← IO.FS.readBinFile path
      let d ← IO.FS.readBinFile dpath
      pure (unwrapped path (Deflate.zlibDecodeDict s.data d.data))
    | ["gzipfile", path] => do
      let s ← IO.FS.readBinFile path
      pure (match Deflate.gzipFile s.data with
        | some o => s!"{path} ok {o.size} {hex16 (fnv o)}"
        | none => s!"{path} bad")
    | _ => pure s!"? {line.trimAsciiEnd}"
  stdout.putStrLn out
  stdout.flush
  wrapBatch stdin stdout

def main (args : List String) : IO UInt32 := do
  match args with
  | ["wrap", "--batch"] =>
    wrapBatch (← IO.getStdin) (← IO.getStdout)
    return 0
  | ["deflate", "--batch"] =>
    batch (← IO.getStdin) (← IO.getStdout)
    return 0
  | ["deflate", path] =>
    let data ← IO.FS.readBinFile path
    match Deflate.inflateBytes data.data with
    | some r =>
      IO.println s!"ok {r.out.size} bytes in {r.bits} bits, zlib {if r.zlib then "accepts" else "rejects"}"
      return 0
    | none => IO.println "bad"; return 2
  | _ =>
    IO.eprintln "usage: lspec deflate FILE | lspec deflate --batch | lspec wrap --batch"
    return 1
