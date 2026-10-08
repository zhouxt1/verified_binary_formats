import Lspec.VIR.Syntax

/-! `virsubset LOG OUT ROOT...`: the VIR items of the spec functions reachable from the
ROOTs, read with `VIR.SExpr.parseMany` and written back one per line. -/

open VIR

partial def calls (acc : Array String) : SExpr → Array String
  | .list (.atom "CallTarget" :: .atom "Fun" :: _ :: .list [.atom "Fun", .atom ":path", .atom p] :: rest) =>
    rest.foldl calls (acc.push p)
  | .list xs => xs.foldl calls acc
  | _ => acc

def fnName? (it : SExpr) : Option String :=
  match it with
  | .list (.atom "Function" :: _) =>
    match it.kw? "name" with
    | some (.list [.atom "Fun", .atom ":path", .atom p]) => some p
    | _ => none
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | log :: out :: roots =>
    let text ← IO.FS.readFile log
    let items ← IO.ofExcept (SExpr.parseMany text)
    let mut byName : Std.HashMap String SExpr := {}
    for it in items do
      if let some n := fnName? it then byName := byName.insert n it
    let mut seen : Std.HashSet String := {}
    let mut todo := roots.toArray
    let mut order : Array String := #[]
    while h : todo.size > 0 do
      let f := todo.back
      todo := todo.pop
      if seen.contains f then continue
      seen := seen.insert f
      if (Conv.prim? f).isSome then continue
      match byName[f]? with
      | none => throw (IO.userError s!"no VIR for {f}")
      | some it =>
        order := order.push f
        let some body := it.kw? "body" | throw (IO.userError s!"no body in {f}")
        todo := calls todo body
    let lines := order.qsort (· < ·) |>.map fun f => (byName[f]!).toString
    IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")
    IO.println s!"{order.size} functions"
    return 0
  | _ => IO.eprintln "usage: virsubset LOG OUT ROOT..."; return 1
