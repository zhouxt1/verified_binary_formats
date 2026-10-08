import Lean
import Lspec.VIR.Syntax

/-!
# Loading a VIR dump into Lean

`vir_program p from "file"` reads a VIR file (as `virsubset` writes it; the path is relative
to the Lean file) when the Lean file is built, converts it with `VIR.readProg`, and defines `p : VIR.Prog` as the result. The program
is never written out as Lean text, so no step between Verus's log and the definition can be
edited by hand.
-/

open Lean Elab Command

elab "vir_program " id:ident " from " path:str : command => do
  let file := (System.FilePath.mk (← getFileName)).parent.getD "." / path.getString
  let text ← IO.FS.readFile file
  match VIR.readProg text with
  | .error e => throwError m!"VIR: {e}"
  | .ok prog =>
    let value := toExpr prog
    liftCoreM <| addDecl <| Declaration.defnDecl {
      name := id.getId, levelParams := [], type := mkConst ``VIR.Prog, value,
      hints := .abbrev, safety := .safe }
    logInfo m!"{prog.length} spec functions from {path.getString}"
