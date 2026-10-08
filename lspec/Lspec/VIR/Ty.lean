/-!
# VIR types

The types of the Verus spec fragment (VIR's `Typ`), and the Lean type each denotes.
Every integer type denotes `Int`, `Seq<A>` denotes `List`, `Option<A>` denotes `Option`,
and an n-tuple denotes a right-nested product. Spec function types (closures) are not
here: they only occur as `Seq::new`'s argument, whose type no definition needs.
-/

namespace VModel

/-- Integer ranges, as VIR's `IntRange`. -/
inductive IntRange where
  | int | nat
  | u (bits : Nat)
  | i (bits : Nat)
  | usize | isize
  deriving DecidableEq, Repr, Inhabited

/-- VIR types in the fragment. -/
inductive VTy where
  | int (r : IntRange)
  | bool
  | seq (t : VTy)
  | opt (t : VTy)
  | tup (ts : List VTy)
  deriving Repr, Inhabited

mutual
/-- The Lean type a VIR type denotes. -/
@[reducible] def VTy.denote : VTy → Type
  | .int _ => Int
  | .bool => Bool
  | .seq t => List t.denote
  | .opt t => Option t.denote
  | .tup ts => VTy.denoteTup ts
/-- An n-tuple: `Unit`, the one type, or a right-nested product. -/
@[reducible] def VTy.denoteTup : List VTy → Type
  | [] => Unit
  | [t] => t.denote
  | t :: ts => t.denote × VTy.denoteTup ts
end

example : VTy.denote (.tup [.int .nat, .seq .bool, .bool]) = (Int × List Bool × Bool) := rfl

end VModel
