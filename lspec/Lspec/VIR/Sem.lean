import Lspec.VIR.Syntax
import Lspec.Bridge.Vstd

/-!
# VIR semantics: what a Verus spec function means

A big-step evaluation relation `Eval P O ρ e v` for the VIR fragment of `Syntax.lean`, in
program `P`, with `O` giving the values Verus leaves unspecified. This file, `Syntax.lean`
and the `Seq` recursions of `Bridge/Vstd.lean` are the **trusted** definition of Verus spec
code. Everything that relates them to the generated Lean definitions is proved.

Spec functions are total and terminate (Verus checks `decreases`), so each call has a finite
derivation, and the relation is the least one closed under these rules. `Eval` is
deterministic (`Eval.det`).

The rules follow Verus's encoding of the fragment into SMT:

* integers of every type are mathematical integers (`Val.int`), `Seq` values are lists
  (vstd defines `Seq` as a cons list), and tuples and `Option` are as in VIR;
* `x as T` keeps an in-range `x` and is unspecified otherwise (`O.clip`, the prelude's
  `u_clip`/`i_clip`/`nat_clip`); `/` and `%` are Euclidean, unspecified by zero;
* `+`, `-`, `*` whose VIR says `Truncate r` (as on `nat`) are clipped to `r` the same way:
  the reader inserts the clip, as Verus's `ast_to_sst.rs` does;
* `arbitrary::<A>()`, where a `Seq` index is out of range or a field of `None` is read, is
  `O.arb A`, one value per type;
* `exists|x: t|` and `forall|x: t|` range over the values of type `t` (`HasTy`), as Verus's
  quantifiers range over the values satisfying `has_type`;
* `&` and `>>` (unsigned only; the reader refuses others) are the bitwise operations on the
  naturals, clipped to the result type as Verus clips them. Verus leaves them uninterpreted
  in SMT apart from range axioms, and `by (bit_vector)` gives them their bit-vector meaning,
  which these agree with on in-range operands;
* a function's integer parameters carry their type's range (Verus's type invariants), and a
  call outside it is unspecified. No Verus call has one.
-/

namespace VIR

open VModel (IntRange VTy)

/-- Values. Closures occur only as `Seq::new`'s argument. -/
inductive Val where
  | int (i : Int)
  | bool (b : Bool)
  | seq (vs : List Val)
  | opt (o : Option Val)
  | tup (vs : List Val)
  | clo (ρ : List (String × Val)) (x : String) (body : Expr)
  deriving Inhabited

abbrev Env := List (String × Val)

/-- The values Verus leaves unspecified. -/
structure Oracle where
  arb : VTy → Val
  clip : IntRange → Int → Int
  div0 : Int → Int
  mod0 : Int → Int

/-! ## The `Seq` operations, by vstd's recursions (`VModel.Seq`) -/

/-- vstd's `arbitrary::<Seq<A>>()` as a list. -/
def Oracle.arbSeq (O : Oracle) (t : VTy) : List Val :=
  match O.arb (.seq t) with
  | .seq l => l
  | _ => []

/-- The `Seq` operations other than `Seq::new` (which takes a closure; see `Eval.new`). -/
def primVal (O : Oracle) : Prim → VTy → List Val → Option Val
  | .empty, _, [] => some (.seq [])
  | .len, _, [.seq vs] => some (.int (VModel.Seq.len vs))
  | .index, t, [.seq vs, .int i] => some (VModel.Seq.indexWith (O.arb t) vs i)
  | .push, _, [.seq vs, v] => some (.seq (VModel.Seq.push vs v))
  | .update, t, [.seq vs, .int i, a] => some (.seq (VModel.Seq.updateWith (O.arbSeq t) vs i a))
  | .subrange, _, [.seq vs, .int i, .int j] => some (.seq (VModel.Seq.subrange vs i j))
  | .add, _, [.seq a, .seq b] => some (.seq (VModel.Seq.add a b))
  | .last, t, [.seq vs] => some (VModel.Seq.indexWith (O.arb t) vs (VModel.Seq.len vs - 1))
  | .dropLast, _, [.seq vs] => some (.seq (VModel.Seq.dropLast vs))
  | .skip, _, [.seq vs, .int n] => some (.seq (VModel.Seq.skip vs n))
  | .take, _, [.seq vs, .int n] => some (.seq (VModel.Seq.take vs n))
  | _, _, _ => none

/-! ## Operators -/

open Classical in
noncomputable def binVal (O : Oracle) : BinOp → Val → Val → Option Val
  | .add, .int x, .int y => some (.int (x + y))
  | .sub, .int x, .int y => some (.int (x - y))
  | .mul, .int x, .int y => some (.int (x * y))
  | .ediv, .int x, .int y => some (.int (if y = 0 then O.div0 x else x / y))
  | .emod, .int x, .int y => some (.int (if y = 0 then O.mod0 x else x % y))
  | .band, .int x, .int y => some (.int (x.toNat &&& y.toNat : Nat))
  | .shr, .int x, .int y => some (.int (x.toNat >>> y.toNat : Nat))
  | .bxor, .int x, .int y => some (.int (x.toNat ^^^ y.toNat : Nat))
  | .eq, a, b => some (.bool (decide (a = b)))
  | .ne, a, b => some (.bool (decide (a ≠ b)))
  | .le, .int x, .int y => some (.bool (decide (x ≤ y)))
  | .lt, .int x, .int y => some (.bool (decide (x < y)))
  | .ge, .int x, .int y => some (.bool (decide (x ≥ y)))
  | .gt, .int x, .int y => some (.bool (decide (x > y)))
  | _, _, _ => none

def logVal : LogOp → Bool → Bool → Bool
  | .and, x, y => x && y
  | .or, x, y => x || y
  | .implies, x, y => !x || y

/-- Arguments in their parameters' integer ranges. -/
def invOk : List (String × VTy) → List Val → Prop
  | (_, .int r) :: ps, .int i :: vs => r.contains i = true ∧ invOk ps vs
  | (_, .int _) :: _, _ :: _ => False
  | _ :: ps, _ :: vs => invOk ps vs
  | _, _ => True

mutual
/-- `v` is a value of type `τ` (Verus's `has_type`): integers lie in their type's range. -/
def HasTy : VTy → Val → Prop
  | .int r, .int i => r.contains i = true
  | .bool, .bool _ => True
  | .seq t, .seq vs => ∀ v ∈ vs, HasTy t v
  | .opt _, .opt none => True
  | .opt t, .opt (some v) => HasTy t v
  | .tup ts, .tup vs => HasTys ts vs
  | _, _ => False
/-- `HasTy`, entry by entry. -/
def HasTys : List VTy → List Val → Prop
  | [], [] => True
  | t :: ts, v :: vs => HasTy t v ∧ HasTys ts vs
  | _, _ => False
end

/-- The definition of `f` in `P`. -/
def Prog.find (P : Prog) (f : String) : Option FnDef := P.find? (·.name == f)

/-! ## Evaluation -/

open Classical in
inductive Eval (P : Prog) (O : Oracle) : Env → Expr → Val → Prop where
  | int : Eval P O ρ (.int i) (.int i)
  | bool : Eval P O ρ (.bool b) (.bool b)
  | var : ρ.lookup x = some v → Eval P O ρ (.var x) v
  | tupField : Eval P O ρ e (.tup vs) → vs[i]? = some v → Eval P O ρ (.tupField e i) v
  | someFieldSome : Eval P O ρ e (.opt (some v)) → Eval P O ρ (.someField e t) v
  | someFieldNone : Eval P O ρ e (.opt none) → Eval P O ρ (.someField e t) (O.arb t)
  | lett : Eval P O ρ init v → Eval P O ((x, v) :: ρ) body w → Eval P O ρ (.lett x init body) w
  | iteT : Eval P O ρ c (.bool true) → Eval P O ρ t v → Eval P O ρ (.ite c t e) v
  | iteF : Eval P O ρ c (.bool false) → Eval P O ρ e v → Eval P O ρ (.ite c t e) v
  /-- A call: the arguments' values, then the body with the parameters bound to them. -/
  | call (vs : List Val) (d : FnDef) :
      vs.length = args.length → (∀ k (h : k < args.length), Eval P O ρ args[k] vs[k]!) →
      P.find f = some d → d.params.length = vs.length → invOk d.params vs →
      Eval P O ((d.params.map (·.1)).zip vs) d.body v → Eval P O ρ (.call f args) v
  /-- A call with an argument outside its type's range: unspecified. -/
  | callBad (vs : List Val) (d : FnDef) :
      vs.length = args.length → (∀ k (h : k < args.length), Eval P O ρ args[k] vs[k]!) →
      P.find f = some d → ¬invOk d.params vs → Eval P O ρ (.call f args) (O.arb d.ret)
  | prim (vs : List Val) :
      vs.length = args.length → (∀ k (h : k < args.length), Eval P O ρ args[k] vs[k]!) →
      p ≠ .new → primVal O p t vs = some v → Eval P O ρ (.prim p t args) v
  /-- `Seq::new(n, |x| body)`: `body` at `x = 0, ..., n - 1` (`SeqInner` recursion). -/
  | new (vs : List Val) :
      Eval P O ρ n (.int k) → 0 ≤ k → vs.length = k.toNat →
      (∀ j (h : j < vs.length), Eval P O ((x, .int j) :: ρ) body vs[j]) →
      Eval P O ρ (.prim .new t [n, .lam x body]) (.seq vs)
  | newNeg : Eval P O ρ n (.int k) → k < 0 →
      Eval P O ρ (.prim .new t [n, .lam x body]) (O.arb (.seq t))
  | tuple (vs : List Val) :
      vs.length = es.length → (∀ k (h : k < es.length), Eval P O ρ es[k] vs[k]!) →
      Eval P O ρ (.tuple es) (.tup vs)
  | some : Eval P O ρ e v → Eval P O ρ (.some e) (.opt (some v))
  | none : Eval P O ρ .none (.opt none)
  | ex (f : Val → Bool) : (∀ v, HasTy t v → Eval P O ((x, v) :: ρ) body (.bool (f v))) →
      Eval P O ρ (.ex x t body) (.bool (decide (∃ v, HasTy t v ∧ f v = true)))
  | all (f : Val → Bool) : (∀ v, HasTy t v → Eval P O ((x, v) :: ρ) body (.bool (f v))) →
      Eval P O ρ (.all x t body) (.bool (decide (∀ v, HasTy t v → f v = true)))
  | not : Eval P O ρ e (.bool b) → Eval P O ρ (.un .not e) (.bool (!b))
  | clip : Eval P O ρ e (.int i) →
      Eval P O ρ (.un (.clip r) e) (.int (if r.contains i then i else O.clip r i))
  | bin : Eval P O ρ a va → Eval P O ρ b vb → binVal O op va vb = some v →
      Eval P O ρ (.bin op a b) v
  | log : Eval P O ρ a (.bool x) → Eval P O ρ b (.bool y) →
      Eval P O ρ (.log op a b) (.bool (logVal op x y))
  | isSome : Eval P O ρ e (.opt o) → Eval P O ρ (.isSome e) (.bool o.isSome)
  | isNone : Eval P O ρ e (.opt o) → Eval P O ρ (.isNone e) (.bool o.isNone)
  | isTuple : Eval P O ρ e v → Eval P O ρ (.isTuple e) (.bool true)

/-- Calling `f` on `vs` in `P` gives `v`. -/
def RunsTo (P : Prog) (O : Oracle) (f : String) (vs : List Val) (v : Val) : Prop :=
  ∃ d, P.find f = some d ∧ d.params.length = vs.length ∧
    ((invOk d.params vs ∧ Eval P O ((d.params.map (·.1)).zip vs) d.body v) ∨
      (¬invOk d.params vs ∧ v = O.arb d.ret))

end VIR
