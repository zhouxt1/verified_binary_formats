import Lean
import Lspec.VIR.Ty

/-!
# VIR syntax: Verus's elaborated spec code, as Lean data

Verus logs the VIR of what it verifies (`--log vir-simple --log vir-option=no_span`) as
S-expressions. `SExpr.parseMany` reads them, and `Conv.fn` turns a spec function's VIR into
a `VIR.FnDef`. Both are **trusted**, together with the semantics in `Sem.lean`. They are
kept to one case per VIR form, and any form outside the fragment is an error, not skipped.
-/

namespace VIR

open VModel (IntRange VTy)

/-! ## S-expressions -/

inductive SExpr where
  | atom (s : String)
  | str (s : String)
  | list (xs : List SExpr)
  deriving Inhabited, Repr, BEq

namespace SExpr

/-- Read every top-level S-expression. `;;` starts a comment to the end of the line, and
strings are `"..."` with `\` escaping the next character. -/
partial def parseMany (s : String) : Except String (List SExpr) := do
  let cs := s.toList.toArray
  let rec skip (i : Nat) : Nat :=
    if h : i < cs.size then
      let c := cs[i]
      if c == ';' then
        let rec eol (j : Nat) : Nat := if h : j < cs.size then (if cs[j] == '\n' then j else eol (j + 1)) else j
        skip (eol i)
      else if c.isWhitespace then skip (i + 1) else i
    else i
  let rec atomEnd (i : Nat) : Nat :=
    if h : i < cs.size then
      let c := cs[i]
      if c.isWhitespace || c == '(' || c == ')' || c == '"' then i else atomEnd (i + 1)
    else i
  let rec strEnd (i : Nat) (acc : String) : Except String (String × Nat) :=
    if h : i < cs.size then
      let c := cs[i]
      if c == '"' then .ok (acc, i + 1)
      else if c == '\\' then
        if h2 : i + 1 < cs.size then strEnd (i + 2) (acc.push cs[i + 1]) else .error "bad escape"
      else strEnd (i + 1) (acc.push c)
    else .error "unterminated string"
  -- an explicit stack of open lists
  let rec go (i : Nat) (stack : List (List SExpr)) (top : List SExpr) : Except String (List SExpr) :=
    let i := skip i
    if h : i < cs.size then
      let c := cs[i]
      if c == '(' then go (i + 1) (top :: stack) []
      else if c == ')' then
        match stack with
        | [] => .error s!"unbalanced ')' at {i}"
        | t :: rest => go (i + 1) rest (SExpr.list top.reverse :: t)
      else if c == '"' then do
        let (sv, j) ← strEnd (i + 1) ""
        go j stack (SExpr.str sv :: top)
      else
        let j := atomEnd i
        go j stack (SExpr.atom (String.ofList (cs.extract i j).toList) :: top)
    else
      if stack.isEmpty then .ok top.reverse else .error "unbalanced '('"
  go 0 [] []

/-- The value after keyword `:key` in a list. -/
def kw? (key : String) : SExpr → Option SExpr
  | .list xs =>
    let rec find : List SExpr → Option SExpr
      | .atom k :: v :: rest => if k == ":" ++ key then some v else find (v :: rest)
      | _ :: rest => find rest
      | [] => none
    find xs
  | _ => none

partial def toString : SExpr → String
  | .atom s => s
  | .str s => "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""
  | .list xs => "(" ++ " ".intercalate (xs.map toString) ++ ")"

end SExpr

/-! ## The VIR fragment -/

deriving instance Lean.ToExpr for VModel.IntRange
deriving instance Lean.ToExpr for VModel.VTy

inductive UnOp where
  | not
  | clip (r : IntRange)
  deriving Repr, Lean.ToExpr, Inhabited

inductive BinOp where
  | add | sub | mul | ediv | emod
  /-- `&`, `>>` and `^`, on unsigned integers only. -/
  | band | shr | bxor
  | eq | ne | le | lt | ge | gt
  deriving Repr, Lean.ToExpr, Inhabited

inductive LogOp where
  | and | or | implies
  deriving Repr, Lean.ToExpr, Inhabited

/-- The vstd `Seq` operations, which are given meaning in `Sem.lean` (vstd's own recursions). -/
inductive Prim where
  | empty | len | index | push | update | subrange | add | new | last | dropLast | skip | take
  deriving Repr, Lean.ToExpr, Inhabited, DecidableEq

/-- VIR expressions in the fragment. -/
inductive Expr where
  | int (i : Int)
  | bool (b : Bool)
  | var (x : String)
  /-- Field `i` of a tuple (VIR `FieldOpr` on `Tuple n`). -/
  | tupField (e : Expr) (i : Nat)
  /-- Field 0 of `Some`, without a variant check; `t` is the field's type. -/
  | someField (e : Expr) (t : VTy)
  /-- A `Block` statement `let x = init;`, then the rest. -/
  | lett (x : String) (init body : Expr)
  | ite (c t e : Expr)
  /-- A call to a spec function of the program. -/
  | call (f : String) (args : List Expr)
  /-- A call to a vstd `Seq` operation, with its element type. -/
  | prim (p : Prim) (t : VTy) (args : List Expr)
  | tuple (es : List Expr)
  | some (e : Expr)
  | none
  /-- A one-parameter spec closure (`Seq::new`'s argument). -/
  | lam (x : String) (body : Expr)
  /-- `exists|x: t| body` and `forall|x: t| body`. -/
  | ex (x : String) (t : VTy) (body : Expr)
  | all (x : String) (t : VTy) (body : Expr)
  | un (op : UnOp) (e : Expr)
  | bin (op : BinOp) (a b : Expr)
  | log (op : LogOp) (a b : Expr)
  | isSome (e : Expr)
  | isNone (e : Expr)
  /-- `IsVariant` on a tuple: always true. -/
  | isTuple (e : Expr)
  deriving Repr, Lean.ToExpr, Inhabited

structure FnDef where
  name : String
  params : List (String × VTy)
  ret : VTy
  body : Expr
  deriving Repr, Lean.ToExpr, Inhabited

abbrev Prog := List FnDef

/-! ## From VIR S-expressions -/

namespace Conv

open SExpr

def fail {α : Type} (what : String) (e : SExpr) : Except String α :=
  .error s!"{what}: {(e.toString).take 300}"

def intRange : SExpr → Except String IntRange
  | .list [.atom "IntRange", .atom "Int"] => .ok .int
  | .list [.atom "IntRange", .atom "Nat"] => .ok .nat
  | .list [.atom "IntRange", .atom "U", .atom n] => .ok (.u n.toNat!)
  | .list [.atom "IntRange", .atom "I", .atom n] => .ok (.i n.toNat!)
  | .list [.atom "IntRange", .atom "USize"] => .ok .usize
  | .list [.atom "IntRange", .atom "ISize"] => .ok .isize
  | e => fail "int range" e

partial def ty : SExpr → Except String VTy
  | .list [.atom "Typ", .atom "Int", r] => return .int (← intRange r)
  | .list [.atom "Typ", .atom "Bool"] => return .bool
  | .list [.atom "Typ", .atom "Decorate", _, t] => ty t
  | .list [.atom "Typ", .atom "Datatype", .list [.atom "Dt", .atom "Path", .atom "vstd::seq::Seq"],
      .list [t], _] => return .seq (← ty t)
  | .list [.atom "Typ", .atom "Datatype", .list [.atom "Dt", .atom "Path", .atom "core::option::Option"],
      .list [t], _] => return .opt (← ty t)
  | .list [.atom "Typ", .atom "Datatype", .list [.atom "Dt", .atom "Tuple", _], .list ts, _] =>
      return .tup (← ts.mapM ty)
  | e => fail "type" e

/-- A variable's name, with its disambiguator, as `vir2lean.py` writes it. -/
def name : SExpr → Except String String
  | .list (.atom "VarIdent" :: .str base :: rest) =>
    let base := base.replace "%" "_"
    let base := if base == "tmp__" then "tmp" else base
    match rest with
    | [.list (.atom "VarIdentDisambiguate" :: _ :: more)] =>
      let suffix := more.map fun
        | .atom a => a
        | .str a => a
        | e => e.toString
      return if suffix.isEmpty then base else base ++ "_" ++ "_".intercalate suffix
    | _ => return base
  | e => fail "variable" e

/-- vstd functions and the `Seq` operation each is. -/
def prim? : String → Option Prim
  | "vstd::seq::Seq::empty" => some .empty
  | "vstd::seq::Seq::len" => some .len
  | "vstd::seq::Seq::index" => some .index
  | "vstd::seq::impl&%2::spec_index" => some .index
  | "vstd::seq::Seq::push" => some .push
  | "vstd::seq::Seq::update" => some .update
  | "vstd::seq::Seq::subrange" => some .subrange
  | "vstd::seq::Seq::add" => some .add
  | "vstd::seq::impl&%2::spec_add" => some .add
  | "vstd::seq::Seq::new" => some .new
  | "vstd::seq::Seq::last" => some .last
  | "vstd::seq_lib::impl&%0::drop_last" => some .dropLast
  | "vstd::seq::impl&%2::skip" => some .skip
  | "vstd::seq::impl&%2::take" => some .take
  | _ => none

/-- The unsigned range of an integer VIR type. -/
def unsigned? (t : SExpr) : Option IntRange :=
  match ty t with
  | .ok (.int (.u n)) => some (.u n)
  | .ok (.int .usize) => some .usize
  | _ => none

/-- The type of a typed expression `(@@ e t)`. -/
def tyOf : SExpr → SExpr
  | .list [.atom "@@", _, t] => t
  | e => e

/-- A non-negative integer constant, of any integer type: the amount in `c >> 1`, which
Rust types as `i32`. -/
def nonnegConst : SExpr → Bool
  | .list [.atom "@@", .list [.atom ">", .atom "Const", .list [.atom "Constant", .atom "Int", .atom n]], _] =>
    n.toNat?.isSome
  | _ => false

mutual

partial def place : SExpr → Except String Expr
  | .list [.atom "@@", p, t] => placeT p (some t)
  | p => placeT p none

partial def placeT (p : SExpr) (t : Option SExpr) : Except String Expr :=
  match p with
  | .list [.atom "Place", .atom "Local", v] => return .var (← name v)
  | .list [.atom "Place", .atom "Temporary", e] => expr e
  | .list [.atom "Place", .atom "Field", fo, inner] => do
    let x ← place inner
    let some dt := fo.kw? "datatype" | fail "field" fo
    let some (.str field) := fo.kw? "field" | fail "field" fo
    let some (.str variant) := fo.kw? "variant" | fail "field" fo
    let some check := fo.kw? "check" | fail "field" fo
    if check != .list [.atom "VariantCheck", .atom "None"] then fail "field check" fo else
    match dt with
    | .list [.atom "Dt", .atom "Tuple", _] => return .tupField x field.toNat!
    | .list [.atom "Dt", .atom "Path", .atom "core::option::Option"] =>
      if variant == "Some" && field == "0" then
        match t with
        | some t => return .someField x (← ty t)
        | none => fail "untyped Some field" p
      else fail "Option field" fo
    | _ => fail "field datatype" fo
  | e => fail "place" e

partial def expr : SExpr → Except String Expr
  | .list [.atom "@@", .list (.atom ">" :: .atom k :: a), t] => node k a t
  | e => fail "typed expression" e

partial def node (k : String) (a : List SExpr) (t : SExpr) : Except String Expr := do
  let e := SExpr.list (.atom ">" :: .atom k :: a)
  match k, a with
  | "Const", [.list [.atom "Constant", .atom "Int", .atom n]] =>
    match n.toInt? with
    | some i => return .int i
    | none => fail "integer" e
  | "Const", [.list [.atom "Constant", .atom "Bool", .atom "true"]] => return .bool true
  | "Const", [.list [.atom "Constant", .atom "Bool", .atom "false"]] => return .bool false
  | "ReadPlace", p :: _ => place p
  | "Var", [v] => return .var (← name v)
  | "Block", [.list stmts, body] =>
    let b ← expr body
    stmts.foldrM (fun st acc => stmt st acc) b
  | "If", [c, th, el] =>
    if el == .atom "None" then fail "if without else" e
    else return .ite (← expr c) (← expr th) (← expr el)
  | "Call", _ => do
    let some tgt := e.kw? "target" | fail "call" e
    let some (.list args) := e.kw? "args" | fail "call" e
    let xs ← args.mapM expr
    match tgt with
    | .list (.atom "CallTarget" :: .atom "Fun" :: _ :: .list [.atom "Fun", .atom ":path", .atom path] ::
        .list targs :: _) =>
      match prim? path with
      | some p =>
        match targs with
        | [ta] => return .prim p (← ty ta) xs
        | _ => fail "vstd call without its element type" tgt
      | none =>
        if path.startsWith "vstd::" then fail "vstd function not in the model" tgt
        else return .call path xs
    | _ => fail "call target" tgt
  | "Ctor", dt :: .str variant :: .list fields :: _ => do
    let vals ← fields.mapM fun
      | .list [.atom "->", .atom i, v] => do return (i.toNat!, ← expr v)
      | .list [.atom "->", .str i, v] => do return (i.toNat!, ← expr v)
      | f => fail "constructor field" f
    let vals := (vals.toArray.qsort (fun x y => x.1 < y.1)).toList
    match dt with
    | .list [.atom "Dt", .atom "Tuple", _] => return .tuple (vals.map (·.2))
    | .list [.atom "Dt", .atom "Path", .atom "core::option::Option"] =>
      if variant == "Some" then
        match vals with
        | [(0, v)] => return .some v
        | _ => fail "Some" e
      else if variant == "None" then return .none
      else fail "Option variant" e
    | _ => fail "constructor" e
  | "Closure", [.list [.list [.atom "->", v, vt]], body] => do
    let _ ← ty vt
    return .lam (← name v) (← expr body)
  | "Quant", [.list [.atom q], .list [.list [.atom "->", v, vt]], body] => do
    match q with
    | "Exists" => return .ex (← name v) (← ty vt) (← expr body)
    | "Forall" => return .all (← name v) (← ty vt) (← expr body)
    | _ => fail "quantifier" e
  -- triggers only guide Verus's SMT instantiation
  | "WithTriggers", _ => do
    let some body := e.kw? "body" | fail "WithTriggers" e
    expr body
  | "Unary", [.list (.atom "UnaryOp" :: .atom "Trigger" :: _), x] => expr x
  | "Unary", [.list [.atom "UnaryOp", .atom "Not"], x] => return .un .not (← expr x)
  | "Unary", [op@(.list (.atom "UnaryOp" :: .atom "Clip" :: _)), x] => do
    -- `truncate` changes only what Verus checks, not the value (sst_to_air.rs)
    let some r := op.kw? "range" | fail "clip" op
    return .un (.clip (← intRange r)) (← expr x)
  | "UnaryOpr", [op@(.list (.atom "UnaryOpr" :: .atom "IsVariant" :: _)), x] => do
    let some dt := op.kw? "datatype" | fail "IsVariant" op
    let some (.str variant) := op.kw? "variant" | fail "IsVariant" op
    match dt with
    | .list [.atom "Dt", .atom "Tuple", _] => return .isTuple (← expr x)
    | .list [.atom "Dt", .atom "Path", .atom "core::option::Option"] =>
      if variant == "Some" then return .isSome (← expr x)
      else if variant == "None" then return .isNone (← expr x)
      else fail "IsVariant" op
    | _ => fail "IsVariant datatype" op
  | "Binary", [op, x, y] => do
    let a ← expr x
    let b ← expr y
    match op with
    | .list [.atom "BinaryOp", .atom "Arith", .list [.atom "ArithOp", .atom o, ob]] =>
      if o == "Add" || o == "Sub" || o == "Mul" then do
        let op := if o == "Add" then BinOp.add else if o == "Sub" then .sub else .mul
        -- `Truncate r` and `Error r` clip the result to `r` (ast_to_sst.rs)
        match ob with
        | .list [.atom "OverflowBehavior", .atom "Allow"] => return .bin op a b
        | .list [.atom "OverflowBehavior", .atom "Truncate", r]
        | .list [.atom "OverflowBehavior", .atom "Error", r] =>
          match ← intRange r with
          | .int => return .bin op a b
          | r => return .un (.clip r) (.bin op a b)
        | _ => fail "overflow behavior" ob
      else match o, ob with
        | "EuclideanDiv", .list [.atom "Div0Behavior", .atom "Allow"] => return .bin .ediv a b
        | "EuclideanMod", .list [.atom "Div0Behavior", .atom "Allow"] => return .bin .emod a b
        | _, _ => fail "binary operator" op
    | .list [.atom "BinaryOp", .atom "Bitwise", .list [.atom "BitwiseOp", .atom o],
        .list [.atom "BitshiftBehavior", .atom "Allow"]] => do
      -- Verus clips the result to its type (`clip_bitwise_result`, sst_to_air.rs)
      let some r := unsigned? t | fail "bitwise operator on a signed or non-integer type" e
      -- the amount of a `>>` may also be a non-negative constant of a signed type
      if !((unsigned? (tyOf x)).isSome &&
          ((unsigned? (tyOf y)).isSome || (o == "Shr" && nonnegConst y))) then
        fail "bitwise operand of a signed or non-integer type" e else
      match o with
      | "BitAnd" => return .un (.clip r) (.bin .band a b)
      | "Shr" => return .un (.clip r) (.bin .shr a b)
      | "BitXor" => return .un (.clip r) (.bin .bxor a b)
      | _ => fail "bitwise operator" op
    | .list [.atom "BinaryOp", .atom "Eq", .atom "Spec"] => return .bin .eq a b
    | .list [.atom "BinaryOp", .atom "Ne"] => return .bin .ne a b
    | .list [.atom "BinaryOp", .atom "Inequality", .list [.atom "InequalityOp", .atom "Le"]] => return .bin .le a b
    | .list [.atom "BinaryOp", .atom "Inequality", .list [.atom "InequalityOp", .atom "Lt"]] => return .bin .lt a b
    | .list [.atom "BinaryOp", .atom "Inequality", .list [.atom "InequalityOp", .atom "Ge"]] => return .bin .ge a b
    | .list [.atom "BinaryOp", .atom "Inequality", .list [.atom "InequalityOp", .atom "Gt"]] => return .bin .gt a b
    | _ => fail "binary operator" op
  | "Logical", [.list [.atom "LogicalOp", .atom op], x, y] => do
    let a ← expr x
    let b ← expr y
    match op with
    | "And" => return .log .and a b
    | "Or" => return .log .or a b
    | "Implies" => return .log .implies a b
    | _ => fail "logical operator" e
  | _, _ => let _ := t; fail s!"expression kind {k}" e

partial def stmt (st : SExpr) (body : Expr) : Except String Expr := do
  match st with
  | .list (.atom "Stmt" :: .atom "Decl" :: _) =>
    let some pat := st.kw? "pattern" | fail "declaration" st
    let some init := st.kw? "init" | fail "declaration" st
    if init == .atom "None" then fail "declaration without value" st else
    let pat := match pat with
      | .list [.atom "@@", p, _] => p
      | p => p
    match pat with
    | .list [.atom "Pattern", .atom "Var", b] =>
      let some v := b.kw? "name" | fail "pattern" pat
      return .lett (← name v) (← place init) body
    | _ => fail "pattern" pat
  | _ => fail "statement" st

end

/-- A spec function: its path, parameters, return type and body. -/
def fn (f : SExpr) : Except String FnDef := do
  let some (.list [.atom "Fun", .atom ":path", .atom path]) := f.kw? "name" | fail "function name" f
  let some (.atom "Spec") := f.kw? "mode" | fail "not a spec function" f
  let some (.list []) := f.kw? "typ_params" | fail "generic function" f
  let some (.list params) := f.kw? "params" | fail "parameters" f
  let some ret := f.kw? "ret" | fail "return" f
  let some body := f.kw? "body" | fail "body" f
  if body == .atom "None" then fail "no body" f else
  let ps ← params.mapM fun q => do
    let some v := q.kw? "name" | fail "parameter" q
    let some t := q.kw? "typ" | fail "parameter" q
    return (← name v, ← ty t)
  let some rt := ret.kw? "typ" | fail "return type" ret
  return { name := path, params := ps, ret := ← ty rt, body := ← expr body }

end Conv

/-- Every function in a VIR dump, converted. -/
def readProg (text : String) : Except String Prog := do
  let items ← SExpr.parseMany text
  items.filterMapM fun it =>
    match it with
    | .list (.atom "Function" :: _) => return some (← Conv.fn it)
    | _ => return none

end VIR
