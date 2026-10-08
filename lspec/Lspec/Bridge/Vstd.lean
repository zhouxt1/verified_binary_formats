import Lspec.VIR.Ty

/-!
# The shallow model of Verus spec code, and vstd's `Seq` recursions

Two things live here.

**Trusted:** vstd's `Seq` operations, `len`, `indexWith`, `push`, `updateWith`,
`subrange`, `add`, `newWith` and `dropLast`, and `IntRange.contains`. The VIR semantics
(`Lspec/VIR/Sem.lean`) uses them for `Seq` values. vstd 0.0.0-2026-09-20-0158 defines
`Seq<A>` as a list (`seq.rs`: `tracked enum SeqInner<A> { Nil, Cons { head, tail } }`, with
`Seq { inner }`), and its operations by recursion on it, and these definitions are those
recursions, case for case. The `*With` forms take the `arbitrary()` value a recursion
returns as an argument.

**Not trusted:** the shallow model, which is everything else here. The generated definitions
of `VDeflate.lean` are written against it: integers as `Int`, `Seq` as `List`, and Verus's
unspecified values as a parameter `u : Unspec`. The unspecified values are:

* `arbitrary::<A>()`, per VIR type;
* out-of-range casts (`u.clip`);
* division by zero (`u.div0`, `u.mod0`).

Integer parameters carry their types' ranges, so Lean sees termination by Verus's own
measures. `VDeflateValid.lean` proves that each generated definition computes what the VIR
semantics gives Verus's VIR, for the oracle `VIR.Oracle.ofUnspec u`. So nothing about the
shallow model has to be taken on trust.
-/

namespace VModel

/-- Whether `x` is in a range. `usize`/`isize` are taken as 64 bits. -/
def IntRange.contains : IntRange → Int → Bool
  | .int, _ => true
  | .nat, x => 0 ≤ x
  | .u n, x => 0 ≤ x && x < 2 ^ n
  | .i n, x => -(2 ^ (n - 1)) ≤ x && x < 2 ^ (n - 1)
  | .usize, x => 0 ≤ x && x < 2 ^ 64
  | .isize, x => -(2 ^ 63) ≤ x && x < 2 ^ 63

/-- The values Verus leaves unspecified. -/
structure Unspec where
  /-- `arbitrary::<A>()`, for each VIR type `A`. -/
  arb : (τ : VTy) → τ.denote
  /-- `x as T` for `x` outside `T`'s range. -/
  clip : IntRange → Int → Int
  /-- It lands in the range (the prelude's `u_clip`/`i_clip`/`nat_clip` axioms). -/
  clip_ok : ∀ (r : IntRange) (x : Int), IntRange.contains r (clip r x) = true
  /-- `x / 0` and `x % 0`. -/
  div0 : Int → Int
  mod0 : Int → Int

/-- A spec-mode cast (VIR `Clip`): the value itself when in range. Verus
(commit aef82ed) encodes `Clip` as `nat_clip`/`u_clip`/`i_clip`
(`vir/src/sst_to_air.rs`, whatever its `truncate` flag). Its prelude
(`vir/src/prelude.rs`) says only that these are the identity in range and land
in range otherwise. -/
def clip (u : Unspec) (r : IntRange) (x : Int) : Int :=
  if r.contains x then x else u.clip r x

/-- VIR `EuclideanDiv` with `Div0Behavior Allow`. Verus encodes it as
`EucDiv`, with the prelude axiom `EucDiv x y = div x y` (SMT-LIB's Euclidean
`div`, unspecified for `y = 0`). Lean's `Int` division is Euclidean too. -/
def ediv (u : Unspec) (x y : Int) : Int := if y = 0 then u.div0 x else x / y

/-- VIR `EuclideanMod` with `Div0Behavior Allow`: `EucMod x y = mod x y`. -/
def emod (u : Unspec) (x y : Int) : Int := if y = 0 then u.mod0 x else x % y

/-- Bitwise `&` on unsigned integers. -/
def band (x y : Int) : Int := ((x.toNat &&& y.toNat : Nat) : Int)

/-- `^` on unsigned integers, clipped like `&` (`clip_bitwise_result`, sst_to_air.rs). -/
def bxor (x y : Int) : Int := ((x.toNat ^^^ y.toNat : Nat) : Int)

/-- `>>` on unsigned integers. -/
def shr (x y : Int) : Int := ((x.toNat >>> y.toNat : Nat) : Int)

mutual
/-- A shallow value of VIR type `τ`: integers in their ranges. Quantifiers range over these. -/
def VTy.wt : (τ : VTy) → τ.denote → Prop
  | .int r, x => r.contains x = true
  | .bool, _ => True
  | .seq t, xs => ∀ x ∈ xs, VTy.wt t x
  | .opt t, o => ∀ x ∈ o, VTy.wt t x
  | .tup ts, x => VTy.wtTup ts x
def VTy.wtTup : (ts : List VTy) → VTy.denoteTup ts → Prop
  | [], _ => True
  | [t], x => VTy.wt t x
  | t :: t2 :: ts, x => VTy.wt t x.1 ∧ VTy.wtTup (t2 :: ts) x.2
end

/-- `arbitrary::<A>()` at the VIR type `τ`, seen at the Lean type it denotes. -/
def arbAt (u : Unspec) (τ : VTy) {α : Type} (h : τ.denote = α) : α := h ▸ u.arb τ

/-- Reading field 0 of `Some` (VIR `FieldOpr` with `VariantCheck None`). On
`None` it is the datatype selector applied to the wrong variant, so
unspecified. -/
def someVal (u : Unspec) (τ : VTy) {α : Type} (h : τ.denote = α) : Option α → α
  | some x => x
  | none => arbAt u τ h

namespace Seq

/-- `Seq::empty`: `Seq { inner: SeqInner::Nil }`. -/
def empty {α : Type} : List α := []

/-- `Seq::len`, `SeqInner::len`: `Nil => 0`, `Cons { tail, .. } => 1 + tail.len()`. -/
def len {α : Type} : List α → Int
  | [] => 0
  | _ :: t => 1 + len t

/-- `Seq::index`, `SeqInner::index`: `Nil => arbitrary()` (here `d`),
`Cons { head, tail } => if i == 0 { head } else { tail.index(i - 1) }`. -/
def indexWith {α : Type} (d : α) : List α → Int → α
  | [], _ => d
  | x :: t, i => if i = 0 then x else indexWith d t (i - 1)

/-- `Seq::index` at element type `τ`: `indexWith` with `arbitrary::<τ>()`. -/
def index (u : Unspec) (τ : VTy) {α : Type} (h : τ.denote = α) (s : List α) (i : Int) : α :=
  indexWith (arbAt u τ h) s i

/-- `Seq::push`, `SeqInner::push`: append at the end. -/
def push {α : Type} : List α → α → List α
  | [], a => [a]
  | h :: t, a => h :: push t a

/-- `Seq::update`, `SeqInner::update`: `self` if `!(0 <= i < self.len())`,
else replace entry `i`. -/
def updateWith {α : Type} (d : List α) (s : List α) (i : Int) (a : α) : List α :=
  if ¬(0 ≤ i ∧ i < len s) then s
  else go s i
where
  go : List α → Int → List α
    | [], _ => d
    | x :: t, i => if i = 0 then a :: t else x :: go t (i - 1)

/-- `Seq::update` at element type `τ`. vstd's `Nil => arbitrary()` in it is at
`SeqInner<A>`; it is never reached (the guard), and taken here at `Seq<A>`. -/
def update (u : Unspec) (τ : VTy) {α : Type} (h : τ.denote = α) (s : List α) (i : Int)
    (a : α) : List α :=
  updateWith (arbAt u (.seq τ) (congrArg List h)) s i a

/-- `Seq::subrange`, `SeqInner::subrange`:
`Nil => Nil`; `Cons` with `start > 0` drops the head and shifts both bounds
down by one; otherwise `end <= 0` gives `Nil`, else the head is kept and the
end shifts down by one. -/
def subrange {α : Type} : List α → Int → Int → List α
  | [], _, _ => []
  | h :: t, i, j =>
    if i > 0 then subrange t (i - 1) (j - 1)
    else if j ≤ 0 then []
    else h :: subrange t i (j - 1)

/-- `Seq::add`, `SeqInner::add`: `Nil => rhs`, `Cons` keeps the head. -/
def add {α : Type} : List α → List α → List α
  | [], r => r
  | h :: t, r => h :: add t r

/-- `Seq::new(len: nat, f)`: `if len == 0 { empty } else
{ new((len - 1) as nat, f).push(f(len - 1)) }`. `len` is a `nat` in Verus.
For a negative `len` (which no Verus value is), it is unspecified here. -/
def newWith {α : Type} (d : List α) (len : Int) (f : Int → α) : List α :=
  if len < 0 then d else go len.toNat
where
  go : Nat → List α
    | 0 => []
    | n + 1 => push (go n) (f n)

/-- `Seq::new` at element type `τ`. -/
def new (u : Unspec) (τ : VTy) {α : Type} (h : τ.denote = α) (len : Int) (f : Int → α) :
    List α :=
  newWith (arbAt u (.seq τ) (congrArg List h)) len f

/-- `Seq::last` (open): `self[self.len() as int - 1]`. -/
def last (u : Unspec) (τ : VTy) {α : Type} (h : τ.denote = α) (s : List α) : α :=
  index u τ h s (len s - 1)

/-- `Seq::drop_last` (open, `seq_lib.rs`): `self.subrange(0, self.len() as int - 1)`. -/
def dropLast {α : Type} (s : List α) : List α := subrange s 0 (len s - 1)

/-- vstd's `skip(n)`: `self.subrange(n, self.len() as int)`. -/
def skip {α : Type} (s : List α) (n : Int) : List α := subrange s n (len s)

/-- vstd's `take(n)`: `self.subrange(0, n)`. -/
def take {α : Type} (s : List α) (n : Int) : List α := subrange s 0 n

theorem len_eq {α : Type} (s : List α) : len s = s.length := by
  induction s with
  | nil => rfl
  | cons h t ih => simp [len, ih]; omega

theorem len_nonneg {α : Type} (s : List α) : 0 ≤ len s := by rw [len_eq]; omega

theorem push_eq {α : Type} (s : List α) (a : α) : push s a = s ++ [a] := by
  induction s with
  | nil => rfl
  | cons h t ih => simp [push, ih]

theorem add_eq {α : Type} (s t : List α) : add s t = s ++ t := by
  induction s with
  | nil => rfl
  | cons h r ih => simp [add, ih]

theorem len_push {α : Type} (s : List α) (a : α) : len (push s a) = len s + 1 := by
  simp [len_eq, push_eq]

theorem len_add {α : Type} (s t : List α) : len (add s t) = len s + len t := by
  simp [len_eq, add_eq]

theorem new_go_length {α : Type} (f : Int → α) (n : Nat) :
    (newWith.go f n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [newWith.go, push_eq, ih]

theorem len_new (u : Unspec) (τ : VTy) {α : Type} (h : τ.denote = α) (n : Int) (f : Int → α)
    (hn : 0 ≤ n) : len (new u τ h n f) = n := by
  simp [new, newWith, len_eq, new_go_length f, show ¬n < 0 by omega]; omega

theorem subrange_length {α : Type} (s : List α) (i j : Int) (h : 0 ≤ i ∧ i ≤ j ∧ j ≤ s.length) :
    (subrange s i j).length = (j - i).toNat := by
  induction s generalizing i j with
  | nil => simp at h; simp [subrange]; omega
  | cons x t ih =>
    simp only [subrange]
    split
    · rw [ih (i - 1) (j - 1) (by simp at h; omega)]; omega
    · split
      · simp; omega
      · simp only [List.length_cons]
        rw [ih i (j - 1) (by simp at h; omega)]; omega

theorem len_subrange {α : Type} (s : List α) (i j : Int) (h : 0 ≤ i ∧ i ≤ j ∧ j ≤ len s) :
    len (subrange s i j) = j - i := by
  rw [len_eq] at h ⊢; rw [subrange_length s i j h]; omega

theorem len_dropLast {α : Type} (s : List α) (h : 1 ≤ len s) : len (dropLast s) = len s - 1 := by
  unfold dropLast; rw [len_subrange s 0 (len s - 1) (by omega)]; omega

theorem len_skip {α : Type} (s : List α) (n : Int) (h : 0 ≤ n ∧ n ≤ len s) : len (skip s n) = len s - n := by
  unfold skip; rw [len_subrange s n (len s) (by omega)]

end Seq

theorem clip_of_contains (u : Unspec) (r : IntRange) (x : Int) (h : r.contains x = true) :
    clip u r x = x := by simp [clip, h]

theorem clip_contains (u : Unspec) (r : IntRange) (x : Int) : r.contains (clip u r x) = true := by
  unfold clip; split
  · assumption
  · exact u.clip_ok r x

theorem contains_nat (x : Int) : IntRange.nat.contains x = decide (0 ≤ x) := rfl

theorem clip_nat (u : Unspec) (x : Int) (h : 0 ≤ x) : clip u .nat x = x :=
  clip_of_contains u _ x (by simp [IntRange.contains, h])

theorem clip_nat_nonneg (u : Unspec) (x : Int) : 0 ≤ clip u .nat x := by
  have := clip_contains u .nat x; simpa [IntRange.contains] using this

end VModel

/-- The termination tactic generated definitions use. It is not trusted: Lean
checks whatever it proves. -/
macro "vir_decreasing" : tactic =>
  `(tactic| first
    | omega
    | (simp_all +zetaDelta [VModel.IntRange.contains, VModel.Seq.len_eq, VModel.Seq.push_eq, VModel.Seq.add_eq,
        VModel.clip]; omega)
    | (simp_all +zetaDelta [VModel.IntRange.contains, VModel.Seq.len_eq, VModel.Seq.push_eq, VModel.Seq.add_eq,
        VModel.clip]; (repeat' split) <;> omega))
