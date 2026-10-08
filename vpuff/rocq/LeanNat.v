(* Lean's natural numbers, booleans and arrays as imported, related to Rocq's Z.

   The imported Lean operations are Lean's own definitions (structural recursion
   compiled to recursors), so one-step equations hold by conversion and
   everything else follows by induction. Division, modulus and testBit go through
   the Lean theorems exported in PuffExport.lean. Lean's propositions are SProps
   here; equality can be turned into Rocq's (of_leq), and Lean.v provides the
   same for <=. *)
From LeanImport Require Import Lean.
Require Import VPuff.LeanSpec.
Close Scope Nat_scope. Close Scope lean_scope.
From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(** * Lean's operations as they appear in imported terms *)

Notation "a +L b" := (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) a b)
  (at level 50, left associativity).
Notation "a -L b" := (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) a b)
  (at level 50, left associativity).
Notation "a *L b" := (HMul_hMul_inst7 Nat Nat Nat (instHMul_inst1 Nat instMulNat) a b)
  (at level 40, left associativity).
Notation "a /L b" := (HDiv_hDiv_inst7 Nat Nat Nat (instHDiv_inst1 Nat Nat_instDiv) a b)
  (at level 40, left associativity).
Notation "a %L b" := (HMod_hMod_inst7 Nat Nat Nat (instHMod_inst1 Nat Nat_instMod) a b)
  (at level 40, left associativity).
Notation "a ^L b" := (HPow_hPow_inst7 Nat Nat Nat
  (instHPow_inst3 Nat Nat (instPowNat_inst1 Nat instNatPowNat)) a b) (at level 30, right associativity).
(* a Lean numeral; n is a Lean Nat *)
Notation "'L#' n" := (OfNat_ofNat_inst1 Nat n (instOfNatNat n)) (at level 1, n at level 0).

(** * Values *)

(* a Lean Nat as a Z, and back *)
Definition V (x : Nat) : Z := Z.of_nat (nat_of_Nat x).
Definition LN (z : Z) : Nat := Nat_of_nat (Z.to_nat z).

Lemma V_nonneg x : 0 <= V x.
Proof. unfold V; lia. Qed.

Lemma V_LN z : 0 <= z -> V (LN z) = z.
Proof. intros; unfold V, LN; rewrite nat2Natid; lia. Qed.

Lemma LN_V x : LN (V x) = x.
Proof. unfold V, LN; rewrite Nat2Z.id, Nat2natid; reflexivity. Qed.

Lemma V_inj x y : V x = V y -> x = y.
Proof. intros H; rewrite <- (LN_V x), <- (LN_V y), H; reflexivity. Qed.

Lemma V_zero : V Nat_zero = 0.
Proof. reflexivity. Qed.

Lemma V_succ x : V (Nat_succ x) = V x + 1.
Proof. unfold V; cbn [nat_of_Nat]; lia. Qed.

Lemma lit_eq n : L# n = n.
Proof. reflexivity. Qed.

(* Lean literals: evaluate V of them *)
Ltac vlits :=
  repeat match goal with
  | |- context [V (OfNat_ofNat_inst1 Nat ?n ?i)] =>
      let e := eval lazy in (V (OfNat_ofNat_inst1 Nat n i)) in
      change (V (OfNat_ofNat_inst1 Nat n i)) with e
  | H : context [V (OfNat_ofNat_inst1 Nat ?n ?i)] |- _ =>
      let e := eval lazy in (V (OfNat_ofNat_inst1 Nat n i)) in
      change (V (OfNat_ofNat_inst1 Nat n i)) with e in H
  | |- context [nat_of_Nat (OfNat_ofNat_inst1 Nat ?n ?i)] =>
      let e := eval lazy in (nat_of_Nat (OfNat_ofNat_inst1 Nat n i)) in
      change (nat_of_Nat (OfNat_ofNat_inst1 Nat n i)) with e
  end.

Lemma V_Nat_of_nat n : V (Nat_of_nat n) = Z.of_nat n.
Proof. unfold V; rewrite nat2Natid; reflexivity. Qed.

(** * Equality *)

Definition of_leq {A : Type} {a b : A} (h : eq a b) : a = b :=
  match h in eq _ y return a = y with eq_refl _ => Logic.eq_refl end.

Definition to_leq {A : Type} {a b : A} (h : a = b) : eq a b :=
  match h in Logic.eq _ y return eq a y with Logic.eq_refl => eq_refl a end.

(** * Arithmetic *)

Lemma add_zero a : a +L Nat_zero = a.
Proof. reflexivity. Qed.
Lemma add_succ a b : a +L Nat_succ b = Nat_succ (a +L b).
Proof. reflexivity. Qed.

Lemma V_add a b : V (a +L b) = V a + V b.
Proof.
  induction b as [|b IH].
  - rewrite add_zero, V_zero; lia.
  - rewrite add_succ, !V_succ, IH; lia.
Qed.

Lemma succ_add_one a : Nat_succ a = a +L L# (Nat_succ Nat_zero).
Proof. reflexivity. Qed.

Lemma sub_zero a : a -L Nat_zero = a.
Proof. reflexivity. Qed.
Lemma sub_succ a b : a -L Nat_succ b = Nat_pred (a -L b).
Proof. reflexivity. Qed.
Lemma V_pred a : V (Nat_pred a) = Z.max 0 (V a - 1).
Proof. destruct a; [reflexivity|]. change (Nat_pred (Nat_succ a)) with a. rewrite V_succ. pose proof (V_nonneg a); lia. Qed.

Lemma V_sub a b : V (a -L b) = Z.max 0 (V a - V b).
Proof.
  induction b as [|b IH].
  - rewrite sub_zero, V_zero; pose proof (V_nonneg a); lia.
  - rewrite sub_succ, V_pred, IH, V_succ; lia.
Qed.

Lemma mul_zero a : a *L Nat_zero = Nat_zero.
Proof. reflexivity. Qed.
Lemma mul_succ a b : a *L Nat_succ b = (a *L b) +L a.
Proof. reflexivity. Qed.

Lemma V_mul a b : V (a *L b) = V a * V b.
Proof.
  induction b as [|b IH].
  - rewrite mul_zero, V_zero; lia.
  - rewrite mul_succ, V_add, IH, V_succ; lia.
Qed.

Lemma pow_zero a : a ^L Nat_zero = Nat_succ Nat_zero.
Proof. reflexivity. Qed.
Lemma pow_succ a b : a ^L Nat_succ b = (a ^L b) *L a.
Proof. reflexivity. Qed.

Lemma V_pow a b : V (a ^L b) = V a ^ V b.
Proof.
  induction b as [|b IH].
  - rewrite pow_zero, V_succ, V_zero; reflexivity.
  - rewrite pow_succ, V_mul, IH, V_succ, Z.pow_add_r by (apply V_nonneg || lia); lia.
Qed.

(** * Comparisons *)

Definition B2b (b : Bool) : bool := match b with Bool_true => true | Bool_false => false end.

Lemma ble_zero b : Nat_ble Nat_zero b = Bool_true.
Proof. destruct b; reflexivity. Qed.
Lemma ble_succ_zero a : Nat_ble (Nat_succ a) Nat_zero = Bool_false.
Proof. reflexivity. Qed.
Lemma ble_succ_succ a b : Nat_ble (Nat_succ a) (Nat_succ b) = Nat_ble a b.
Proof. reflexivity. Qed.

Lemma B2b_ble a b : B2b (Nat_ble a b) = (V a <=? V b).
Proof.
  revert b; induction a as [|a IH]; intros b.
  - rewrite ble_zero, V_zero; cbn; symmetry; apply Z.leb_le, V_nonneg.
  - destruct b as [|b].
    + rewrite ble_succ_zero, V_succ, V_zero; cbn; pose proof (V_nonneg a).
      symmetry; apply Z.leb_gt; lia.
    + rewrite ble_succ_succ, IH, !V_succ.
      destruct (V a <=? V b) eqn:E1, (V a + 1 <=? V b + 1) eqn:E2; auto;
        rewrite ?Z.leb_le, ?Z.leb_gt in *; lia.
Qed.

Lemma B2b_blt a b : B2b (Nat_blt a b) = (V a <? V b).
Proof.
  change (Nat_blt a b) with (Nat_ble (Nat_succ a) b).
  rewrite B2b_ble, V_succ.
  destruct (V a + 1 <=? V b) eqn:E1, (V a <? V b) eqn:E2; auto;
    rewrite ?Z.leb_le, ?Z.leb_gt, ?Z.ltb_lt, ?Z.ltb_ge in *; lia.
Qed.

Lemma beq_zero_zero : Nat_beq Nat_zero Nat_zero = Bool_true.
Proof. reflexivity. Qed.
Lemma beq_zero_succ b : Nat_beq Nat_zero (Nat_succ b) = Bool_false.
Proof. reflexivity. Qed.
Lemma beq_succ_zero a : Nat_beq (Nat_succ a) Nat_zero = Bool_false.
Proof. reflexivity. Qed.
Lemma beq_succ_succ a b : Nat_beq (Nat_succ a) (Nat_succ b) = Nat_beq a b.
Proof. reflexivity. Qed.

Lemma B2b_beq a b : B2b (Nat_beq a b) = (V a =? V b).
Proof.
  revert b; induction a as [|a IH]; intros [|b].
  - reflexivity.
  - rewrite beq_zero_succ, V_succ, V_zero; pose proof (V_nonneg b).
    symmetry; apply Z.eqb_neq; lia.
  - rewrite beq_succ_zero, V_succ, V_zero; pose proof (V_nonneg a).
    symmetry; apply Z.eqb_neq; lia.
  - rewrite beq_succ_succ, IH, !V_succ.
    destruct (V a =? V b) eqn:E1, (V a + 1 =? V b + 1) eqn:E2; auto;
      rewrite ?Z.eqb_eq, ?Z.eqb_neq in *; lia.
Qed.

Lemma B2b_inj a b : B2b a = B2b b -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.

(* Lean's <= and < (SProp) and Rocq's *)
Lemma le_V a b : LE_le_inst1 Nat instLENat a b -> V a <= V b.
Proof. intros H; apply Nat_le_nat_le' in H; unfold V; lia. Qed.

Lemma lt_V a b : LT_lt_inst1 Nat instLTNat a b -> V a < V b.
Proof.
  intros H. change (LE_le_inst1 Nat instLENat (Nat_succ a) b) in H.
  apply le_V in H; rewrite V_succ in H; lia.
Qed.

(** * Division and modulus, through Lean's theorems *)

Lemma V_divmod a b : 0 < V b -> V (a /L b) = V a / V b /\ V (a %L b) = V a mod V b.
Proof.
  intros Hb.
  pose proof (of_leq (Deflate_Puff_Export_div_add_mod a b)) as E.
  apply (f_equal V) in E; rewrite V_add, V_mul in E.
  assert (Hlt : V (a %L b) < V b).
  { assert (H1 : B2b (Nat_ble (L# (Nat_succ Nat_zero)) b) = true)
      by (rewrite B2b_ble; vlits; apply Z.leb_le; lia).
    pose proof (of_leq (Deflate_Puff_Export_mod_lt a b (to_leq (B2b_inj _ Bool_true H1)))) as H2.
    apply (f_equal B2b) in H2; rewrite B2b_ble, V_add in H2; cbn [B2b] in H2.
    vlits; apply Z.leb_le in H2; lia. }
  pose proof (V_nonneg (a %L b)); pose proof (V_nonneg (a /L b)).
  assert (Hd : V (a /L b) = V a / V b).
  { apply Z.div_unique_pos with (V (a %L b)); lia. }
  split; [exact Hd|].
  rewrite Zmod_eq_full by lia; rewrite <- Hd; lia.
Qed.

Lemma V_div a b : 0 < V b -> V (a /L b) = V a / V b.
Proof. intros H; apply (V_divmod a b H). Qed.
Lemma V_mod a b : 0 < V b -> V (a %L b) = V a mod V b.
Proof. intros H; apply (V_divmod a b H). Qed.

Lemma V_lit2 : V (L# (Nat_succ (Nat_succ Nat_zero))) = 2.
Proof. reflexivity. Qed.

Lemma B2b_testBit x i : B2b (Nat_testBit x i) = Z.testbit (V x) (V i).
Proof.
  rewrite (of_leq (Deflate_Puff_Export_testBit_eq x i)), B2b_beq.
  assert (Hp : 0 < V (L# (Nat_succ (Nat_succ Nat_zero)) ^L i))
    by (rewrite V_pow, V_lit2; apply Z.pow_pos_nonneg; [lia | apply V_nonneg]).
  rewrite V_mod by (rewrite V_lit2; lia).
  rewrite V_div by exact Hp.
  rewrite V_pow, V_lit2.
  vlits.
  rewrite Z.testbit_eqb by apply V_nonneg.
  reflexivity.
Qed.

(** * Lean's cond *)
#[universes(polymorphic)]
Lemma cond_true {A : Type} (x y : A) : cond A Bool_true x y = x.
Proof. reflexivity. Qed.
#[universes(polymorphic)]
Lemma cond_false {A : Type} (x y : A) : cond A Bool_false x y = y.
Proof. reflexivity. Qed.
