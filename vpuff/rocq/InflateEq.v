(* The Rocq mirror of the spec's inflate (Inflate.v) is the imported Lean spec:
   inflateZ_eq says Inflate.inflateZ bytes is Deflate.inflateBytes on the same
   bytes, read back into Rocq values (lean_inflate).

   Technique, as in Bridge.v: the imported Lean functions are unfolded with
   the exported equations (lspec/Lspec/Deflate/InflateExport.lean), each mirror
   piece is rewritten into V of the Lean piece, and then the Lean subterm is
   destructed on both sides at once. *)
From LeanImport Require Import Lean.
Require Import VPuff.LeanSpec VPuff.LeanNat VPuff.Model VPuff.Bridge VPuff.Inflate.
Close Scope Nat_scope. Close Scope lean_scope.
From Stdlib Require Import ZArith List Lia Bool.
From VST.zlist Require Import sublist.
Import ListNotations.
Open Scope Z_scope.

(** * Small conversions *)

Definition optV (o : Option_inst1 Nat) : option Z :=
  match o with Option_none_inst1 _ => None | Option_some_inst1 _ x => Some (V x) end.

Definition Bb (b : bool) : Bool := if b then Bool_true else Bool_false.

Lemma B2b_Bb b : B2b (Bb b) = b.
Proof. destruct b; reflexivity. Qed.

Lemma B2b_and a b : B2b (Bool_and a b) = B2b a && B2b b.
Proof. destruct a, b; reflexivity. Qed.
Lemma B2b_or a b : B2b (Bool_or a b) = B2b a || B2b b.
Proof. destruct a, b; reflexivity. Qed.
Lemma B2b_not a : B2b (Bool_not a) = negb (B2b a).
Proof. destruct a; reflexivity. Qed.

Definition bytes_ok (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.

Lemma lgetD_toL {A B} (f : A -> B) (l : list A) (dA : Inhabitant A) (i : Nat) (d : B) :
  Deflate_Puff_Export_lgetD B (toL f l) i d =
    if V i <? Zlength l then f (@Znth A dA (V i) l) else d.
Proof.
  revert i; induction l as [|x l IH]; intros i; cbn [toL].
  - rewrite lgetD_nil'; destruct (V i <? Zlength (@nil A)) eqn:E; auto.
    rewrite Zlength_nil in E; pose proof (V_nonneg i); apply Z.ltb_lt in E; lia.
  - destruct i as [|i].
    + rewrite lgetD_zero', V_zero, Zlength_cons.
      pose proof (Zlength_nonneg l).
      destruct (0 <? Z.succ (Zlength l)) eqn:E; [|apply Z.ltb_ge in E; lia].
      rewrite Znth_0_cons; reflexivity.
    + rewrite lgetD_succ', IH, V_succ, Zlength_cons.
      pose proof (V_nonneg i).
      rewrite Znth_pos_cons by lia; replace (V i + 1 - 1) with (V i) by lia.
      destruct (V i <? Zlength l) eqn:E1, (V i + 1 <? Z.succ (Zlength l)) eqn:E2; auto;
        rewrite ?Z.ltb_lt, ?Z.ltb_ge in *; lia.
Qed.

Lemma toL_app {A B} (f : A -> B) (l1 l2 : list A) :
  toL f (l1 ++ l2) =
    HAppend_hAppend_inst7 (List_inst1 B) (List_inst1 B) (List_inst1 B)
      (instHAppendOfAppend_inst1 (List_inst1 B) (List_instAppend_inst1 B)) (toL f l1) (toL f l2).
Proof.
  induction l1 as [|x l1 IH]; cbn [toL app].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** * Bits *)

Lemma lsbVal_zero' b p : Deflate_lsbVal b p Nat_zero = Nat_zero.
Proof. exact (of_leq (Deflate_InflateExport_lsbVal_zero b p)). Qed.
Lemma lsbVal_succ' b p n :
  Deflate_lsbVal b p (Nat_succ n) =
    cond Nat (Array_getD_inst1 Bool b p Bool_false) (L# 1) (L# 0) +L
    L# 2 *L Deflate_lsbVal b (p +L L# 1) n.
Proof. exact (of_leq (Deflate_InflateExport_lsbVal_succ b p n)). Qed.

Lemma bitsOf_size' bytes :
  V (Array_size_inst1 Bool (Deflate_bitsOf (arrU8 bytes))) = nbits bytes.
Proof.
  rewrite (of_leq (Deflate_InflateExport_bitsOf_size _)), V_mul.
  unfold arrU8. rewrite V_size_mk. vlits. unfold nbits. lia.
Qed.

Lemma B2b_bit bytes Q : bytes_ok bytes ->
  B2b (Array_getD_inst1 Bool (Deflate_bitsOf (arrU8 bytes)) Q Bool_false) = bitZ bytes (V Q).
Proof.
  intros Hb.
  rewrite (of_leq (Deflate_InflateExport_bitsOf_getD _ _)).
  destruct (Nat_blt Q _) eqn:E; pose proof (f_equal B2b E) as E'; rewrite B2b_blt, V_mul in E';
    unfold arrU8 in E'; rewrite V_size_mk in E'; vlits; cbn [B2b] in E'.
  - rewrite cond_false. unfold bitZ.
    apply Z.ltb_ge in E'.
    assert (Zlength bytes <= V Q / 8) by (apply Z.div_le_lower_bound; lia).
    rewrite Znth_overflow by lia. symmetry. apply Z.testbit_0_l.
  - rewrite cond_true, byteBit_def', B2b_testBit, V_toNat_getD_arrU8 by auto.
    rewrite V_div, V_mod by (vlits; lia). vlits. reflexivity.
Qed.

Lemma V_lsbVal bytes : bytes_ok bytes -> forall n P,
  V (Deflate_lsbVal (Deflate_bitsOf (arrU8 bytes)) P (Nat_of_nat n)) = lsbZ bytes (V P) n.
Proof.
  intros Hb n; induction n as [|n IH]; intros P.
  - cbn [Nat_of_nat]. rewrite lsbVal_zero'. reflexivity.
  - cbn [Nat_of_nat lsbZ]. rewrite lsbVal_succ', V_add, V_mul, IH, V_add.
    rewrite <- (B2b_bit bytes P Hb).
    destruct (Array_getD_inst1 Bool _ P Bool_false); [rewrite cond_false|rewrite cond_true];
      vlits; cbn [B2b]; lia.
Qed.

Lemma getbits_V bytes P N : bytes_ok bytes ->
  getbitsZ bytes (V P) (V N) = optV (Deflate_getbits (Deflate_bitsOf (arrU8 bytes)) P N).
Proof.
  intros Hb. rewrite (of_leq (Deflate_InflateExport_getbits_eq _ _ _)).
  unfold getbitsZ.
  destruct (Nat_ble (P +L N) _) eqn:E; pose proof (f_equal B2b E) as E';
    rewrite B2b_ble, V_add, bitsOf_size' in E'; cbn [B2b] in E'; rewrite E'.
  - rewrite cond_false. reflexivity.
  - rewrite cond_true. cbn [optV]. f_equal.
    rewrite <- (Nat2natid N) at 2. rewrite V_lsbVal by auto. f_equal.
    unfold V. lia.
Qed.

(** * Byte arrays *)

Lemma push_arrU8 l X :
  Array_push_inst1 UInt8 (arrU8 l) (Nat_toUInt8 X) = arrU8 (l ++ [V X]).
Proof.
  unfold arrU8. rewrite (of_leq (Deflate_InflateExport_push_mk _ _ _)).
  rewrite toL_app. cbn [toL]. rewrite LN_V. reflexivity.
Qed.

Lemma push_arrU8' l z :
  Array_push_inst1 UInt8 (arrU8 l) (UInt8_ofNat (LN z)) = arrU8 (l ++ [z]).
Proof.
  unfold arrU8. rewrite (of_leq (Deflate_InflateExport_push_mk _ _ _)).
  rewrite toL_app. reflexivity.
Qed.

Lemma push_arrN l X : Array_push_inst1 Nat (arrN l) X = arrN (l ++ [V X]).
Proof.
  unfold arrN. rewrite (of_leq (Deflate_InflateExport_push_mk _ _ _)).
  rewrite toL_app. cbn [toL]. rewrite LN_V. reflexivity.
Qed.

Lemma app_arrU8 l1 l2 :
  HAppend_hAppend_inst7 (Array_inst1 UInt8) (Array_inst1 UInt8) (Array_inst1 UInt8)
    (instHAppendOfAppend_inst1 (Array_inst1 UInt8) (Array_instAppend_inst1 UInt8))
    (arrU8 l1) (arrU8 l2) = arrU8 (l1 ++ l2).
Proof.
  unfold arrU8. rewrite (of_leq (Deflate_InflateExport_append_mk _ _ _)), toL_app. reflexivity.
Qed.

Lemma size_arrU8 l : V (Array_size_inst1 UInt8 (arrU8 l)) = Zlength l.
Proof. unfold arrU8. apply V_size_mk. Qed.
Lemma size_arrN l : V (Array_size_inst1 Nat (arrN l)) = Zlength l.
Proof. unfold arrN. apply V_size_mk. Qed.

Lemma lzCopy_succ' out d n :
  Deflate_lzCopy out d (Nat_succ n) =
    Deflate_lzCopy (Array_push_inst1 UInt8 out
      (Array_getD_inst1 UInt8 out (Array_size_inst1 UInt8 out -L d)
         (OfNat_ofNat_inst1 UInt8 Nat_zero (UInt8_instOfNat Nat_zero)))) d n.
Proof. exact (of_leq (Deflate_InflateExport_lzCopy_succ out d n)). Qed.

Lemma lzCopy_zero' out d : Deflate_lzCopy out d Nat_zero = out.
Proof. exact (of_leq (Deflate_InflateExport_lzCopy_zero out d)). Qed.

Lemma lzCopy_arrU8 n : forall l D, bytes_ok l -> 1 <= V D <= Zlength l ->
  Deflate_lzCopy (arrU8 l) D (Nat_of_nat n) = arrU8 (lzCopyZ l (V D) n) /\ bytes_ok (lzCopyZ l (V D) n).
Proof.
  induction n as [|n IH]; intros l D Hl HD.
  - cbn [Nat_of_nat lzCopyZ]. rewrite lzCopy_zero'. auto.
  - cbn [Nat_of_nat lzCopyZ]. rewrite lzCopy_succ'.
    unfold arrU8 at 2 3. rewrite getD_mk'.
    rewrite (lgetD_toL _ _ Inhabitant_Z).
    rewrite V_sub. fold (arrU8 l). rewrite size_arrU8.
    destruct (Z.max 0 (Zlength l - V D) <? Zlength l) eqn:E; [|apply Z.ltb_ge in E; lia].
    rewrite push_arrU8'.
    assert (Hz : 0 <= Znth (Z.max 0 (Zlength l - V D)) l < 256)
      by (apply Forall_Znth; auto; lia).
    apply IH.
    + apply Forall_app; split; auto.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

(** * Matchers of the exported equations, on constructors *)

Section Matchers.
#[local] Set Universe Polymorphism.
Context {M : Type}.
Lemma m1_none h1 h2 :
  Deflate_InflateExport_inflateSyms_eq_match_1 (fun _ => M) (Option_none_inst1 Nat) h1 h2 = h1 Unit_unit.
Proof. reflexivity. Qed.
Lemma m1_some x h1 h2 :
  Deflate_InflateExport_inflateSyms_eq_match_1 (fun _ => M) (Option_some_inst1 Nat x) h1 h2 = h2 x.
Proof. reflexivity. Qed.
Lemma m3_none h1 h2 :
  Deflate_InflateExport_inflateSyms_eq_match_3 (fun _ => M) (Option_none_inst1 _) h1 h2 = h1 Unit_unit.
Proof. reflexivity. Qed.
Lemma m3_some a b h1 h2 :
  Deflate_InflateExport_inflateSyms_eq_match_3 (fun _ => M)
    (Option_some_inst1 _ (Prod_mk_inst3 Nat Nat a b)) h1 h2 = h2 a b.
Proof. reflexivity. Qed.
Lemma dm1_none h1 h2 :
  Deflate_InflateExport_dynHeader_eq_match_1 (fun _ => M) (Option_none_inst1 _) h1 h2 = h1 Unit_unit.
Proof. reflexivity. Qed.
Lemma dm1_some a b h1 h2 :
  Deflate_InflateExport_dynHeader_eq_match_1 (fun _ => M)
    (Option_some_inst1 _ (Prod_mk_inst3 (Array_inst1 Nat) Nat a b)) h1 h2 = h2 a b.
Proof. reflexivity. Qed.
Lemma bm1_none h1 h2 :
  Deflate_InflateExport_block_eq_match_1 (fun _ => M) (Option_none_inst1 _) h1 h2 = h1 Unit_unit.
Proof. reflexivity. Qed.
Lemma bm1_some a b h1 h2 :
  Deflate_InflateExport_block_eq_match_1 (fun _ => M)
    (Option_some_inst1 _ (Prod_mk_inst3 (Array_inst1 UInt8) Nat a b)) h1 h2 = h2 a b.
Proof. reflexivity. Qed.
Lemma bm3_none h1 h2 :
  Deflate_InflateExport_block_eq_match_3 (fun _ => M) (Option_none_inst1 _) h1 h2 = h1 Unit_unit.
Proof. reflexivity. Qed.
Lemma bm3_some a b c d h1 h2 :
  Deflate_InflateExport_block_eq_match_3 (fun _ => M)
    (Option_some_inst1 _ (Prod_mk_inst3 (Array_inst1 Nat) (Prod_inst3 (Array_inst1 Nat) (Prod_inst3 Nat Bool)) a
      (Prod_mk_inst3 (Array_inst1 Nat) (Prod_inst3 Nat Bool) b (Prod_mk_inst3 Nat Bool c d)))) h1 h2 = h2 a b c d.
Proof. reflexivity. Qed.
Lemma im1_none h1 h2 :
  Deflate_InflateExport_inflateBlocks_eq_match_1 (fun _ => M) (Option_none_inst1 _) h1 h2 = h1 Unit_unit.
Proof. reflexivity. Qed.
Lemma im1_some a b c h1 h2 :
  Deflate_InflateExport_inflateBlocks_eq_match_1 (fun _ => M)
    (Option_some_inst1 _ (Prod_mk_inst3 (Array_inst1 UInt8) (Prod_inst3 Nat Bool) a (Prod_mk_inst3 Nat Bool b c)))
    h1 h2 = h2 a b c.
Proof. reflexivity. Qed.
End Matchers.

Ltac mred :=
  rewrite ?m1_none, ?m1_some, ?m3_none, ?m3_some, ?dm1_none, ?dm1_some, ?bm1_none, ?bm1_some,
    ?bm3_none, ?bm3_some, ?im1_none, ?im1_some; cbv beta.

(** * Booleans: Lean conditions against the mirror's *)

Ltac bprop H :=
  repeat progress rewrite ?andb_true_iff, ?andb_false_iff, ?orb_true_iff, ?orb_false_iff,
    ?negb_true_iff, ?negb_false_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt,
    ?Z.eqb_eq, ?Z.eqb_neq in H.

Ltac bsolve :=
  first [ assumption
        | (repeat progress rewrite ?andb_true_iff, ?andb_false_iff, ?orb_true_iff, ?orb_false_iff,
             ?negb_true_iff, ?negb_false_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt,
             ?Z.eqb_eq, ?Z.eqb_neq);
          first [ lia | intuition (first [ lia | congruence | assumption ]) ] ].

(* decide the mirror's conditions from the context *)
Ltac zif :=
  repeat match goal with
  | |- context [if ?c then _ else _] =>
      lazymatch type of c with bool => idtac end;
      first [ replace c with true by (symmetry; bsolve)
            | replace c with false by (symmetry; bsolve) ];
      cbv iota beta zeta
  end.

Lemma notOversub_B2b l : Forall (fun x => 0 <= x) l ->
  B2b (Deflate_notOversub (arrN l)) = notOversubZ l.
Proof. intros Hl. apply (lean_notOversub_eq l Hl). Qed.

Definition nonneg (l : list Z) : Prop := Forall (fun x => 0 <= x) l.

(* the rewrites that bring a Lean condition to the mirror's terms *)
Ltac brew H :=
  rewrite ?B2b_and, ?B2b_or, ?B2b_not, ?B2b_blt, ?B2b_ble, ?B2b_beq, ?B2b_Bb in H;
  rewrite ?V_add, ?V_mul, ?bitsOf_size', ?size_arrU8, ?size_arrN in H;
  rewrite ?notOversub_B2b, ?V_getD_arrN in H by (unfold nonneg in *; auto using Forall_sublist); vlits.

(* split on the outermost Lean condition c *)
Ltac bsplit c :=
  let E := fresh "E" in let EP := fresh "EP" in
  destruct c eqn:E; apply (f_equal B2b) in E; cbn [B2b] in E;
  rewrite ?cond_false, ?cond_true;
  brew E; pose proof E as EP; bprop EP.

Ltac bs :=
  match goal with
  | |- context [cond _ ?c _ _] =>
      lazymatch c with Bool_true => fail | Bool_false => fail | _ => bsplit c end
  end.

Lemma Bb_and a b : Bb (a && b) = Bool_and (Bb a) (Bb b).
Proof. destruct a, b; reflexivity. Qed.

(** * Lean lists *)

Lemma rep_zero {A} (x : A) : List_replicate_inst1 A Nat_zero x = List_nil_inst1 A.
Proof. reflexivity. Qed.
Lemma rep_succ {A} n (x : A) :
  List_replicate_inst1 A (Nat_succ n) x = List_cons_inst1 A x (List_replicate_inst1 A n x).
Proof. reflexivity. Qed.
Lemma set_nil {A} i (x : A) : List_set_inst1 A (List_nil_inst1 A) i x = List_nil_inst1 A.
Proof. destruct i; reflexivity. Qed.
Lemma set_zero {A} y l (x : A) :
  List_set_inst1 A (List_cons_inst1 A y l) Nat_zero x = List_cons_inst1 A x l.
Proof. reflexivity. Qed.
Lemma set_succ {A} y l i (x : A) :
  List_set_inst1 A (List_cons_inst1 A y l) (Nat_succ i) x = List_cons_inst1 A y (List_set_inst1 A l i x).
Proof. reflexivity. Qed.
Lemma take_zero {A} l : List_take_inst1 A Nat_zero l = List_nil_inst1 A.
Proof. reflexivity. Qed.
Lemma take_nil {A} n : List_take_inst1 A n (List_nil_inst1 A) = List_nil_inst1 A.
Proof. destruct n; reflexivity. Qed.
Lemma take_succ {A} n y l :
  List_take_inst1 A (Nat_succ n) (List_cons_inst1 A y l) = List_cons_inst1 A y (List_take_inst1 A n l).
Proof. reflexivity. Qed.
Lemma drop_zero {A} l : List_drop_inst1 A Nat_zero l = l.
Proof. reflexivity. Qed.
Lemma drop_nil {A} n : List_drop_inst1 A n (List_nil_inst1 A) = List_nil_inst1 A.
Proof. destruct n; reflexivity. Qed.
Lemma drop_succ {A} n y l : List_drop_inst1 A (Nat_succ n) (List_cons_inst1 A y l) = List_drop_inst1 A n l.
Proof. reflexivity. Qed.
Lemma last_nil {A} : List_getLast__q_inst1 A (List_nil_inst1 A) = Option_none_inst1 A.
Proof. reflexivity. Qed.
Lemma last_one {A} (x : A) :
  List_getLast__q_inst1 A (List_cons_inst1 A x (List_nil_inst1 A)) = Option_some_inst1 A x.
Proof. reflexivity. Qed.
Lemma last_two {A} (x y : A) l :
  List_getLast__q_inst1 A (List_cons_inst1 A x (List_cons_inst1 A y l)) =
    List_getLast__q_inst1 A (List_cons_inst1 A y l).
Proof. reflexivity. Qed.

Lemma toL_repeat {A B} (f : A -> B) x n :
  toL f (repeat x n) = List_replicate_inst1 B (Nat_of_nat n) (f x).
Proof. induction n as [|n IH]; cbn [repeat toL Nat_of_nat]; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma toL_firstn {A B} (f : A -> B) n l :
  toL f (firstn n l) = List_take_inst1 B (Nat_of_nat n) (toL f l).
Proof.
  revert l; induction n as [|n IH]; intros l; cbn [firstn Nat_of_nat].
  - reflexivity.
  - destruct l as [|x l]; cbn [toL]; [rewrite take_nil; reflexivity|].
    rewrite take_succ, IH; reflexivity.
Qed.

Lemma toL_skipn {A B} (f : A -> B) n l :
  toL f (skipn n l) = List_drop_inst1 B (Nat_of_nat n) (toL f l).
Proof.
  revert l; induction n as [|n IH]; intros l; cbn [skipn Nat_of_nat].
  - reflexivity.
  - destruct l as [|x l]; cbn [toL]; [rewrite drop_nil; reflexivity|].
    rewrite drop_succ, IH; reflexivity.
Qed.

Lemma toL_upd {A B} (f : A -> B) x : forall k l, (k < length l)%nat ->
  toL f (upd_Znth (Z.of_nat k) l x) = List_set_inst1 B (toL f l) (Nat_of_nat k) (f x).
Proof.
  induction k as [|k IH]; intros l Hk; destruct l as [|y l]; cbn [length] in Hk; try lia.
  - change (Z.of_nat 0) with 0. rewrite upd_Znth0. reflexivity.
  - rewrite upd_Znth_cons by lia. cbn [toL Nat_of_nat]. rewrite set_succ.
    replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia. rewrite IH by lia. reflexivity.
Qed.

(** * Lean arrays of Rocq lists *)

Lemma Nat_of_nat_V X : Nat_of_nat (Z.to_nat (V X)) = X.
Proof. unfold V. rewrite Nat2Z.id. apply Nat2natid. Qed.

Lemma set_arrN l J X : V J < Zlength l ->
  Array_set__B_inst1 Nat (arrN l) J X = arrN (upd_Znth (V J) l (V X)).
Proof.
  intros HJ. unfold arrN. rewrite (of_leq (Deflate_InflateExport_setD_mk _ _ _ _)). f_equal.
  change (V J) with (Z.of_nat (nat_of_Nat J)). rewrite toL_upd, Nat2natid, LN_V; [reflexivity|].
  rewrite Zlength_correct in HJ. unfold V in HJ. lia.
Qed.

Lemma rep_arrN N X : Array_replicate_inst1 Nat N X = arrN (Zrepeat (V X) (V N)).
Proof.
  rewrite (of_leq (Deflate_InflateExport_replicate_mk _ _ _)). unfold arrN, Zrepeat.
  rewrite toL_repeat, Nat_of_nat_V, LN_V. reflexivity.
Qed.

Lemma app_arrN l1 l2 :
  HAppend_hAppend_inst7 (Array_inst1 Nat) (Array_inst1 Nat) (Array_inst1 Nat)
    (instHAppendOfAppend_inst1 (Array_inst1 Nat) (Array_instAppend_inst1 Nat))
    (arrN l1) (arrN l2) = arrN (l1 ++ l2).
Proof.
  unfold arrN. rewrite (of_leq (Deflate_InflateExport_append_mk _ _ _)), toL_app. reflexivity.
Qed.

Lemma extract_arrN l A C :
  Array_extract_inst1 Nat (arrN l) A C = arrN (sublist (V A) (V C) l).
Proof.
  unfold arrN. rewrite (of_leq (Deflate_InflateExport_extract_mk _ _ _ _)). f_equal.
  rewrite sublist_old_sublist by apply V_nonneg. unfold old_sublist.
  rewrite toL_firstn, toL_skipn, Nat_of_nat_V. f_equal.
  apply V_inj. rewrite V_Nat_of_nat, V_sub. lia.
Qed.

Lemma back_arrN l : Forall (fun x => 0 <= x) l ->
  lastZ l = optV (Array_back__q_inst1 Nat (arrN l)).
Proof.
  intros Hl. unfold arrN. rewrite (of_leq (Deflate_InflateExport_back_mk _ _)). unfold lastZ.
  induction l as [|x l IH]; [reflexivity|].
  inversion Hl; subst. destruct l as [|y l].
  - cbn [toL rev app]. rewrite last_one. cbn [optV]. rewrite V_LN by auto. reflexivity.
  - cbn [toL]. rewrite last_two.
    change (List_cons_inst1 Nat (LN y) (toL LN l)) with (toL LN (y :: l)). rewrite <- IH by auto.
    cbn [rev]. destruct (rev l ++ [y]) eqn:E; [|reflexivity].
    apply (f_equal (@length Z)) in E. rewrite length_app in E. cbn in E. lia.
Qed.

Lemma lsbZ_range bytes : forall n p, 0 <= lsbZ bytes p n < 2 ^ Z.of_nat n.
Proof.
  induction n as [|n IH]; intros p; cbn [lsbZ]; [cbn; lia|].
  specialize (IH (p + 1)). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  destruct (bitZ bytes p); lia.
Qed.

(** * The length and distance tables *)

Lemma lenTab k : 0 <= k < 29 ->
  V (Deflate_InflateExport_lenBase (LN k)) = lenBaseZ k /\ V (Deflate_InflateExport_lenExtra (LN k)) = lenExtraZ k.
Proof.
  intros Hk. rewrite <- (Z2Nat.id k) by lia. assert (Hn : (Z.to_nat k < 29)%nat) by lia.
  generalize (Z.to_nat k) Hn. clear. intros n Hn.
  do 29 (destruct n as [|n]; [split; vm_compute; reflexivity|]). lia.
Qed.

Lemma distTab k : 0 <= k < 30 ->
  V (Deflate_InflateExport_distBase (LN k)) = distBaseZ k /\ V (Deflate_InflateExport_distExtra (LN k)) = distExtraZ k.
Proof.
  intros Hk. rewrite <- (Z2Nat.id k) by lia. assert (Hn : (Z.to_nat k < 30)%nat) by lia.
  generalize (Z.to_nat k) Hn. clear. intros n Hn.
  do 30 (destruct n as [|n]; [split; vm_compute; reflexivity|]). lia.
Qed.

Lemma distBaseZ_pos k : 0 <= k -> 1 <= distBaseZ k.
Proof.
  intros Hk. unfold distBaseZ. destruct (k <? 4) eqn:E; bprop E; [lia|].
  assert (0 < 2 ^ (k / 2 - 1)) by (apply Z.pow_pos_nonneg; [lia|]; apply Z.le_0_sub; apply Z.div_le_lower_bound; lia ).
  pose proof (Z.mod_pos_bound k 2 ltac:(lia)). nia.
Qed.

Lemma V_lenTab K : V K < 29 ->
  V (Deflate_InflateExport_lenBase K) = lenBaseZ (V K) /\ V (Deflate_InflateExport_lenExtra K) = lenExtraZ (V K).
Proof.
  intros HK. pose proof (V_nonneg K). rewrite <- (LN_V K). rewrite V_LN by auto. apply lenTab. lia.
Qed.

Lemma V_distTab K : V K < 30 ->
  V (Deflate_InflateExport_distBase K) = distBaseZ (V K) /\ V (Deflate_InflateExport_distExtra K) = distExtraZ (V K).
Proof.
  intros HK. pose proof (V_nonneg K). rewrite <- (LN_V K). rewrite V_LN by auto. apply distTab. lia.
Qed.

Lemma lenTable_get' i :
  GetElem__q_getElem__q_inst7 (Array_inst1 (Prod_inst3 Nat Nat)) Nat (Prod_inst3 Nat Nat)
    (fun xs i0 => LT_lt_inst1 Nat instLTNat i0 (Array_size_inst1 (Prod_inst3 Nat Nat) xs))
    (Array_instGetElem__qNatLtSize_inst1 (Prod_inst3 Nat Nat)) Deflate_lenTable i =
  cond (Option_inst1 (Prod_inst3 Nat Nat)) (Nat_blt i (L# 29))
    (Option_some_inst1 (Prod_inst3 Nat Nat)
       (Prod_mk_inst3 Nat Nat (Deflate_InflateExport_lenBase i) (Deflate_InflateExport_lenExtra i)))
    (Option_none_inst1 (Prod_inst3 Nat Nat)).
Proof. exact (of_leq (Deflate_InflateExport_lenTable_get i)). Qed.

Lemma distTable_get' i :
  GetElem__q_getElem__q_inst7 (Array_inst1 (Prod_inst3 Nat Nat)) Nat (Prod_inst3 Nat Nat)
    (fun xs i0 => LT_lt_inst1 Nat instLTNat i0 (Array_size_inst1 (Prod_inst3 Nat Nat) xs))
    (Array_instGetElem__qNatLtSize_inst1 (Prod_inst3 Nat Nat)) Deflate_distTable i =
  cond (Option_inst1 (Prod_inst3 Nat Nat)) (Nat_blt i (L# 30))
    (Option_some_inst1 (Prod_inst3 Nat Nat)
       (Prod_mk_inst3 Nat Nat (Deflate_InflateExport_distBase i) (Deflate_InflateExport_distExtra i)))
    (Option_none_inst1 (Prod_inst3 Nat Nat)).
Proof. exact (of_leq (Deflate_InflateExport_distTable_get i)). Qed.

(** * The fixed codes and the order of the code length code *)

Lemma clOrder_eq : Deflate_clOrder = arrN clOrderZ.
Proof. reflexivity. Qed.

Lemma clOrder_range : Forall (fun x => 0 <= x < 19) clOrderZ.
Proof. unfold clOrderZ. repeat (apply Forall_cons; [lia|]). apply Forall_nil. Qed.

Lemma fixedDist_eq' : Deflate_fixedDist = arrN fixedDistZ.
Proof. rewrite (of_leq Deflate_InflateExport_fixedDist_eq). reflexivity. Qed.

Lemma lgetD_ext {A} (d : A) : forall l1 l2,
  List_length_inst1 A l1 = List_length_inst1 A l2 ->
  (forall i, Deflate_Puff_Export_lgetD A l1 i d = Deflate_Puff_Export_lgetD A l2 i d) -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] Hlen Hget;
    rewrite ?length_nil, ?length_cons in Hlen; try discriminate; [reflexivity|].
  injection Hlen as Hlen. f_equal.
  - specialize (Hget Nat_zero). rewrite !lgetD_zero' in Hget. exact Hget.
  - apply IH; auto. intros i. specialize (Hget (Nat_succ i)). rewrite !lgetD_succ' in Hget. exact Hget.
Qed.

Lemma arr_ext (a b : Array_inst1 Nat) :
  V (Array_size_inst1 Nat a) = V (Array_size_inst1 Nat b) ->
  (forall i, V (Array_getD_inst1 Nat a i (L# 0)) = V (Array_getD_inst1 Nat b i (L# 0))) -> a = b.
Proof.
  intros Hs Hg.
  change a with (Array_mk_inst1 Nat (toList0 _ a)) in *.
  change b with (Array_mk_inst1 Nat (toList0 _ b)) in *.
  rewrite !size_mk' in Hs. f_equal. apply (lgetD_ext (L# 0)).
  - apply V_inj; exact Hs.
  - intros i. specialize (Hg i). rewrite !getD_mk' in Hg. apply V_inj; exact Hg.
Qed.

Lemma Znth_rep_app (x : Z) n l k : 0 <= n -> 0 <= k ->
  Znth k (Zrepeat x n ++ l) = if k <? n then x else Znth (k - n) l.
Proof.
  intros Hn Hk. destruct (k <? n) eqn:E; bprop E.
  - rewrite app_Znth1 by (rewrite Zlength_Zrepeat; lia). apply Znth_Zrepeat; lia.
  - rewrite app_Znth2 by (rewrite Zlength_Zrepeat; lia). rewrite Zlength_Zrepeat by lia. reflexivity.
Qed.

Lemma Forall_Zrepeat (P : Z -> Prop) x n : P x -> Forall P (Zrepeat x n).
Proof. intros Hx. unfold Zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. subst; auto. Qed.

Lemma fixedLitZ_nonneg : Forall (fun x => 0 <= x) fixedLitZ.
Proof. unfold fixedLitZ. rewrite !Forall_app. repeat split; apply Forall_Zrepeat; lia. Qed.

Lemma fixedLit_eq' : Deflate_fixedLit = arrN fixedLitZ.
Proof.
  apply arr_ext.
  - rewrite (of_leq Deflate_InflateExport_fixedLit_size), size_arrN. vlits. reflexivity.
  - intros i. rewrite (of_leq (Deflate_InflateExport_fixedLit_getD i)), V_getD_arrN by apply fixedLitZ_nonneg.
    pose proof (V_nonneg i).
    unfold fixedLitZ. rewrite !Znth_rep_app by lia.
    repeat (bs; zif); vlits; repeat (rewrite Znth_rep_app by lia; zif); try reflexivity.
    all: first [ reflexivity | (rewrite Znth_Zrepeat by lia; reflexivity)
               | (rewrite Znth_overflow by (rewrite Zlength_Zrepeat; lia); reflexivity) ].
Qed.



Lemma V_blCount l x : Forall (fun x => 0 <= x) l ->
  V (Deflate_blCount (arrN l) x) = cntOf l (V x).
Proof.
  intros Hl. rewrite (of_leq (Deflate_Puff_blCount_eq_cnt _ _)).
  assert (Hlen : forall x, V (Array_getD_inst1 Nat (arrN l) x (L# 0)) = Znth (V x) l)
    by (intros; apply V_getD_arrN, Hl).
  rewrite (V_cnt _ (fun i => Znth i l) Hlen). unfold cntOf. f_equal.
  rewrite <- (size_arrN l). unfold V. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma V_krbl l : Forall (fun x => 0 <= x) l ->
  V (Deflate_Puff_kr (Deflate_blCount (arrN l)) Deflate_maxBits) = krOf l.
Proof.
  intros Hl. rewrite (V_kr (Deflate_blCount (arrN l)) (cntOf l)).
  - unfold Deflate_maxBits. vlits. reflexivity.
  - intros x. apply V_blCount, Hl.
Qed.

Lemma zlibOk_B2b l c : Forall (fun x => 0 <= x) l ->
  B2b (Deflate_zlibOk (arrN l) c) = zlibOkZ l (B2b c).
Proof.
  intros Hl. rewrite (of_leq (Deflate_InflateExport_zlibOk_eq _ _)).
  rewrite !B2b_or, !B2b_and, B2b_not, !B2b_beq, !V_blCount, !V_krbl, size_arrN by auto.
  vlits. reflexivity.
Qed.

(** * The spec's parts on Rocq values *)

Definition fromU8 (a : Array_inst1 UInt8) : list Z :=
  (fix go (l : List_inst1 UInt8) : list Z :=
     match l with List_nil_inst1 _ => [] | List_cons_inst1 _ x t => V (UInt8_toNat x) :: go t end)
    (toList0 _ a).

Lemma fromU8_arrU8 l : bytes_ok l -> fromU8 (arrU8 l) = l.
Proof.
  unfold fromU8, arrU8. cbn [toList0].
  induction l as [|x l IH]; intros Hl; cbn [toL]; [reflexivity|].
  inversion Hl; subst. rewrite IH by auto. f_equal.
  rewrite (of_leq (Deflate_Puff_Export_uint8_toNat_ofNat _)), V_mod by (vlits; lia).
  vlits. rewrite V_LN by lia. apply Z.mod_small; lia.
Qed.

(* a mirror result m and a Lean one o agree: o is m carried to Lean values *)
Definition R {A L : Type} (emb : A -> L) (ok : A -> Prop) (m : option A) (o : Option_inst1 L) : Prop :=
  match m with
  | None => o = Option_none_inst1 L
  | Some a => o = Option_some_inst1 L (emb a) /\ ok a
  end.

Definition embS (r : list Z * Z) := Prod_mk_inst3 (Array_inst1 UInt8) Nat (arrU8 (Datatypes.fst r)) (LN (Datatypes.snd r)).
Definition okS (r : list Z * Z) := bytes_ok (Datatypes.fst r) /\ 0 <= Datatypes.snd r.
Definition embL (r : list Z * Z) := Prod_mk_inst3 (Array_inst1 Nat) Nat (arrN (Datatypes.fst r)) (LN (Datatypes.snd r)).
Definition okL (r : list Z * Z) := nonneg (Datatypes.fst r) /\ 0 <= Datatypes.snd r.
Definition embD (r : list Z * list Z * Z * bool) :=
  match r with (lit, dist, q, z) =>
    Prod_mk_inst3 (Array_inst1 Nat) (Prod_inst3 (Array_inst1 Nat) (Prod_inst3 Nat Bool)) (arrN lit)
      (Prod_mk_inst3 (Array_inst1 Nat) (Prod_inst3 Nat Bool) (arrN dist) (Prod_mk_inst3 Nat Bool (LN q) (Bb z)))
  end.
Definition okD (r : list Z * list Z * Z * bool) :=
  match r with (lit, dist, q, z) => nonneg lit /\ nonneg dist /\ 0 <= q end.
Definition embB (r : list Z * Z * bool) :=
  match r with (o, q, z) =>
    Prod_mk_inst3 (Array_inst1 UInt8) (Prod_inst3 Nat Bool) (arrU8 o) (Prod_mk_inst3 Nat Bool (LN q) (Bb z))
  end.
Definition okB (r : list Z * Z * bool) := match r with (o, q, z) => bytes_ok o /\ 0 <= q end.

Ltac rnone := first [ reflexivity | (cbv [R]; reflexivity) | (exfalso; lia) ].

Ltac vnn := repeat match goal with |- context [V ?x] =>
  lazymatch goal with _ : 0 <= V x |- _ => fail | _ => pose proof (V_nonneg x) end end.

Ltac lneq := apply V_inj; rewrite ?V_add, ?V_mul; vlits; vnn; rewrite V_LN by lia; lia.

Section Spec.
Variable bytes : list Z.
Hypothesis Hb : bytes_ok bytes.
Local Notation B := (Deflate_bitsOf (arrU8 bytes)).

Ltac vside := vlits; first [ lia | rewrite ?V_add, ?V_mul; vlits; lia | rewrite ?V_add, ?V_mul, ?V_sub; vlits; lia ].

Lemma getbitsE P N p n : p = V P -> n = V N -> getbitsZ bytes p n = optV (Deflate_getbits B P N).
Proof. intros -> ->. apply getbits_V, Hb. Qed.

Lemma decodeE l P p : p = V P ->
  lean_decode l bytes p = Vopt (Deflate_decodeSym (Deflate_code (arrN l)) B P).
Proof. intros ->. unfold lean_decode. rewrite LN_V. reflexivity. Qed.

Ltac gb := match goal with |- context [Deflate_getbits _ ?P ?N] => rewrite (getbitsE P N) by vside end.
Ltac gbd v G := match goal with |- context [Deflate_getbits _ ?P ?N] =>
  rewrite (getbitsE P N) by vside;
  destruct (Deflate_getbits B P N) as [|v] eqn:G; cbn [optV]; mred; [rnone|] end.
Ltac dc := match goal with
  |- context [Deflate_decodeSym (Deflate_code (arrN ?l)) _ ?P] => rewrite (decodeE l P) by vside end.

Lemma getbits_some P N v : Deflate_getbits B P N = Option_some_inst1 Nat v ->
  V P + V N <= nbits bytes /\ 0 <= V v < 2 ^ V N.
Proof.
  intros G. pose proof (getbitsE P N _ _ Logic.eq_refl Logic.eq_refl) as E. rewrite G in E. cbn [optV] in E.
  unfold getbitsZ in E. destruct (V P + V N <=? nbits bytes) eqn:C; [|discriminate].
  injection E as E. bprop C. split; auto.
  rewrite <- E. pose proof (lsbZ_range bytes (Z.to_nat (V N)) (V P)).
  rewrite Z2Nat.id in H by apply V_nonneg. exact H.
Qed.

Lemma decode_bounds l P s q :
  Deflate_decodeSym (Deflate_code (arrN l)) B P = Option_some_inst1 _ (Prod_mk_inst3 Nat Nat s q) ->
  V P < V q /\ V q <= nbits bytes /\ V s < Zlength l.
Proof.
  intros D. pose proof (of_leq (Deflate_InflateExport_decodeSym_bounds _ _ _ _ _ (to_leq D))) as H.
  apply (f_equal B2b) in H. rewrite !B2b_and, !B2b_blt, B2b_ble, bitsOf_size', size_arrN in H.
  cbn [B2b] in H. bprop H. lia.
Qed.

Lemma lzCopy_arrU8' l D N : bytes_ok l -> 1 <= V D <= Zlength l ->
  Deflate_lzCopy (arrU8 l) D N = arrU8 (lzCopyZ l (V D) (Z.to_nat (V N))) /\ bytes_ok (lzCopyZ l (V D) (Z.to_nat (V N))).
Proof.
  intros Hl HD. pose proof (lzCopy_arrU8 (Z.to_nat (V N)) l D Hl HD).
  rewrite Nat_of_nat_V in H. exact H.
Qed.

(** ** inflateSyms *)

Lemma syms_R lit dist n : forall P p out, p = V P -> bytes_ok out -> nbits bytes - p < Z.of_nat n ->
  R embS okS (symsZ lit dist bytes n p out)
    (Deflate_inflateSyms (Deflate_code (arrN lit)) (Deflate_code (arrN dist)) B P (arrU8 out)).
Proof.
  induction n as [|n IH]; intros P p out -> Hout Hn.
  - cbn [symsZ]; cbv [R]. rewrite (of_leq (Deflate_InflateExport_inflateSyms_eq _ _ _ _ _)).
    destruct (Deflate_decodeSym _ B P) as [|[s p1]] eqn:D; mred; [rnone|].
    apply decode_bounds in D. lia.
  - cbn [symsZ]. rewrite (of_leq (Deflate_InflateExport_inflateSyms_eq _ _ _ _ _)).
    dc. destruct (Deflate_decodeSym _ B P) as [|[s p1]] eqn:D; cbn [Vopt fst1 snd1]; mred;
      [rnone|].
    apply decode_bounds in D.
    bs; zif.
    + (* s >= 256 *)
      bs; zif.
      * (* s > 256 *)
        rewrite lenTable_get'.
        replace (V s - 257) with (V (s -L L# 257)) by (rewrite V_sub; vlits; lia).
        bs; zif; mred; [rnone|].
        destruct (V_lenTab (s -L L# 257)) as [HlB HlE]; [lia|].
        gb. destruct (Deflate_getbits B p1 _) as [|e] eqn:G1; cbn [optV]; mred; [rnone|].
        dc. destruct (Deflate_decodeSym _ B _) as [|[ds p3]] eqn:D2; cbn [Vopt fst1 snd1]; mred;
          [rnone|].
        apply decode_bounds in D2.
        rewrite distTable_get'. bs; zif; mred; [rnone|].
        destruct (V_distTab ds) as [HdB HdE]; [lia|].
        gb. destruct (Deflate_getbits B p3 _) as [|e2] eqn:G2; cbn [optV]; mred; [rnone|].
        bs; zif; [rnone|].
        bs; zif; [rnone|].
        destruct (lzCopy_arrU8' out (Deflate_InflateExport_distBase ds +L e2)
                    (Deflate_InflateExport_lenBase (s -L L# 257) +L e)) as [Hlz Hok];
          [auto| rewrite V_add; pose proof (distBaseZ_pos (V ds) (V_nonneg ds));
                 pose proof (V_nonneg e2); lia |].
        rewrite Hlz. rewrite !V_add, HdB, HlB in *.
        eapply IH; [vside | exact Hok | lia].
      * (* s = 256 *)
        cbv [R embS okS Datatypes.fst Datatypes.snd]. rewrite LN_V. split; [reflexivity|split; auto; apply V_nonneg].
    + (* a literal *)
      bs; zif; [rnone|].
      rewrite push_arrU8. eapply IH; [reflexivity| |lia].
      apply Forall_app; split; auto. repeat constructor; pose proof (V_nonneg s); lia.
Qed.

(** ** Stored blocks *)

Lemma bytesAt_succ' Q n :
  Deflate_InflateExport_bytesAt B Q (Nat_succ n) =
    List_cons_inst1 UInt8 (Nat_toUInt8 (Deflate_lsbVal B Q (L# 8)))
      (Deflate_InflateExport_bytesAt B (Q +L L# 8) n).
Proof. exact (of_leq (Deflate_InflateExport_bytesAt_succ _ _ _)). Qed.

Lemma bytesAt_eq : forall n Q,
  Deflate_InflateExport_bytesAt B Q (Nat_of_nat n) =
    toL (fun z => UInt8_ofNat (LN z)) (bytesAtZ bytes (V Q) n).
Proof.
  induction n as [|n IH]; intros Q; [reflexivity|].
  cbn [Nat_of_nat bytesAtZ toL].
  rewrite bytesAt_succ', IH, V_add. vlits. f_equal.
  rewrite <- (V_lsbVal bytes Hb 8 Q), LN_V. reflexivity.
Qed.

Lemma bytesAt_ok : forall n q, bytes_ok (bytesAtZ bytes q n).
Proof.
  induction n as [|n IH]; intros q; cbn [bytesAtZ]; [constructor|].
  constructor; [|apply IH]. pose proof (lsbZ_range bytes 8 q) as H.
  change (2 ^ Z.of_nat 8) with 256 in H. exact H.
Qed.

Lemma stored_R P : R embS okS (storedZ bytes (V P)) (Deflate_stored B P).
Proof.
  unfold storedZ. rewrite (of_leq (Deflate_InflateExport_stored_eq _ _)). cbv zeta.
  replace ((V P + 7) / 8 * 8) with (V ((P +L L# 7) /L L# 8 *L L# 8))
    by (rewrite V_mul, V_div, V_add by (vlits; lia); vlits; reflexivity).
  remember ((P +L L# 7) /L L# 8 *L L# 8) as Q eqn:EQ.
  gbd len G1. gbd nlen G2.
  bs; zif; [rnone|].
  cbv [R embS okS Datatypes.fst Datatypes.snd]. split; [|split; [apply bytesAt_ok | pose proof (V_nonneg Q); pose proof (V_nonneg len); lia]].
  f_equal. f_equal.
  - unfold arrU8. f_equal. rewrite <- (Nat_of_nat_V len) at 1. rewrite bytesAt_eq, V_add. vlits. reflexivity.
  - lneq.
Qed.

(** ** The code length code *)

Lemma readCLgo_R n : forall P H I acc i, i = V I -> V H <= 19 -> Zlength acc = 19 -> nonneg acc ->
  Z.max 0 (V H - i) < Z.of_nat n ->
  R embL okL (readCLgo bytes (V P) (V H) n i acc) (Deflate_readCL_go B P H I (arrN acc)).
Proof.
  induction n as [|n IH]; intros P H I acc i -> HH Hl Hacc Hn; [lia|].
  cbn [readCLgo]. rewrite (of_leq (Deflate_InflateExport_readCL_go_eq _ _ _ _ _)).
  bs; zif.
  - cbv [R embL okL Datatypes.fst Datatypes.snd]. split; [|split; [auto | pose proof (V_nonneg P); pose proof (V_nonneg H); lia]].
    do 2 f_equal. lneq.
  - gbd v G.
    rewrite clOrder_eq.
    assert (Hc : 0 <= Znth (V I) clOrderZ < 19)
      by (apply Forall_Znth; first [ apply clOrder_range
                                   | change (Zlength clOrderZ) with 19; pose proof (V_nonneg I); lia ]).
    assert (Hn0 : Forall (fun x => 0 <= x) clOrderZ)
      by (eapply Forall_impl; [|apply clOrder_range]; cbv beta; intros; lia).
    rewrite set_arrN by (rewrite V_getD_arrN by auto; lia).
    rewrite V_getD_arrN by auto.
    eapply IH; [vside | auto | rewrite upd_Znth_Zlength by lia; lia | | lia].
    apply Forall_upd_Znth; auto. apply V_nonneg.
Qed.

Lemma readCL_R P H : V H <= 19 ->
  R embL okL (readCLZ bytes (V P) (V H)) (Deflate_readCL B P H).
Proof.
  intros HH. unfold readCLZ. rewrite (of_leq (Deflate_InflateExport_readCL_def _ _ _)), rep_arrN. vlits.
  apply readCLgo_R; [vlits; reflexivity | auto | apply Zlength_Zrepeat; lia | apply Forall_Zrepeat; lia | lia].
Qed.

(** ** The code lengths *)

Lemma readLens_R cl n : forall P p T acc, p = V P -> nonneg acc ->
  Z.max 0 (V T - Zlength acc) < Z.of_nat n ->
  R embL okL (readLensZ cl bytes n p (V T) acc)
    (Deflate_readLens (Deflate_code (arrN cl)) B P T (arrN acc)).
Proof.
  induction n as [|n IH]; intros P p T acc -> Hacc Hn; [lia|].
  cbn [readLensZ]. rewrite (of_leq (Deflate_InflateExport_readLens_eq _ _ _ _ _)).
  bs; zif.
  2:{ cbv [R embL okL Datatypes.fst Datatypes.snd]. rewrite LN_V.
      split; [reflexivity | split; [auto | apply V_nonneg]]. }
  dc. destruct (Deflate_decodeSym _ B P) as [|[s p1]] eqn:D; cbn [Vopt fst1 snd1]; mred; [rnone|].
  apply decode_bounds in D.
  bs; zif.
  2:{ rewrite push_arrN. eapply IH; [reflexivity | | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia].
      apply Forall_app; split; auto. repeat constructor. apply V_nonneg. }
  cbv zeta.
  bsplit (Nat_beq s (L# 16)); bsplit (Nat_beq s (L# 17)); bsplit (Nat_beq s (L# 18)); zif.
  all: try (exfalso; lia).
  all: gbd e G.
  all: try (rewrite (back_arrN acc Hacc);
            destruct (Array_back__q_inst1 Nat (arrN acc)) as [|v] eqn:Hv; cbn [optV]; mred; [rnone|]).
  all: cbv iota beta zeta; mred; zif.
  all: bs; zif; [rnone|].
  all: rewrite rep_arrN, app_arrN; rewrite ?V_add; vlits.
  all: eapply IH; [vside | | rewrite Zlength_app, Zlength_Zrepeat by (pose proof (V_nonneg e); lia); vnn; lia].
  all: apply Forall_app; split; auto; apply Forall_Zrepeat; first [lia | apply V_nonneg].
Qed.

(** ** Dynamic block headers *)

Lemma empty_arrN : List_toArray_inst1 Nat (List_nil_inst1 Nat) = arrN [].
Proof. reflexivity. Qed.

Lemma dyn_R P : R embD okD (dynHeaderZ bytes (V P)) (Deflate_dynHeader B P).
Proof.
  unfold dynHeaderZ. rewrite (of_leq (Deflate_InflateExport_dynHeader_eq _ _)).
  gbd hlit G1. gbd hdist G2. gbd hclen G3.
  apply getbits_some in G1, G2, G3. vlits.
  replace (2 ^ 4) with 16 in G3 by reflexivity.
  bs; zif; [rnone|].
  assert (H19 : V (hclen +L L# 4) <= 19) by (rewrite V_add; vlits; lia).
  pose proof (readCL_R (P +L L# 14) (hclen +L L# 4) H19) as HR. rewrite !V_add in HR. vlits.
  destruct (readCLZ bytes (V P + 14) (V hclen + 4)) as [[cl q]|];
    cbv [R embL okL Datatypes.fst Datatypes.snd] in HR; [destruct HR as [HR [Hcl Hq]]|];
    rewrite HR; mred; [|rnone].
  bs; zif; [rnone|].
  rewrite empty_arrN.
  pose proof (readLens_R cl (Z.to_nat (V hlit + 257 + (V hdist + 1)) + 1) (LN q) q
                (hlit +L L# 257 +L (hdist +L L# 1)) [] ltac:(symmetry; apply V_LN; lia)
                (Forall_nil _) ltac:(rewrite !V_add, Zlength_nil; vlits; vnn; lia)) as HL.
  rewrite !V_add in HL. vlits.
  destruct (readLensZ cl bytes _ q _ []) as [[lens r]|];
    cbv [R embL okL Datatypes.fst Datatypes.snd] in HL; [destruct HL as [HL [Hlens Hr]]|];
    rewrite HL; mred; [|rnone].
  rewrite !extract_arrN, ?V_add. vlits. cbv zeta.
  bs; zif; [rnone|].
  cbv [R embD okD]. unfold nonneg in *.
  split; [|split; [apply Forall_sublist; auto | split; [apply Forall_sublist; auto | lia]]].
  repeat f_equal. apply B2b_inj.
  rewrite B2b_Bb, !B2b_and, !zlibOk_B2b, B2b_ble by auto using Forall_sublist. cbn [B2b].
  rewrite V_add. vlits. reflexivity.
Qed.

(** ** Blocks *)

Lemma block_R P T out : bytes_ok out ->
  R embB okB (blockZ bytes (V P) (V T) out) (Deflate_block B P T (arrU8 out)).
Proof.
  intros Hout. unfold blockZ. rewrite (of_leq (Deflate_InflateExport_block_eq _ _ _ _)).
  bs; zif.
  2:{ pose proof (stored_R P) as HS.
      destruct (storedZ bytes (V P)) as [[sb q]|];
        cbv [R embS okS Datatypes.fst Datatypes.snd] in HS; [destruct HS as [HS [Hsb Hq]]|];
        rewrite HS; mred; [|rnone].
      rewrite app_arrU8. cbv [R embB okB]. split; [reflexivity | split; [apply Forall_app; auto | lia]]. }
  bs; zif.
  2:{ rewrite fixedLit_eq', fixedDist_eq'. unfold symsF.
      pose proof (syms_R fixedLitZ fixedDistZ (Z.to_nat (nbits bytes - V P) + 1) P (V P) out
                    Logic.eq_refl Hout ltac:(lia)) as HS.
      destruct (symsZ fixedLitZ fixedDistZ bytes _ _ _) as [[o q]|];
        cbv [R embS okS Datatypes.fst Datatypes.snd] in HS; [destruct HS as [HS [Ho Hq]]|];
        rewrite HS; mred; [|rnone].
      cbv [R embB okB]. split; [reflexivity | auto]. }
  bs; zif; [rnone|].
  pose proof (dyn_R P) as HD.
  destruct (dynHeaderZ bytes (V P)) as [[[[lit dist] q] z]|];
    cbv [R embD okD] in HD; [destruct HD as [HD [Hl [Hd Hq]]]|]; rewrite HD; mred; [|rnone].
  unfold symsF.
  pose proof (syms_R lit dist (Z.to_nat (nbits bytes - q) + 1) (LN q) q out
                ltac:(symmetry; apply V_LN; lia) Hout ltac:(lia)) as HS.
  destruct (symsZ lit dist bytes _ q out) as [[o r]|];
    cbv [R embS okS Datatypes.fst Datatypes.snd] in HS; [destruct HS as [HS [Ho Hr]]|];
    rewrite HS; mred; [|rnone].
  cbv [R embB okB]. split; [reflexivity | auto].
Qed.

Lemma blocks_R n : forall P p out zl, p = V P -> bytes_ok out -> nbits bytes - p < Z.of_nat n ->
  R embB okB (blocksZ bytes n p out zl) (Deflate_inflateBlocks B P (arrU8 out) (Bb zl)).
Proof.
  induction n as [|n IH]; intros P p out zl -> Hout Hn.
  - cbn [blocksZ]. cbv [R]. rewrite (of_leq (Deflate_InflateExport_inflateBlocks_eq _ _ _ _)).
    destruct (Deflate_getbits B P (L# 1)) as [|v] eqn:G; mred; [reflexivity|].
    apply getbits_some in G. vlits. lia.
  - cbn [blocksZ]. rewrite (of_leq (Deflate_InflateExport_inflateBlocks_eq _ _ _ _)).
    gbd bfinal G1. gbd btype G2.
    pose proof (block_R (P +L L# 3) btype out Hout) as HB. rewrite V_add in HB. vlits.
    destruct (blockZ bytes (V P + 3) (V btype) out) as [[[o q] z]|];
      cbv [R embB okB] in HB; [destruct HB as [HB [Ho Hq]]|]; rewrite HB; mred; [|rnone].
    pose proof (V_LN q Hq) as HVq.
    bs; zif.
    2:{ cbv [R embB okB]. rewrite Bb_and. split; [reflexivity | auto]. }
    bs; zif; [rnone|].
    rewrite <- Bb_and. eapply IH; [symmetry; exact HVq | exact Ho | lia].
Qed.

End Spec.

(** * The theorem *)

(* Deflate.inflateBytes on Rocq values: the output, the bits taken, and the
   zlib flag *)
Definition lean_inflate (bytes : list Z) : option (list Z * Z * bool) :=
  match Deflate_inflateBytes (arrU8 bytes) with
  | Option_none_inst1 _ => None
  | Option_some_inst1 _ d => Some (fromU8 (out d), V (bits d), B2b (zlib d))
  end.

Lemma dout a b c : out (Deflate_Decoded_mk a b c) = a.
Proof. reflexivity. Qed.
Lemma dbits a b c : bits (Deflate_Decoded_mk a b c) = b.
Proof. reflexivity. Qed.
Lemma dzlib a b c : zlib (Deflate_Decoded_mk a b c) = c.
Proof. reflexivity. Qed.

Theorem inflateZ_eq bytes : Forall (fun b => 0 <= b < 256) bytes -> inflateZ bytes = lean_inflate bytes.
Proof.
  intros Hb. unfold inflateZ, blocksF, lean_inflate.
  rewrite (of_leq (Deflate_InflateExport_inflateBytes_def _)), (of_leq (Deflate_InflateExport_inflate_def _)).
  pose proof (blocks_R bytes Hb (Z.to_nat (nbits bytes - 0) + 1) (L# 0) 0 [] true
                ltac:(vlits; reflexivity) (Forall_nil _) ltac:(lia)) as HB.
  change (arrU8 []) with (List_toArray_inst1 UInt8 (List_nil_inst1 UInt8)) in HB.
  change (Bb true) with Bool_true in HB.
  destruct (blocksZ bytes _ 0 [] true) as [[[o q] z]|];
    cbv [R embB okB] in HB; [destruct HB as [HB [Ho Hq]]|]; rewrite HB; mred; [|reflexivity].
  cbv iota beta. rewrite ?dout, ?dbits, ?dzlib.
  first [ (rewrite fromU8_arrU8, V_LN, B2b_Bb by auto; reflexivity)
        | (match goal with |- ?g => idtac "FINAL" g end; fail) ].
Qed.


