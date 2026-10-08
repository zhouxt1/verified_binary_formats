(* The Rocq model (Model.v) is the imported Lean model, and through Lean's
   theorem Deflate.Puff.decode_eq it computes the imported Lean spec.

   lean_decode and lean_notOversub below are the Lean spec's decodeSym and
   notOversub on Rocq lists; they are what the C contracts are stated against. *)
From LeanImport Require Import Lean.
Require Import VPuff.LeanSpec VPuff.LeanNat VPuff.Model.
Close Scope Nat_scope. Close Scope lean_scope.
From Stdlib Require Import ZArith List Lia.
From VST.zlist Require Import sublist.
Import ListNotations.
Open Scope Z_scope.

(** * Rocq lists as Lean arrays *)

Fixpoint toL {A B : Type} (f : A -> B) (l : list A) : List_inst1 B :=
  match l with nil => List_nil_inst1 B | cons x t => List_cons_inst1 B (f x) (toL f t) end.

Definition arrN (l : list Z) : Array_inst1 Nat := Array_mk_inst1 Nat (toL LN l).
Definition arrU8 (l : list Z) : Array_inst1 UInt8 :=
  Array_mk_inst1 UInt8 (toL (fun z => UInt8_ofNat (LN z)) l).

(** The Lean spec on Rocq values. *)
Definition Vopt (o : Option_inst1 (Prod_inst3 Nat Nat)) : option (Z * Z) :=
  match o with
  | Option_none_inst1 _ => None
  | Option_some_inst1 _ x => Some (V (fst1 _ _ x), V (snd1 _ _ x))
  end.

(* Deflate.decodeSym (Deflate.code lens) (Deflate.bitsOf bytes) p *)
Definition lean_decode (lens bytes : list Z) (p : Z) : option (Z * Z) :=
  Vopt (Deflate_decodeSym (Deflate_code (arrN lens)) (Deflate_bitsOf (arrU8 bytes)) (LN p)).

(* Deflate.notOversub lens *)
Definition lean_notOversub (lens : list Z) : bool := B2b (Deflate_notOversub (arrN lens)).

(** * Unfolding equations, from the exported Lean theorems *)

Section Eqns.
Local Abbreviation lgetD := Deflate_Puff_Export_lgetD.

Lemma lgetD_nil' {B} i (d : B) : lgetD B (List_nil_inst1 B) i d = d.
Proof. exact (of_leq (Deflate_Puff_Export_lgetD_nil B i d)). Qed.
Lemma lgetD_zero' {B} x l (d : B) : lgetD B (List_cons_inst1 B x l) Nat_zero d = x.
Proof. exact (of_leq (Deflate_Puff_Export_lgetD_zero B x l d)). Qed.
Lemma lgetD_succ' {B} x l i (d : B) :
  lgetD B (List_cons_inst1 B x l) (Nat_succ i) d = lgetD B l i d.
Proof. exact (of_leq (Deflate_Puff_Export_lgetD_succ B x l i d)). Qed.
Lemma getD_mk' {B} l i (d : B) : Array_getD_inst1 B (Array_mk_inst1 B l) i d = lgetD B l i d.
Proof. exact (of_leq (Deflate_Puff_Export_getD_mk B l i d)). Qed.
Lemma size_mk' {B} l : Array_size_inst1 B (Array_mk_inst1 B l) = List_length_inst1 B l.
Proof. exact (of_leq (Deflate_Puff_Export_size_mk B l)). Qed.
Lemma length_cons {B} x l : List_length_inst1 B (List_cons_inst1 B x l) = Nat_succ (List_length_inst1 B l).
Proof. reflexivity. Qed.
Lemma length_nil {B} : List_length_inst1 B (List_nil_inst1 B) = Nat_zero.
Proof. reflexivity. Qed.

Lemma cnt_zero' len l : Deflate_Puff_cnt len Nat_zero l = Nat_zero.
Proof. exact (of_leq (Deflate_Puff_Export_cnt_zero len l)). Qed.
Lemma cnt_succ' len n l :
  Deflate_Puff_cnt len (Nat_succ n) l =
    Deflate_Puff_cnt len n l +L cond Nat (Nat_beq (len n) l) (Nat_succ Nat_zero) Nat_zero.
Proof. exact (of_leq (Deflate_Puff_Export_cnt_succ len n l)). Qed.

Lemma offs_zero' c : Deflate_Puff_offs c Nat_zero = Nat_zero.
Proof. exact (of_leq (Deflate_Puff_Export_offs_zero c)). Qed.
Lemma offs_one' c : Deflate_Puff_offs c (Nat_succ Nat_zero) = Nat_zero.
Proof. exact (of_leq (Deflate_Puff_Export_offs_one c)). Qed.
Lemma offs_succ' c l :
  Deflate_Puff_offs c (Nat_succ (Nat_succ l)) = Deflate_Puff_offs c (Nat_succ l) +L c (Nat_succ l).
Proof. exact (of_leq (Deflate_Puff_Export_offs_succ c l)). Qed.

Lemma kr_zero' c : Deflate_Puff_kr c Nat_zero = Nat_zero.
Proof. exact (of_leq (Deflate_Puff_Export_kr_zero c)). Qed.
Lemma kr_succ' c L :
  Deflate_Puff_kr c (Nat_succ L) = L# 2 *L Deflate_Puff_kr c L +L c (Nat_succ L).
Proof. exact (of_leq (Deflate_Puff_Export_kr_succ c L)). Qed.

Lemma go_zero' count symbol bit nbits p len cd first index :
  Deflate_Puff_go count symbol bit nbits p Nat_zero len cd first index = Option_none_inst1 _.
Proof. exact (of_leq (Deflate_Puff_Export_go_zero count symbol bit nbits p len cd first index)). Qed.

Definition bitv (bit : Nat -> Bool) (p len : Nat) : Nat :=
  cond Nat (bit (p +L len -L L# 1)) (L# 1) (L# 0).

Lemma go_succ' count symbol bit nbits p k len cd first index :
  Deflate_Puff_go count symbol bit nbits p (Nat_succ k) len cd first index =
  cond _ (Nat_blt nbits (p +L len)) (Option_none_inst1 _)
    (cond _ (Nat_blt (cd +L bitv bit p len) (first +L count len))
      (Option_some_inst1 _ (Prod_mk_inst3 Nat Nat
         (symbol (index +L (cd +L bitv bit p len -L first))) (p +L len)))
      (Deflate_Puff_go count symbol bit nbits p k (len +L L# 1)
         (L# 2 *L (cd +L bitv bit p len)) (L# 2 *L (first +L count len))
         (index +L count len))).
Proof. exact (of_leq (Deflate_Puff_Export_go_succ count symbol bit nbits p k len cd first index)). Qed.

Lemma decode_def' count symbol bit nbits p :
  Deflate_Puff_decode count symbol bit nbits p =
    Deflate_Puff_go count symbol bit nbits p (L# 15) (L# 1) (L# 0) (L# 0) (L# 0).
Proof. exact (of_leq (Deflate_Puff_Export_decode_def count symbol bit nbits p)). Qed.

Lemma byteBit_def' byte q :
  Deflate_Puff_byteBit byte q = Nat_testBit (byte (q /L L# 8)) (q %L L# 8).
Proof. exact (of_leq (Deflate_Puff_Export_byteBit_def byte q)). Qed.

End Eqns.

Lemma B2b_cond (c : Bool) (x y : bool) :
  B2b (cond Bool c (if x then Bool_true else Bool_false) (if y then Bool_true else Bool_false)) =
    if B2b c then x else y.
Proof. destruct c, x, y; reflexivity. Qed.

(** * Arrays *)

Lemma V_lgetD_toL (f : Z -> Nat) (l : list Z) (i : Nat) (d : Nat) :
  V (Deflate_Puff_Export_lgetD Nat (toL f l) i d) =
    if V i <? Zlength l then V (f (Znth (V i) l)) else V d.
Proof.
  revert i; induction l as [|x l IH]; intros i; cbn [toL].
  - rewrite lgetD_nil'; destruct (V i <? Zlength []) eqn:E; auto.
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

Lemma V_getD_arrN (l : list Z) (i : Nat) :
  Forall (fun x => 0 <= x) l ->
  V (Array_getD_inst1 Nat (arrN l) i (L# 0)) = Znth (V i) l.
Proof.
  intros Hl; unfold arrN; rewrite getD_mk'.
  change (L# 0) with Nat_zero; rewrite V_lgetD_toL.
  destruct (V i <? Zlength l) eqn:E.
  - apply Z.ltb_lt in E; rewrite V_LN; auto.
    apply Forall_Znth; auto. pose proof (V_nonneg i); lia.
  - apply Z.ltb_ge in E; rewrite Znth_overflow by lia; reflexivity.
Qed.

Lemma V_size_mk {A B} (f : A -> B) (l : list A) :
  V (Array_size_inst1 B (Array_mk_inst1 B (toL f l))) = Zlength l.
Proof.
  rewrite size_mk'; induction l as [|x l IH]; cbn [toL].
  - rewrite length_nil; reflexivity.
  - rewrite length_cons, V_succ, IH, Zlength_cons; lia.
Qed.

Lemma V_toNat_getD_arrU8 (l : list Z) (i : Nat) :
  Forall (fun x => 0 <= x < 256) l ->
  V (UInt8_toNat (Array_getD_inst1 UInt8 (arrU8 l) i (OfNat_ofNat_inst1 UInt8 Nat_zero (UInt8_instOfNat Nat_zero)))) =
    Znth (V i) l.
Proof.
  intros Hl; unfold arrU8; rewrite getD_mk'.
  revert i; induction l as [|x l IH]; intros i; cbn [toL].
  - rewrite lgetD_nil', (of_leq Deflate_Puff_Export_uint8_toNat_zero).
    rewrite Znth_nil; reflexivity.
  - inversion Hl as [|? ? Hx Hl']; subst.
    destruct i as [|i].
    + rewrite lgetD_zero', (of_leq (Deflate_Puff_Export_uint8_toNat_ofNat _)), V_mod by (vlits; lia).
      vlits; rewrite V_LN by lia; rewrite V_zero, Znth_0_cons, Z.mod_small; lia.
    + rewrite lgetD_succ', IH by auto.
      rewrite V_succ, Znth_pos_cons by (pose proof (V_nonneg i); lia).
      f_equal; lia.
Qed.

(** * The model, function by function *)

Section Iso.
Variables (lenL : Nat -> Nat) (lenZ : Z -> Z).
Hypothesis Hlen : forall x, V (lenL x) = lenZ (V x).

Lemma V_cnt n l : V (Deflate_Puff_cnt lenL n l) = cntZ lenZ (nat_of_Nat n) (V l).
Proof.
  induction n as [|n IH].
  - rewrite cnt_zero'; reflexivity.
  - rewrite cnt_succ', V_add, IH. cbn [nat_of_Nat cntZ].
    change (Z.of_nat (nat_of_Nat n)) with (V n). rewrite <- Hlen.
    destruct (Nat_beq (lenL n) l) eqn:E; pose proof (f_equal B2b E) as E'; rewrite B2b_beq in E';
      cbn [B2b] in E'; rewrite E'.
    + rewrite cond_false, V_zero; lia.
    + rewrite cond_true, V_succ, V_zero; lia.
Qed.
End Iso.

Section Iso2.
Variables (countL : Nat -> Nat) (countZ : Z -> Z).
Hypothesis Hcount : forall x, V (countL x) = countZ (V x).

Lemma V_offs_nat m : V (Deflate_Puff_offs countL (Nat_of_nat m)) = offsZ countZ m.
Proof.
  assert (H : forall k, V (Deflate_Puff_offs countL (Nat_of_nat k)) = offsZ countZ k /\
                        V (Deflate_Puff_offs countL (Nat_of_nat (S k))) = offsZ countZ (S k)).
  { clear m. intros m. induction m as [|m [IH1 IH2]].
    - split; [rewrite offs_zero'|cbn [Nat_of_nat]; rewrite offs_one']; reflexivity.
    - split; [exact IH2|].
      change (Nat_of_nat (S (S m))) with (Nat_succ (Nat_succ (Nat_of_nat m))).
      rewrite offs_succ', V_add, Hcount.
      change (Nat_succ (Nat_of_nat m)) with (Nat_of_nat (S m)).
      rewrite IH2, V_Nat_of_nat. reflexivity. }
  apply (H m).
Qed.

Lemma V_offs l : V (Deflate_Puff_offs countL l) = offsZ countZ (nat_of_Nat l).
Proof. rewrite <- (Nat2natid l) at 1; apply V_offs_nat. Qed.

Lemma V_kr L : V (Deflate_Puff_kr countL L) = krZ countZ (nat_of_Nat L).
Proof.
  induction L as [|L IH].
  - rewrite kr_zero'; reflexivity.
  - rewrite kr_succ', V_add, V_mul, IH, Hcount; vlits. cbn [nat_of_Nat krZ].
    rewrite V_succ. f_equal. f_equal. unfold V; lia.
Qed.

Variables (symbolL : Nat -> Nat) (symbolZ : Z -> Z) (bitL : Nat -> Bool) (bitZf : Z -> bool).
Hypothesis Hsymbol : forall x, V (symbolL x) = symbolZ (V x).
Hypothesis Hbit : forall x, B2b (bitL x) = bitZf (V x).
Variables (nbits p : Nat).

Lemma V_bitv len : 1 <= V len ->
  V (bitv bitL p len) = (if bitZf (V p + V len - 1) then 1 else 0) /\
  V (p +L len -L L# 1) = V p + V len - 1.
Proof.
  intros Hl.
  assert (E : V (p +L len -L L# 1) = V p + V len - 1)
    by (rewrite V_sub, V_add; vlits; pose proof (V_nonneg p); lia).
  split; [|exact E].
  unfold bitv. rewrite <- E, <- Hbit.
  destruct (bitL (p +L len -L L# 1)); [rewrite cond_false|rewrite cond_true]; vlits; reflexivity.
Qed.

Lemma V_go k : forall len cd first index,
  1 <= V len -> V first <= V cd ->
  Vopt (Deflate_Puff_go countL symbolL bitL nbits p k len cd first index) =
    goZ countZ symbolZ bitZf (V nbits) (V p) (nat_of_Nat k) (V len) (V cd) (V first) (V index).
Proof.
  induction k as [|k IH]; intros len cd first index Hlen Hfc.
  - rewrite go_zero'; reflexivity.
  - rewrite go_succ'. cbn [nat_of_Nat goZ].
    destruct (V_bitv len Hlen) as [Hb _].
    destruct (Nat_blt nbits (p +L len)) eqn:E1;
      pose proof (f_equal B2b E1) as E1'; rewrite B2b_blt, V_add in E1'; cbn [B2b] in E1';
      rewrite E1'; [rewrite cond_false | rewrite cond_true; reflexivity].
    set (b := bitv bitL p len) in *.
    destruct (Nat_blt (cd +L b) (first +L countL len)) eqn:E2;
      pose proof (f_equal B2b E2) as E2'; rewrite B2b_blt, !V_add, Hcount, Hb in E2';
      cbn [B2b] in E2'; rewrite E2'.
    + rewrite cond_false. rewrite IH.
      * rewrite !V_mul, !V_add, Hb, Hcount; vlits. reflexivity.
      * rewrite V_add; vlits; lia.
      * rewrite !V_mul, !V_add, Hcount, Hb; vlits.
        apply Z.ltb_ge in E2'. lia.
    + rewrite cond_true. cbn [Vopt fst1 snd1]. rewrite Hsymbol, V_add, V_sub, V_add, Hb, V_add.
      do 3 f_equal. destruct (bitZf _); lia.
Qed.

End Iso2.

(** * The Lean spec, on Rocq values *)

Lemma V_LN_fun (f : Z -> Z) : (forall z, 0 <= f z) -> forall x, V (LN (f (V x))) = f (V x).
Proof. intros H x; apply V_LN, H. Qed.

Lemma lt_LT a b : V a < V b -> LT_lt_inst1 Nat instLTNat a b.
Proof.
  intros H. change (LE_le_inst1 Nat instLENat (Nat_succ a) b).
  apply nat_le_Nat_le. unfold V in H. cbn [nat_of_Nat]. lia.
Qed.

(** Lean's theorem decode_eq, in Rocq terms: for tables as puff's construct
    builds them, decodeZ is the spec's decodeSym. *)
Theorem lean_decode_eq (lens bytes : list Z) (p : Z) (countZ symbolZ : Z -> Z) :
  Forall (fun x => 0 <= x) lens ->
  Forall (fun x => 0 <= x < 256) bytes ->
  0 <= p ->
  (forall z, 0 <= symbolZ z) ->
  (forall l, 0 <= l -> countZ l = cntZ (fun i => Znth i lens) (Z.to_nat (Zlength lens)) l) ->
  (forall s, 0 <= s < Zlength lens -> 1 <= Znth s lens ->
     symbolZ (offsZ countZ (Z.to_nat (Znth s lens)) +
              cntZ (fun i => Znth i lens) (Z.to_nat s) (Znth s lens)) = s) ->
  lean_decode lens bytes p = decodeZ countZ symbolZ (bitZ bytes) (8 * Zlength bytes) p.
Proof.
  intros Hlens Hbytes Hp Hsym Hc Hs.
  set (countL := fun x => LN (countZ (V x))).
  set (symbolL := fun x => LN (symbolZ (V x))).
  assert (Hcnn : forall l, 0 <= l -> 0 <= countZ l)
    by (intros; rewrite Hc by auto; apply cntZ_nonneg).
  assert (HcL : forall x, V (countL x) = countZ (V x))
    by (intros; apply V_LN, Hcnn, V_nonneg).
  assert (HsL : forall x, V (symbolL x) = symbolZ (V x)) by (intros; apply V_LN, Hsym).
  assert (Hlen : forall x, V (Array_getD_inst1 Nat (arrN lens) x (L# 0)) = Znth (V x) lens)
    by (intros; apply V_getD_arrN, Hlens).
  assert (Hsize : V (Array_size_inst1 Nat (arrN lens)) = Zlength lens) by apply V_size_mk.
  (* Lean's hypotheses: count is blCount, and symbol is puff's table *)
  assert (hc : forall l, eq (countL l) (Deflate_blCount (arrN lens) l)).
  { intros l. apply to_leq, V_inj.
    rewrite HcL, (of_leq (Deflate_Puff_blCount_eq_cnt _ _)).
    rewrite (V_cnt _ (fun i => Znth i lens) Hlen).
    rewrite Hc by apply V_nonneg. f_equal.
    rewrite <- Hsize; unfold V; rewrite Nat2Z.id; reflexivity. }
  assert (hs : forall s,
    LT_lt_inst1 Nat instLTNat s (Array_size_inst1 Nat (arrN lens)) ->
    LE_le_inst1 Nat instLENat (L# 1) (Array_getD_inst1 Nat (arrN lens) s (L# 0)) ->
    eq (symbolL (Deflate_Puff_offs countL (Array_getD_inst1 Nat (arrN lens) s (L# 0)) +L
                 Deflate_Puff_cnt (fun x => Array_getD_inst1 Nat (arrN lens) x (L# 0)) s
                   (Array_getD_inst1 Nat (arrN lens) s (L# 0)))) s).
  { intros s Hs1 Hs2. apply lt_V in Hs1. apply le_V in Hs2.
    rewrite Hsize in Hs1. rewrite Hlen in Hs2. vlits.
    apply to_leq, V_inj.
    rewrite HsL, V_add, (V_offs countL countZ HcL), (V_cnt _ (fun i => Znth i lens) Hlen), Hlen.
    replace (nat_of_Nat (Array_getD_inst1 Nat (arrN lens) s (L# 0))) with (Z.to_nat (Znth (V s) lens))
      by (rewrite <- Hlen; unfold V; lia).
    replace (nat_of_Nat s) with (Z.to_nat (V s)) by (unfold V; lia).
    apply Hs; pose proof (V_nonneg s); lia. }
  unfold lean_decode.
  rewrite <- (of_leq (Deflate_Puff_decode_eq (arrN lens) countL symbolL hc hs (arrU8 bytes) (LN p))).
  rewrite decode_def'.
  rewrite (V_go countL countZ HcL symbolL symbolZ _ (bitZ bytes) HsL).
  - unfold decodeZ. vlits. rewrite V_LN by lia.
    unfold arrU8. rewrite V_mul, V_size_mk; vlits.
    replace (Zlength bytes * 8) with (8 * Zlength bytes) by lia. reflexivity.
  - intros q. rewrite byteBit_def'.
    rewrite B2b_testBit, V_toNat_getD_arrU8 by auto.
    rewrite V_div, V_mod by (vlits; lia). vlits. reflexivity.
  - vlits; lia.
  - vlits; lia.
Qed.

(** Lean's notOversub, in Rocq terms. *)
Theorem lean_notOversub_eq (lens : list Z) :
  Forall (fun x => 0 <= x) lens ->
  lean_notOversub lens =
    (krZ (fun l => cntZ (fun i => Znth i lens) (Z.to_nat (Zlength lens)) l) 15 <=? 32768).
Proof.
  intros Hlens. unfold lean_notOversub.
  rewrite (of_leq (Deflate_Puff_Export_notOversub_eq _)), B2b_ble.
  assert (Hlen : forall x, V (Array_getD_inst1 Nat (arrN lens) x (L# 0)) = Znth (V x) lens)
    by (intros; apply V_getD_arrN, Hlens).
  assert (Hsize : V (Array_size_inst1 Nat (arrN lens)) = Zlength lens) by apply V_size_mk.
  rewrite (V_kr (Deflate_blCount (arrN lens))
             (fun l => cntZ (fun i => Znth i lens) (Z.to_nat (Zlength lens)) l)).
  - vlits. reflexivity.
  - intros x. rewrite (of_leq (Deflate_Puff_blCount_eq_cnt _ _)).
    rewrite (V_cnt _ (fun i => Znth i lens) Hlen). f_equal.
    rewrite <- Hsize; unfold V; rewrite Nat2Z.id; reflexivity.
Qed.
