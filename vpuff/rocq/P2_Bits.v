(* Bit-level facts about the mirror's lsbZ (Inflate.v), for the VST proofs of
   bits() and stored(). Every equation is proved bit by bit (Z.bits_inj'). *)
Require Import VST.floyd.proofauto.
Require Import VPuff.Model.
Require VPuff.Inflate.
Open Scope Z_scope.

Notation lsbZ := VPuff.Inflate.lsbZ.

Lemma testbit_small x m j : 0 <= x < 2 ^ m -> 0 <= m <= j -> Z.testbit x j = false.
Proof.
  intros Hx Hj. destruct (Z.eq_dec x 0) as [->|Hne]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  apply Z.lt_le_trans with m; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma testbit_b2z_2 (b : bool) x i : 0 <= i ->
  Z.testbit (Z.b2z b + 2 * x) i = if i =? 0 then b else Z.testbit x (i - 1).
Proof.
  intros Hi. rewrite Z.add_comm.
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Z.eqb_refl. destruct b; cbn [Z.b2z].
    + apply Z.testbit_odd_0.
    + rewrite Z.add_0_r. apply Z.testbit_even_0.
  - rewrite (proj2 (Z.eqb_neq _ _) Hne).
    replace i with (Z.succ (i - 1)) at 1 by lia.
    destruct b; cbn [Z.b2z].
    + apply Z.testbit_odd_succ; lia.
    + rewrite Z.add_0_r. apply Z.testbit_even_succ; lia.
Qed.

Lemma lsbZ_testbit bytes n : forall p i, 0 <= i ->
  Z.testbit (lsbZ bytes p n) i = andb (i <? Z.of_nat n) (bitZ bytes (p + i)).
Proof.
  induction n as [|n IH]; intros p i Hi.
  - cbn [VPuff.Inflate.lsbZ]. rewrite Z.bits_0.
    destruct (i <? Z.of_nat 0) eqn:E; [apply Z.ltb_lt in E; lia|reflexivity].
  - cbn [VPuff.Inflate.lsbZ].
    replace ((if bitZ bytes p then 1 else 0) + 2 * lsbZ bytes (p + 1) n)
      with (Z.b2z (bitZ bytes p) + 2 * lsbZ bytes (p + 1) n)
      by (destruct (bitZ bytes p); reflexivity).
    rewrite testbit_b2z_2 by lia.
    destruct (Z.eq_dec i 0) as [->|Hne].
    + rewrite Z.eqb_refl, Z.add_0_r.
      destruct (0 <? Z.of_nat (S n)) eqn:E; [reflexivity|apply Z.ltb_ge in E; lia].
    + rewrite (proj2 (Z.eqb_neq _ _) Hne), IH by lia.
      replace (p + 1 + (i - 1)) with (p + i) by lia.
      destruct (i - 1 <? Z.of_nat n) eqn:E1, (i <? Z.of_nat (S n)) eqn:E2; auto;
        rewrite ?Z.ltb_lt, ?Z.ltb_ge in *; lia.
Qed.

Lemma lsbZ_bound bytes n p : 0 <= lsbZ bytes p n < 2 ^ Z.of_nat n.
Proof.
  revert p; induction n as [|n IH]; intros p; cbn [VPuff.Inflate.lsbZ].
  - simpl; lia.
  - specialize (IH (p + 1)). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    destruct (bitZ bytes p); lia.
Qed.

(* the unused bits of the last byte read *)
Lemma shiftr_byte_lsbZ bytes k b :
  Forall (fun x => 0 <= x < 256) bytes -> 1 <= k <= Zlength bytes -> 0 <= b <= 8 ->
  Z.shiftr (Znth (k - 1) bytes) (8 - b) = lsbZ bytes (8 * k - b) (Z.to_nat b).
Proof.
  intros Hb Hk Hbb.
  assert (Hx : 0 <= Znth (k - 1) bytes < 2 ^ 8)
    by (rewrite Forall_Znth in Hb; specialize (Hb (k - 1) ltac:(lia)); cbv beta in Hb; simpl; lia).
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec, lsbZ_testbit by lia.
  rewrite Z2Nat.id by lia.
  destruct (i <? b) eqn:E.
  - apply Z.ltb_lt in E. unfold bitZ.
    replace ((8 * k - b + i) / 8) with (k - 1).
    + replace ((8 * k - b + i) mod 8) with (i + (8 - b)); [reflexivity|].
      rewrite Zmod_eq_full by lia.
      replace ((8 * k - b + i) / 8) with (k - 1); [lia|].
      apply Z.div_unique_pos with (i + (8 - b)); lia.
    + apply Z.div_unique_pos with (i + (8 - b)); lia.
  - apply Z.ltb_ge in E. cbn [andb].
    apply testbit_small with 8; lia.
Qed.

(* bits() loads the next byte above the bits it has *)
Lemma lsbZ_or_byte bytes p c k :
  Forall (fun x => 0 <= x < 256) bytes -> 0 <= k < Zlength bytes -> 0 <= c -> p + c = 8 * k ->
  Z.lor (lsbZ bytes p (Z.to_nat c)) (Z.shiftl (Znth k bytes) c) = lsbZ bytes p (Z.to_nat (c + 8)).
Proof.
  intros Hb Hk Hc Hp.
  assert (Hx : 0 <= Znth k bytes < 2 ^ 8)
    by (rewrite Forall_Znth in Hb; specialize (Hb k ltac:(lia)); cbv beta in Hb; simpl; lia).
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.lor_spec, !lsbZ_testbit, Z.shiftl_spec by lia.
  rewrite !Z2Nat.id by lia.
  destruct (i <? c) eqn:E1.
  - apply Z.ltb_lt in E1.
    rewrite (proj2 (Z.ltb_lt i (c + 8))) by lia.
    rewrite (Z.testbit_neg_r (Znth k bytes) (i - c)) by lia.
    rewrite orb_false_r. reflexivity.
  - apply Z.ltb_ge in E1. cbn [andb orb].
    destruct (i <? c + 8) eqn:E2.
    + apply Z.ltb_lt in E2. cbn [andb]. unfold bitZ.
      replace ((p + i) / 8) with k by (apply Z.div_unique_pos with (i - c); lia).
      replace ((p + i) mod 8) with (i - c); [reflexivity|].
      rewrite Zmod_eq_full by lia.
      replace ((p + i) / 8) with k by (apply Z.div_unique_pos with (i - c); lia). lia.
    + apply Z.ltb_ge in E2. cbn [andb]. apply testbit_small with 8; lia.
Qed.

Lemma lsbZ_shiftr bytes p c n : 0 <= n <= c ->
  Z.shiftr (lsbZ bytes p (Z.to_nat c)) n = lsbZ bytes (p + n) (Z.to_nat (c - n)).
Proof.
  intros Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec, !lsbZ_testbit by lia. rewrite !Z2Nat.id by lia.
  replace (p + (i + n)) with (p + n + i) by lia.
  destruct (i + n <? c) eqn:E1, (i <? c - n) eqn:E2; auto;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *; lia.
Qed.

Lemma lsbZ_land bytes p c n : 0 <= n <= c ->
  Z.land (lsbZ bytes p (Z.to_nat c)) (Z.ones n) = lsbZ bytes p (Z.to_nat n).
Proof.
  intros Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !lsbZ_testbit by lia. rewrite !Z2Nat.id by lia.
  destruct (i <? n) eqn:E.
  - apply Z.ltb_lt in E. rewrite Z.ones_spec_low by lia.
    rewrite (proj2 (Z.ltb_lt i c)) by lia. rewrite andb_true_r. reflexivity.
  - apply Z.ltb_ge in E. rewrite Z.ones_spec_high by lia. rewrite andb_false_r. reflexivity.
Qed.

Lemma lsbZ_zero bytes p : lsbZ bytes p 0 = 0.
Proof. reflexivity. Qed.
