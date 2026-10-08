(* Pure facts for the VST proof of dynamic() (Verif_dynamic.v). *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model VPuff.Spec_puff.
Require VPuff.Inflate VPuff.Bridge.
Import VPuff.Inflate.
Open Scope Z_scope.

(** * Counting lengths *)

Lemma Dyn_cntZ_succ len n l :
  cntZ len (S n) l = cntZ len n l + (if len (Z.of_nat n) =? l then 1 else 0).
Proof. reflexivity. Qed.

Fixpoint Dyn_sumc (c : Z -> Z) (k : nat) : Z :=
  match k with O => 0 | S k => Dyn_sumc c k + c (Z.of_nat k) end.

Lemma Dyn_sumc_ind x (k : nat) : 0 <= x ->
  Dyn_sumc (fun l => if x =? l then 1 else 0) k = if x <? Z.of_nat k then 1 else 0.
Proof.
  intros Hx. induction k as [|k IH]; cbn [Dyn_sumc].
  - change (Z.of_nat 0) with 0.
    destruct (x <? 0) eqn:E; [apply Z.ltb_lt in E; lia|reflexivity].
  - rewrite IH.
    destruct (x <? Z.of_nat k) eqn:E1, (x =? Z.of_nat k) eqn:E2, (x <? Z.of_nat (S k)) eqn:E3;
      rewrite ?Z.ltb_lt, ?Z.ltb_ge, ?Z.eqb_eq, ?Z.eqb_neq in *; lia.
Qed.

Lemma Dyn_sumc_add a b k : Dyn_sumc (fun l => a l + b l) k = Dyn_sumc a k + Dyn_sumc b k.
Proof. induction k; cbn [Dyn_sumc]; [lia|]. rewrite IHk. lia. Qed.

Lemma Dyn_sumc_cnt_succ len n k :
  Dyn_sumc (cntZ len (S n)) k =
    Dyn_sumc (cntZ len n) k + Dyn_sumc (fun l => if len (Z.of_nat n) =? l then 1 else 0) k.
Proof. induction k; cbn [Dyn_sumc]; [lia|]. rewrite IHk. cbn [cntZ]. lia. Qed.

(* with every length in 0..15, the 16 counts add up to the number of lengths *)
Lemma Dyn_sum_counts len n :
  (forall i, 0 <= i < Z.of_nat n -> 0 <= len i <= 15) ->
  Dyn_sumc (cntZ len n) 16 = Z.of_nat n.
Proof.
  induction n as [|n IH]; intros H.
  - reflexivity.
  - rewrite Dyn_sumc_cnt_succ, IH by (intros; apply H; lia).
    specialize (H (Z.of_nat n) ltac:(lia)).
    rewrite Dyn_sumc_ind by lia.
    destruct (len (Z.of_nat n) <? Z.of_nat 16) eqn:E; [|apply Z.ltb_ge in E; lia]. lia.
Qed.

Lemma Dyn_cnt_nonneg len n l : 0 <= cntZ len n l.
Proof. induction n; cbn [cntZ]; [lia|]. destruct (_ =? _); lia. Qed.

(* the Kraft sum of 15 lengths, written out *)
Lemma Dyn_kr15 c : krZ c 15 =
  c 1 * 16384 + c 2 * 8192 + c 3 * 4096 + c 4 * 2048 + c 5 * 1024 + c 6 * 512 + c 7 * 256 +
  c 8 * 128 + c 9 * 64 + c 10 * 32 + c 11 * 16 + c 12 * 8 + c 13 * 4 + c 14 * 2 + c 15.
Proof. cbn. lia. Qed.

Lemma Dyn_sum16 c : Dyn_sumc c 16 =
  c 0 + c 1 + c 2 + c 3 + c 4 + c 5 + c 6 + c 7 + c 8 + c 9 + c 10 + c 11 + c 12 + c 13 + c 14 + c 15.
Proof. cbn. lia. Qed.

(** * construct()'s counts are cntOf/krOf *)

Lemma Dyn_Znth_countsOf lens l : 0 <= l < 16 -> Znth l (countsOf lens) = cntOf lens l.
Proof.
  intros Hl. unfold countsOf, cntOf, lenF.
  rewrite Znth_map by (rewrite Zlength_map, Zlength_correct, seq_length; cbn; lia).
  rewrite Znth_map by (rewrite Zlength_correct, seq_length; cbn; lia).
  f_equal. rewrite <- (Z2Nat.id l) at 1 by lia.
  rewrite <- nth_Znth'. unfold default, Inhabitant_nat. rewrite seq_nth by lia. cbn. lia.
Qed.

Lemma Dyn_kr_countsOf lens : krZ (countF (countsOf lens)) 15 = krOf lens.
Proof.
  unfold krOf. rewrite !Dyn_kr15. unfold countF.
  rewrite !Dyn_Znth_countsOf by lia. reflexivity.
Qed.

(* every length in 0..15 *)
Definition Dyn_lens_ok (lens : list Z) : Prop := Forall (fun x => 0 <= x <= 15) lens.

Lemma Dyn_sum_cntOf lens : Dyn_lens_ok lens ->
  cntOf lens 0 + cntOf lens 1 + cntOf lens 2 + cntOf lens 3 + cntOf lens 4 + cntOf lens 5 +
  cntOf lens 6 + cntOf lens 7 + cntOf lens 8 + cntOf lens 9 + cntOf lens 10 + cntOf lens 11 +
  cntOf lens 12 + cntOf lens 13 + cntOf lens 14 + cntOf lens 15 = Zlength lens.
Proof.
  intros H. rewrite <- (Dyn_sum16 (cntOf lens)). unfold cntOf.
  change (Dyn_sumc (fun l => cntZ (fun i => Znth i lens) (Z.to_nat (Zlength lens)) l) 16)
    with (Dyn_sumc (cntZ (fun i => Znth i lens) (Z.to_nat (Zlength lens))) 16).
  rewrite Dyn_sum_counts. { rewrite Z2Nat.id; [lia|apply Zlength_nonneg]. }
  intros i Hi. rewrite Z2Nat.id in Hi by apply Zlength_nonneg.
  unfold Dyn_lens_ok in H. rewrite Forall_Znth in H. apply H. lia.
Qed.

(** * puff's checks after construct() are the spec's notOversub and zlibOk *)

(* construct()'s return value, as construct_spec states it *)
Definition Dyn_cons_ok (lens : list Z) (r : Z) : Prop :=
  (r < 0 <-> 32768 < krZ (countF (countsOf lens)) 15) /\
  (0 <= r -> (r = 0 <-> (Znth 0 (countsOf lens) = Zlength lens \/
                          krZ (countF (countsOf lens)) 15 = 32768))).

(* the code length code: puff requires construct() to return 0 *)
Lemma Dyn_cl_check lens r : Dyn_cons_ok lens r ->
  (r = 0 <-> andb (notOversubZ lens) (zlibOkZ lens true) = true).
Proof.
  intros [H1 H2]. rewrite Dyn_kr_countsOf, Dyn_Znth_countsOf in * by lia.
  unfold notOversubZ, zlibOkZ. simpl negb. rewrite andb_false_l, orb_false_r.
  rewrite andb_true_iff, orb_true_iff, Z.leb_le, !Z.eqb_eq.
  split.
  - intros ->. specialize (H2 ltac:(lia)). destruct H2 as [H2 _]. specialize (H2 eq_refl).
    split; [|destruct H2; auto]. destruct (Z_lt_le_dec 32768 (krOf lens)); [|lia].
    apply H1 in l. lia.
  - intros [Hk Hz]. destruct (Z_lt_le_dec r 0) as [Hr|Hr].
    + apply H1 in Hr. lia.
    + apply (proj2 (H2 Hr)). destruct Hz; auto.
Qed.

(* the literal/length and distance codes: puff fails when
   err && (err < 0 || n != count[0] + count[1]) *)
Lemma Dyn_lit_check lens r : Dyn_lens_ok lens -> Dyn_cons_ok lens r ->
  ((r = 0 \/ (0 < r /\ Zlength lens = Znth 0 (countsOf lens) + Znth 1 (countsOf lens))) <->
   andb (notOversubZ lens) (zlibOkZ lens false) = true).
Proof.
  intros Hok [H1 H2]. rewrite Dyn_kr_countsOf, !Dyn_Znth_countsOf in * by lia.
  pose proof (Dyn_sum_cntOf lens Hok) as Hs.
  pose proof (Dyn_kr15 (cntOf lens)) as Hk. fold (krOf lens) in Hk.
  assert (Hn : forall l, 0 <= cntOf lens l) by (intros; apply Dyn_cnt_nonneg).
  pose proof (Hn 0); pose proof (Hn 1); pose proof (Hn 2); pose proof (Hn 3); pose proof (Hn 4);
  pose proof (Hn 5); pose proof (Hn 6); pose proof (Hn 7); pose proof (Hn 8); pose proof (Hn 9);
  pose proof (Hn 10); pose proof (Hn 11); pose proof (Hn 12); pose proof (Hn 13); pose proof (Hn 14);
  pose proof (Hn 15).
  unfold notOversubZ, zlibOkZ. simpl negb. rewrite andb_true_l.
  rewrite andb_true_iff, !orb_true_iff, andb_true_iff, Z.leb_le, !Z.eqb_eq.
  split.
  - intros [->|[Hr Hc]].
    + specialize (H2 ltac:(lia)). destruct H2 as [H2 _]. specialize (H2 eq_refl).
      assert (krOf lens <= 32768).
      { destruct (Z_lt_le_dec 32768 (krOf lens)) as [l|l]; [apply H1 in l; lia|lia]. }
      split; [lia|]. destruct H2; auto.
    + assert (krOf lens <= 32768).
      { destruct (Z_lt_le_dec 32768 (krOf lens)) as [l|l]; [apply H1 in l; lia|lia]. }
      split; [lia|]. lia.
  - intros [Hle Hz].
    destruct (Z_lt_le_dec r 0) as [Hr|Hr]; [apply H1 in Hr; lia|].
    destruct (Z.eq_dec r 0) as [->|Hr0]; [left; auto|]. right. split; [lia|].
    destruct Hz as [[Hz|Hz]|[Hz1 Hz2]].
    + exfalso. apply Hr0. apply (proj2 (H2 Hr)). auto.
    + exfalso. apply Hr0. apply (proj2 (H2 Hr)). auto.
    + lia.
Qed.

(** * The order table *)

Lemma Dyn_order_eq : orderTab = clOrderZ.
Proof. reflexivity. Qed.

Lemma Dyn_order_range k : 0 <= k < 19 -> 0 <= Znth k orderTab < 19.
Proof.
  intros Hk. assert (H : Forall (fun x => 0 <= x < 19) orderTab) by (repeat constructor; lia).
  rewrite Forall_Znth in H. apply H. unfold orderTab. cbn. lia.
Qed.

Lemma Dyn_order_cover j : 0 <= j < 19 -> exists k, 0 <= k < 19 /\ Znth k orderTab = j.
Proof.
  intros Hj. assert (Hin : In j orderTab).
  { assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/
            j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/ j = 18)
      as Hc by lia.
    unfold orderTab; repeat (destruct Hc as [->|Hc]; [cbn; tauto|]); subst; cbn; tauto. }
  apply In_Znth in Hin. destruct Hin as (k & Hk & Hz). exists k. split; [|auto].
  unfold orderTab in Hk. cbn in Hk. lia.
Qed.

(** * Bits *)

Lemma Dyn_lsb_range bytes p n : 0 <= lsbZ bytes p n < 2 ^ Z.of_nat n.
Proof.
  revert p; induction n as [|n IH]; intros p; cbn [lsbZ].
  - cbn. lia.
  - specialize (IH (p + 1)). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    destruct (bitZ bytes p); lia.
Qed.

Lemma Dyn_getbits_some bytes p n : p + n <= nbits bytes ->
  getbitsZ bytes p n = Some (lsbZ bytes p (Z.to_nat n)).
Proof. intros H. unfold getbitsZ. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.

Lemma Dyn_getbits_none bytes p n : nbits bytes < p + n -> getbitsZ bytes p n = None.
Proof. intros H. unfold getbitsZ. rewrite (proj2 (Z.leb_gt _ _) H). reflexivity. Qed.

(** * readLensZ: enough fuel is enough *)

Lemma Dyn_readLens_fuel cl bytes total : forall f1 f2 p acc,
  (Z.to_nat (total - Zlength acc) < f1)%nat -> (Z.to_nat (total - Zlength acc) < f2)%nat ->
  readLensZ cl bytes f1 p total acc = readLensZ cl bytes f2 p total acc.
Proof.
  induction f1 as [|f1 IH]; intros f2 p acc H1 H2; [lia|].
  destruct f2 as [|f2]; [lia|].
  cbn [readLensZ].
  destruct (total <=? Zlength acc) eqn:Et; [reflexivity|]. apply Z.leb_gt in Et.
  destruct (lean_decode cl bytes p) as [[s p1]|]; [|reflexivity].
  destruct (s <? 16).
  - apply IH; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
  - unfold getbitsZ.
    destruct (_ <=? _); [|reflexivity].
    set (e := lsbZ _ _ _).
    assert (0 <= e) by apply Dyn_lsb_range.
    destruct (if s =? 16 then lastZ acc else Some 0) as [v|]; [|reflexivity].
    destruct (Zlength acc + _ <=? total); [|reflexivity].
    apply IH; rewrite Zlength_app, Zlength_Zrepeat by (destruct (s =? 18); lia);
      destruct (s =? 18); lia.
Qed.

(** * The dynamic block header, taken apart *)

Definition Dyn_hdr_ok (bytes : list Z) (p : Z) (lit dist : list Z) (q : Z) : Prop :=
  exists hlit hdist hclen cl q1 lens,
    getbitsZ bytes p 5 = Some hlit /\ getbitsZ bytes (p + 5) 5 = Some hdist /\
    getbitsZ bytes (p + 10) 4 = Some hclen /\
    hlit + 257 <= 286 /\ hdist + 1 <= 30 /\
    readCLZ bytes (p + 14) (hclen + 4) = Some (cl, q1) /\
    andb (notOversubZ cl) (zlibOkZ cl true) = true /\
    readLensZ cl bytes (Z.to_nat (hlit + 257 + (hdist + 1)) + 1) q1 (hlit + 257 + (hdist + 1)) [] =
      Some (lens, q) /\
    lit = sublist 0 (hlit + 257) lens /\
    dist = sublist (hlit + 257) (hlit + 257 + (hdist + 1)) lens /\
    Znth 256 lit <> 0 /\
    andb (notOversubZ lit) (zlibOkZ lit false) = true /\
    andb (notOversubZ dist) (zlibOkZ dist false) = true.

Lemma Dyn_hdr_iff bytes p lit dist q :
  dynHeaderZ bytes p = Some (lit, dist, q, true) <-> Dyn_hdr_ok bytes p lit dist q.
Proof.
  unfold dynHeaderZ, Dyn_hdr_ok. split.
  - intros H.
    destruct (getbitsZ bytes p 5) as [hlit|] eqn:E1; [|discriminate].
    destruct (getbitsZ bytes (p + 5) 5) as [hdist|] eqn:E2; [|discriminate].
    destruct (getbitsZ bytes (p + 10) 4) as [hclen|] eqn:E3; [|discriminate].
    destruct (hlit + 257 <=? 286) eqn:E4; [|discriminate].
    destruct (readCLZ bytes (p + 14) (hclen + 4)) as [[cl q1]|] eqn:E5; [|discriminate].
    destruct (notOversubZ cl) eqn:E6; [|discriminate].
    destruct (readLensZ _ _ _ _ _ _) as [[lens r]|] eqn:E7; [|discriminate].
    destruct (negb _ && _)%bool eqn:E8; [|discriminate].
    injection H as Hl Hd Hq Hz.
    repeat match goal with
           | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
           end.
    exists hlit, hdist, hclen, cl, q1, lens.
    repeat match goal with H : negb _ = true |- _ => apply negb_true_iff, Z.eqb_neq in H end.
    repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
    subst. repeat split; auto; apply andb_true_iff; auto.
  - intros (hlit & hdist & hclen & cl & q1 & lens & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & Hl & Hd & E9
            & E10 & E11).
    rewrite E1, E2, E3, (proj2 (Z.leb_le _ _) E4), E6.
    apply andb_true_iff in E7. destruct E7 as [E7a E7b]. rewrite E7a, E8.
    subst lit dist.
    apply andb_true_iff in E10, E11. destruct E10 as [E10a E10b]. destruct E11 as [E11a E11b].
    rewrite (proj2 (Z.eqb_neq _ _) E9), E10a, E11a, E7b, E10b, E11b, (proj2 (Z.leb_le _ _) E5).
    reflexivity.
Qed.

(* the block's result as dynamic_spec states it *)
Definition Dyn_res (bytes : list Z) (p : Z) (out : list Z) : option (list Z * Z) :=
  match dynHeaderZ bytes p with
  | Some (lit, dist, q, true) => symsF lit dist bytes q out
  | _ => None
  end.

Lemma Dyn_res_none bytes p out :
  (forall lit dist q, ~ Dyn_hdr_ok bytes p lit dist q) -> Dyn_res bytes p out = None.
Proof.
  intros H. unfold Dyn_res.
  destruct (dynHeaderZ bytes p) as [[[[lit dist] q] [|]]|] eqn:E; auto.
  exfalso. apply (H lit dist q). apply Dyn_hdr_iff. auto.
Qed.

Lemma Dyn_res_some bytes p out lit dist q :
  Dyn_hdr_ok bytes p lit dist q -> Dyn_res bytes p out = symsF lit dist bytes q out.
Proof. intros H. apply Dyn_hdr_iff in H. unfold Dyn_res. rewrite H. reflexivity. Qed.
