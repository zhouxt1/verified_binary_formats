(* Facts that join puff's Huffman tables to the imported Lean spec, used by
   Verif_construct.v and Verif_decode.v (decode_spec is stated with the Lean
   decodeSym; the C computes the Rocq model of Model.v):

   - construct_verdict: construct returns a negative value exactly when the
     Lean spec's notOversub refuses the lengths;
   - construct_tables_decodable: what construct builds meets decode's
     preconditions;
   - decode_model_lean: on those tables, the model decode computes is the
     Lean spec's decodeSym (code lens) (bitsOf bytes). *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model VPuff.Spec_puff.
Require VPuff.Bridge.
Open Scope Z_scope.

(* the symbol table as a function: the entries decode can reach are the first n *)
Definition symF (syms : list val) (n : Z) (j : Z) : Z :=
  if andb (0 <=? j) (j <? n) then
    match Znth j syms with Vint v => Z.max 0 (Int.signed v) | _ => 0 end
  else 0.

(** * Counting *)

Lemma cntZ_succ len n l :
  cntZ len (S n) l = cntZ len n l + (if len (Z.of_nat n) =? l then 1 else 0).
Proof. reflexivity. Qed.

Lemma cntZ_mono len l (m n : nat) : (m <= n)%nat -> cntZ len m l <= cntZ len n l.
Proof.
  induction 1; [lia|]. rewrite cntZ_succ. destruct (_ =? _); lia.
Qed.

(* the symbol s comes before every later symbol of its length *)
Lemma cntZ_lt len (s n : nat) :
  (s < n)%nat -> cntZ len s (len (Z.of_nat s)) < cntZ len n (len (Z.of_nat s)).
Proof.
  intros H. pose proof (cntZ_mono len (len (Z.of_nat s)) (S s) n H).
  rewrite cntZ_succ, Z.eqb_refl in H0. lia.
Qed.

(* the c-th symbol of length l *)
Lemma cntZ_exists len l (N : nat) c :
  0 <= c < cntZ len N l -> exists m, (m < N)%nat /\ len (Z.of_nat m) = l /\ cntZ len m l = c.
Proof.
  induction N as [|N IH]; intros Hc; cbn [cntZ] in Hc; [lia|].
  destruct (len (Z.of_nat N) =? l) eqn:E.
  - apply Z.eqb_eq in E.
    destruct (Z.eq_dec c (cntZ len N l)) as [->|Hne].
    + exists N; split; [lia|]; split; auto.
    + destruct (IH ltac:(lia)) as (m & ? & ? & ?). exists m; split; [lia|auto].
  - destruct (IH ltac:(lia)) as (m & ? & ? & ?). exists m; split; [lia|auto].
Qed.

Lemma cntZ_none len (n : nat) l :
  (forall i, 0 <= i < Z.of_nat n -> len i <> l) -> cntZ len n l = 0.
Proof.
  induction n as [|n IH]; intros H; [reflexivity|].
  rewrite cntZ_succ, IH by (intros; apply H; lia).
  destruct (len (Z.of_nat n) =? l) eqn:E; [apply Z.eqb_eq in E; exfalso; apply (H (Z.of_nat n)); auto; lia|lia].
Qed.

(* how many of the symbols 0 .. n-1 have a length in [1, m) *)
Fixpoint rngZ (len : Z -> Z) (n : nat) (m : Z) : Z :=
  match n with
  | O => 0
  | S n' => rngZ len n' m + (if andb (1 <=? len (Z.of_nat n')) (len (Z.of_nat n') <? m) then 1 else 0)
  end.

Lemma rngZ_le len n m : 0 <= rngZ len n m <= Z.of_nat n.
Proof. induction n; cbn [rngZ]; [lia|]. destruct (andb _ _); lia. Qed.

Lemma rngZ_split len n m : 1 <= m -> rngZ len n (m + 1) = rngZ len n m + cntZ len n m.
Proof.
  intros Hm; induction n as [|n IH]; [reflexivity|].
  cbn [rngZ]; rewrite cntZ_succ, IH.
  destruct (1 <=? len (Z.of_nat n)) eqn:E1, (len (Z.of_nat n) <? m + 1) eqn:E2,
    (len (Z.of_nat n) <? m) eqn:E3, (len (Z.of_nat n) =? m) eqn:E4; cbn [andb];
    rewrite ?Z.leb_le, ?Z.leb_gt, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.eqb_eq, ?Z.eqb_neq in *; lia.
Qed.

(** * offs *)

Lemma offsZ_ext c1 c2 (m : nat) :
  (forall l, 1 <= l < Z.of_nat m -> c1 l = c2 l) -> offsZ c1 m = offsZ c2 m.
Proof.
  induction m as [|m IH]; intros H; [reflexivity|].
  destruct m as [|m]; [reflexivity|].
  rewrite !offsZ_succ by lia. rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma offsZ_mono c (m n : nat) :
  (forall l, 0 <= c l) -> (m <= n)%nat -> offsZ c m <= offsZ c n.
Proof.
  intros Hc; induction 1 as [|k Hk IH]; [lia|].
  destruct k as [|k]; [change (offsZ c 1) with 0; change (offsZ c 0) with 0 in IH; lia|].
  rewrite offsZ_succ by lia. specialize (Hc (Z.of_nat (S k))). lia.
Qed.

(* offs over the counts of the lengths: the symbols with a length in [1, m) *)
Lemma offsZ_cnt len (n m : nat) : (1 <= m)%nat ->
  offsZ (fun l => cntZ len n l) m = rngZ len n (Z.of_nat m).
Proof.
  intros Hm; induction m as [|m IH]; [lia|].
  destruct m as [|m].
  - cbn [offsZ]. change (Z.of_nat 1) with 1. clear IH Hm.
    induction n as [|n IHn]; [reflexivity|].
    cbn [rngZ]. rewrite <- IHn. destruct (andb _ _) eqn:E; [|lia].
    apply andb_true_iff in E; rewrite Z.leb_le, Z.ltb_lt in E; lia.
  - rewrite offsZ_succ, IH by lia.
    replace (Z.of_nat (S (S m))) with (Z.of_nat (S m) + 1) by lia.
    rewrite rngZ_split by lia. reflexivity.
Qed.

(* the positions [0, offs m) split into the blocks [offs l, offs l + c l) *)
Lemma offsZ_tile c (m : nat) j :
  (forall l, 0 <= c l) -> (1 <= m)%nat -> 0 <= j < offsZ c m ->
  exists l, 1 <= l < Z.of_nat m /\ offsZ c (Z.to_nat l) <= j < offsZ c (Z.to_nat l) + c l.
Proof.
  intros Hc; induction m as [|m IH]; intros Hm Hj; [lia|].
  destruct m as [|m]; [cbn in Hj; lia|].
  rewrite offsZ_succ in Hj by lia.
  destruct (Z_lt_dec j (offsZ c (S m))) as [Hlt|Hge].
  - destruct (IH ltac:(lia) ltac:(lia)) as (l & ? & ?). exists l; split; [lia|auto].
  - exists (Z.of_nat (S m)); split; [lia|]. rewrite Nat2Z.id. lia.
Qed.

(* stated for any counts, so the kernel never unfolds offsZ on concrete ones *)
Lemma ncodes_def c : ncodes c = offsZ (countF c) 16.
Proof. reflexivity. Qed.

(** * countsOf *)

Section Lens.
Variable lens : list Z.
Hypothesis Hlens : Forall (fun x => 0 <= x <= 15) lens.
Hypothesis Hn : Zlength lens <= 320.

Let n := Z.to_nat (Zlength lens).
Let C := fun l => cntZ (lenF lens) n l.

Lemma lens_range i : 0 <= i < Zlength lens -> 0 <= Znth i lens <= 15.
Proof. intros; apply Forall_Znth; auto. Qed.

Lemma Zlength_countsOf : Zlength (countsOf lens) = 16.
Proof. unfold countsOf; rewrite !Zlength_map; reflexivity. Qed.

Lemma Znth_countsOf l : 0 <= l < 16 -> Znth l (countsOf lens) = C l.
Proof.
  intros Hl. unfold countsOf, C.
  rewrite Znth_map by (rewrite Zlength_map; cbn; lia).
  rewrite Znth_map by (cbn; lia).
  f_equal. unfold Znth. destruct (Z_lt_dec l 0); [lia|].
  rewrite seq_nth by lia. lia.
Qed.

(* lengths are at most 15, so no symbol has a longer one *)
Lemma C_big l : 16 <= l -> C l = 0.
Proof.
  intros Hl; unfold C; apply cntZ_none; intros i Hi.
  unfold lenF; pose proof (lens_range i ltac:(unfold n in Hi; lia)); lia.
Qed.

Lemma countF_C l : 0 <= l -> countF (countsOf lens) l = C l.
Proof.
  intros Hl; unfold countF. destruct (Z_lt_dec l 16).
  - apply Znth_countsOf; lia.
  - rewrite Znth_overflow by (rewrite Zlength_countsOf; lia). rewrite C_big by lia. reflexivity.
Qed.

Lemma countsOf_range : Forall (fun c => 0 <= c <= 320) (countsOf lens).
Proof.
  apply Forall_Znth; intros l Hl; rewrite Zlength_countsOf in Hl.
  rewrite Znth_countsOf by lia. unfold C.
  pose proof (cntZ_nonneg (lenF lens) n l); pose proof (cntZ_le (lenF lens) n l).
  unfold n in *; rewrite Z2Nat.id in * by (apply Zlength_nonneg); lia.
Qed.

Lemma ncodes_eq : ncodes (countsOf lens) = rngZ (lenF lens) n 16.
Proof.
  rewrite ncodes_def, (offsZ_ext _ C) by (intros; apply countF_C; lia).
  apply offsZ_cnt; lia.
Qed.

Lemma ncodes_le : ncodes (countsOf lens) <= Zlength lens.
Proof.
  rewrite ncodes_eq. pose proof (rngZ_le (lenF lens) n 16). unfold n in *.
  rewrite Z2Nat.id in * by (apply Zlength_nonneg); lia.
Qed.

Lemma offs_C l : (l <= 16)%nat -> offsZ (countF (countsOf lens)) l = offsZ C l.
Proof. intros; apply offsZ_ext; intros; apply countF_C; lia. Qed.

(* where symbol s sits *)
Definition pos (s : Z) : Z :=
  offsZ (countF (countsOf lens)) (Z.to_nat (Znth s lens)) + cntZ (lenF lens) (Z.to_nat s) (Znth s lens).

Lemma pos_range s : 0 <= s < Zlength lens -> 1 <= Znth s lens ->
  0 <= pos s < ncodes (countsOf lens).
Proof.
  intros Hs H1. pose proof (lens_range s Hs) as Hl.
  unfold pos, ncodes. rewrite !offs_C by lia.
  assert (Hc : forall l, 0 <= C l) by (intros; apply cntZ_nonneg).
  assert (H0 : offsZ C 0 = 0) by reflexivity.
  pose proof (offsZ_mono C 0 (Z.to_nat (Znth s lens)) Hc ltac:(lia)).
  assert (Hlt : cntZ (lenF lens) (Z.to_nat s) (Znth s lens) < C (Znth s lens)).
  { pose proof (cntZ_lt (lenF lens) (Z.to_nat s) n ltac:(unfold n; lia)) as Hx.
    rewrite Z2Nat.id in Hx by lia. exact Hx. }
  pose proof (offsZ_succ C (Z.to_nat (Znth s lens)) ltac:(lia)) as Hs1.
  rewrite Z2Nat.id in Hs1 by lia.
  pose proof (offsZ_mono C (S (Z.to_nat (Znth s lens))) 16 Hc ltac:(lia)).
  pose proof (cntZ_nonneg (lenF lens) (Z.to_nat s) (Znth s lens)).
  lia.
Qed.

(** * construct's verdict is the Lean spec's *)

Lemma krZ_ext c1 c2 (L : nat) :
  (forall l, 1 <= l <= Z.of_nat L -> c1 l = c2 l) -> krZ c1 L = krZ c2 L.
Proof.
  induction L as [|L IH]; intros H; [reflexivity|].
  rewrite !krZ_succ, IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Theorem construct_verdict :
  32768 < krZ (countF (countsOf lens)) 15 <-> Bridge.lean_notOversub lens = false.
Proof.
  rewrite Bridge.lean_notOversub_eq by (eapply Forall_impl; [|exact Hlens]; cbn; lia).
  rewrite (krZ_ext _ C) by (intros; apply countF_C; lia).
  unfold C, lenF, n. split; intros H; [apply Z.leb_gt; lia|apply Z.leb_gt in H; lia].
Qed.

(** * construct's tables meet decode's preconditions *)

Lemma countF_nonneg l : 0 <= countF (countsOf lens) l.
Proof.
  destruct (Z_lt_dec l 0).
  - unfold countF, Znth; destruct (Z_lt_dec l 0) as [_|]; [|lia]; apply Z.le_refl.
  - rewrite countF_C by lia; apply cntZ_nonneg.
Qed.

Lemma covering_tile j : 0 <= j < ncodes (countsOf lens) ->
  exists l, 1 <= l < 16 /\
    offsZ (countF (countsOf lens)) (Z.to_nat l) <= j < offsZ (countF (countsOf lens)) (Z.to_nat l) + C l.
Proof.
  intros Hj. rewrite ncodes_def in Hj.
  assert (H16 : (1 <= 16)%nat) by lia.
  destruct (offsZ_tile (countF (countsOf lens)) 16 j countF_nonneg H16 Hj) as (l & Hl & Hjl).
  exists l. rewrite <- countF_C by lia. split; [lia|exact Hjl].
Qed.

Lemma covering_sym j l : 1 <= l < 16 ->
  offsZ (countF (countsOf lens)) (Z.to_nat l) <= j < offsZ (countF (countsOf lens)) (Z.to_nat l) + C l ->
  exists s, 0 <= s < Zlength lens /\ 1 <= Znth s lens /\ pos s = j.
Proof.
  intros Hl Hjl.
  set (o := offsZ (countF (countsOf lens)) (Z.to_nat l)) in *.
  assert (Hc : 0 <= j - o < cntZ (lenF lens) n l) by (unfold C in Hjl; lia).
  destruct (cntZ_exists (lenF lens) l n _ Hc) as (m & Hm & Hlm & Hcm).
  exists (Z.of_nat m). unfold lenF in Hlm.
  split; [unfold n in Hm; lia|]. split; [lia|].
  unfold pos. rewrite Hlm, Nat2Z.id. fold o. lia.
Qed.

(* every position below ncodes holds some symbol *)
Lemma covering j : 0 <= j < ncodes (countsOf lens) ->
  exists s, 0 <= s < Zlength lens /\ 1 <= Znth s lens /\ pos s = j.
Proof.
  intros Hj. destruct (covering_tile j Hj) as (l & Hl & Hjl). exact (covering_sym j l Hl Hjl).
Qed.

Theorem construct_tables_decodable syms :
  Zlength syms = Zlength lens -> table lens syms ->
  Zlength (countsOf lens) = 16 /\
  Forall (fun c => 0 <= c <= 320) (countsOf lens) /\
  ncodes (countsOf lens) <= Zlength syms /\
  (forall j, 0 <= j < ncodes (countsOf lens) ->
     exists v, Znth j syms = Vint (Int.repr v) /\ 0 <= v <= Int.max_signed).
Proof.
  intros Hlen Htab.
  split; [apply Zlength_countsOf|]. split; [apply countsOf_range|].
  split; [rewrite Hlen; apply ncodes_le|].
  intros j Hj.
  destruct (covering j Hj) as (s & Hs & H1 & Hp).
  exists s. split; [|rep_lia].
  rewrite <- Hp. apply Htab; auto.
Qed.

(** * decode's model is the Lean spec *)

Theorem decode_model_lean syms bytes p :
  Zlength syms = Zlength lens -> table lens syms ->
  Forall (fun b => 0 <= b < 256) bytes -> 0 <= p ->
  decodeZ (countF (countsOf lens)) (symF syms (ncodes (countsOf lens))) (bitZ bytes)
          (8 * Zlength bytes) p = Bridge.lean_decode lens bytes p.
Proof.
  intros Hlen Htab Hbytes Hp. symmetry.
  apply Bridge.lean_decode_eq; auto.
  - eapply Forall_impl; [|exact Hlens]; cbn; lia.
  - intros z. unfold symF. destruct (andb _ _); [|lia]. destruct (Znth z syms); lia.
  - intros l Hl. rewrite countF_C by auto. reflexivity.
  - intros s Hs H1.
    pose proof (pos_range s Hs H1) as Hr. unfold pos in Hr.
    unfold symF. fold (lenF lens).
    destruct (andb _ _) eqn:E;
      [|rewrite andb_false_iff, Z.leb_gt, Z.ltb_ge in E; lia].
    rewrite Htab by auto.
    rewrite Int.signed_repr by rep_lia. lia.
Qed.

End Lens.
