(* Arithmetic facts behind the proof of construct (Verif_construct.v). *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model VPuff.Spec_puff.
Open Scope Z_scope.

(** * Arrays of 16 indexed by length *)

Definition idx16 : list Z := map Z.of_nat (seq 0 16).

Definition mk16 {A} (f : Z -> A) : list A := map f idx16.

Lemma Zlength_idx16 : Zlength idx16 = 16.
Proof. reflexivity. Qed.

Lemma Znth_idx16 l : 0 <= l < 16 -> Znth l idx16 = l.
Proof.
  intros H. unfold idx16. rewrite Znth_map by (change (Zlength (seq 0 16)) with 16; lia).
  unfold Znth. destruct (Z_lt_dec l 0); [lia|].
  rewrite seq_nth by lia. lia.
Qed.

Lemma Zlength_mk16 {A} (f : Z -> A) : Zlength (mk16 f) = 16.
Proof. unfold mk16. rewrite Zlength_map. reflexivity. Qed.

Lemma Znth_mk16 {A} {d : Inhabitant A} (f : Z -> A) l : 0 <= l < 16 -> Znth l (mk16 f) = f l.
Proof.
  intros H. unfold mk16. rewrite Znth_map by (rewrite Zlength_idx16; lia).
  rewrite Znth_idx16 by lia. reflexivity.
Qed.

Lemma mk16_ext {A} {d : Inhabitant A} (f g : Z -> A) :
  (forall l, 0 <= l < 16 -> f l = g l) -> mk16 f = mk16 g.
Proof.
  intros H. apply Znth_eq_ext. rewrite !Zlength_mk16; reflexivity.
  intros i Hi. rewrite Zlength_mk16 in Hi. rewrite !Znth_mk16 by lia. apply H; lia.
Qed.

Lemma upd_mk16 {A} {d : Inhabitant A} (f : Z -> A) k v : 0 <= k < 16 ->
  upd_Znth k (mk16 f) v = mk16 (fun l => if l =? k then v else f l).
Proof.
  intros Hk. apply Znth_eq_ext.
  rewrite Zlength_upd_Znth, !Zlength_mk16; reflexivity.
  intros i Hi. rewrite Zlength_upd_Znth, Zlength_mk16 in Hi.
  rewrite Znth_mk16 by lia.
  destruct (Z.eq_dec i k).
  - subst. rewrite upd_Znth_same by (rewrite Zlength_mk16; lia). rewrite Z.eqb_refl. reflexivity.
  - rewrite upd_Znth_diff by (rewrite ?Zlength_mk16; lia). rewrite Znth_mk16 by lia.
    rewrite (proj2 (Z.eqb_neq i k) n). reflexivity.
Qed.

Lemma map_mk16 {A B} (g : A -> B) (f : Z -> A) : map g (mk16 f) = mk16 (fun l => g (f l)).
Proof. unfold mk16. rewrite map_map. reflexivity. Qed.

Lemma countsOf_mk16 lens :
  map Vint (map Int.repr (countsOf lens)) =
    mk16 (fun l => Vint (Int.repr (cntZ (lenF lens) (Z.to_nat (Zlength lens)) l))).
Proof. unfold countsOf. rewrite !map_map. reflexivity. Qed.

Lemma countF_countsOf lens l : 0 <= l < 16 ->
  countF (countsOf lens) l = cntZ (lenF lens) (Z.to_nat (Zlength lens)) l.
Proof. intros. unfold countF, countsOf. fold idx16. fold (mk16 (fun l => cntZ (lenF lens) (Z.to_nat (Zlength lens)) l)).
  apply Znth_mk16; lia. Qed.

Lemma countF_nonneg lens l : 0 <= countF (countsOf lens) l.
Proof.
  destruct (zlt l 0). { unfold countF. rewrite Znth_underflow by lia. apply Z.le_refl. }
  destruct (zlt l 16). { rewrite countF_countsOf by lia. apply cntZ_nonneg. }
  unfold countF. rewrite Znth_overflow. apply Z.le_refl. unfold countsOf. rewrite !Zlength_map. change (Zlength (seq 0 16)) with 16. lia.
Qed.

(** * Counting *)

Lemma cntZ_mono len l m n : (m <= n)%nat -> cntZ len m l <= cntZ len n l.
Proof.
  induction 1; [lia|]. cbn. destruct (_ =? _); lia.
Qed.

Lemma cntZ_lt len i n : (i < n)%nat -> cntZ len i (len (Z.of_nat i)) < cntZ len n (len (Z.of_nat i)).
Proof.
  intros H. pose proof (cntZ_mono len (len (Z.of_nat i)) (S i) n ltac:(lia)).
  cbn in H0. rewrite Z.eqb_refl in H0. lia.
Qed.

Lemma cntZ_zero_all len n : cntZ len n 0 = Z.of_nat n -> forall i, 0 <= i < Z.of_nat n -> len i = 0.
Proof.
  induction n; intros H i Hi; [lia|].
  cbn in H. pose proof (cntZ_le len n 0).
  destruct (len (Z.of_nat n) =? 0) eqn:E; [|lia].
  apply Z.eqb_eq in E.
  destruct (Z.eq_dec i (Z.of_nat n)); [subst; auto|].
  apply IHn; lia.
Qed.

Lemma cntZ_none len n l : (forall i, 0 <= i < Z.of_nat n -> len i <> l) -> cntZ len n l = 0.
Proof.
  induction n; intros H; [reflexivity|]. cbn.
  rewrite IHn by (intros; apply H; lia).
  destruct (len (Z.of_nat n) =? l) eqn:E; [|lia].
  apply Z.eqb_eq in E. exfalso. apply (H (Z.of_nat n)); auto; lia.
Qed.

(** * The table's offsets *)

Lemma offsZ_mono cf a b : (forall l, 0 <= cf l) -> (1 <= a <= b)%nat -> offsZ cf a <= offsZ cf b.
Proof.
  intros Hc [Ha Hab]. induction Hab; [lia|].
  rewrite offsZ_succ by lia. specialize (Hc (Z.of_nat m)). lia.
Qed.

Lemma offsZ_ext cf cg l : (forall j, 0 <= j < Z.of_nat l -> cf j = cg j) -> offsZ cf l = offsZ cg l.
Proof.
  induction l as [|[|l] IH]; intros H; [reflexivity|reflexivity|].
  change (offsZ cf (S (S l))) with (offsZ cf (S l) + cf (Z.of_nat (S l))).
  change (offsZ cg (S (S l))) with (offsZ cg (S l) + cg (Z.of_nat (S l))).
  rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

(* adding a symbol adds one to the offsets above its length *)
Lemma offs_cnt_succ len n k : (1 <= k)%nat ->
  offsZ (fun l => cntZ len (S n) l) k =
    offsZ (fun l => cntZ len n l) k + (if andb (1 <=? len (Z.of_nat n)) (len (Z.of_nat n) <? Z.of_nat k) then 1 else 0).
Proof.
  intros Hk. induction Hk.
  - assert (E : andb (1 <=? len (Z.of_nat n)) (len (Z.of_nat n) <? Z.of_nat 1) = false).
    { destruct (1 <=? len (Z.of_nat n)) eqn:E1, (len (Z.of_nat n) <? Z.of_nat 1) eqn:E2; auto.
      rewrite Z.leb_le, Z.ltb_lt in *. simpl in *. lia. }
    rewrite E. reflexivity.
  - rewrite !offsZ_succ by lia. rewrite IHHk. cbn [cntZ].
    destruct (len (Z.of_nat n) =? Z.of_nat m) eqn:E;
    destruct (1 <=? len (Z.of_nat n)) eqn:E1;
    destruct (len (Z.of_nat n) <? Z.of_nat m) eqn:E2;
    destruct (len (Z.of_nat n) <? Z.of_nat (S m)) eqn:E3; cbn [andb];
      rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.leb_le, ?Z.leb_gt, ?Z.ltb_lt, ?Z.ltb_ge in *; lia.
Qed.

(* the coded symbols fit in the table *)
Lemma offs16_le len n : offsZ (fun l => cntZ len n l) 16 <= Z.of_nat n.
Proof.
  induction n.
  - assert (forall k, offsZ (fun l => cntZ len 0 l) k = 0) by (induction k as [|[|k] IH]; auto; cbn in *; lia).
    rewrite H. lia.
  - rewrite offs_cnt_succ by lia. destruct (andb _ _); lia.
Qed.

Section Pos.
Variable lens : list Z.
Hypothesis Hlens : Forall (fun x => 0 <= x <= 15) lens.
Let n := Zlength lens.
Let cf := countF (countsOf lens).
Definition pos (s : Z) : Z :=
  offsZ (countF (countsOf lens)) (Z.to_nat (Znth s lens)) +
    cntZ (lenF lens) (Z.to_nat s) (Znth s lens).

Lemma Znth_lens_range s : 0 <= s < Zlength lens -> 0 <= Znth s lens <= 15.
Proof. intros. apply Forall_Znth; auto. Qed.

Lemma offs_cf l : (l <= 16)%nat ->
  offsZ cf l = offsZ (fun j => cntZ (lenF lens) (Z.to_nat n) j) l.
Proof. intros. apply offsZ_ext. intros. unfold cf. rewrite countF_countsOf by lia. reflexivity. Qed.

Lemma pos_range s : 0 <= s < n -> 1 <= Znth s lens ->
  0 <= pos s /\ pos s + 1 <= offsZ cf (S (Z.to_nat (Znth s lens))) /\
  offsZ cf (Z.to_nat (Znth s lens)) <= pos s.
Proof.
  intros Hs H1. pose proof (Znth_lens_range s Hs) as Hr.
  set (l := Znth s lens) in *.
  assert (Hlt : cntZ (lenF lens) (Z.to_nat s) l < cntZ (lenF lens) (Z.to_nat n) l).
  { replace l with (lenF lens (Z.of_nat (Z.to_nat s))) by (unfold lenF, l; f_equal; lia).
    apply cntZ_lt; lia. }
  unfold pos; fold l; fold cf.
  rewrite offsZ_succ by lia.
  assert (cf (Z.of_nat (Z.to_nat l)) = cntZ (lenF lens) (Z.to_nat n) l)
    by (unfold cf; rewrite countF_countsOf by lia; f_equal; unfold l; lia).
  pose proof (cntZ_nonneg (lenF lens) (Z.to_nat s) l).
  assert (0 <= offsZ cf (Z.to_nat l)) by (destruct (Z.to_nat l) as [|[|]] eqn:?; cbn; try lia;
    pose proof (offsZ_mono cf 1 (S (S n0)) (countF_nonneg lens) ltac:(lia)); cbn in H2; lia).
  lia.
Qed.

Lemma pos_lt_n s : 0 <= s < n -> 1 <= Znth s lens -> pos s < n.
Proof.
  intros Hs H1. destruct (pos_range s Hs H1) as [_ [H2 _]].
  pose proof (Znth_lens_range s Hs).
  pose proof (offsZ_mono cf (S (Z.to_nat (Znth s lens))) 16 (countF_nonneg lens) ltac:(lia)).
  rewrite (offs_cf 16) in H0 by lia.
  pose proof (offs16_le (lenF lens) (Z.to_nat n)).
  pose proof (Zlength_nonneg lens). unfold n in *.
  lia.
Qed.

Lemma pos_inj s i : 0 <= s < i -> i < n -> 1 <= Znth s lens -> 1 <= Znth i lens -> pos s <> pos i.
Proof.
  intros Hs Hi H1 H2.
  pose proof (Znth_lens_range s ltac:(lia)); pose proof (Znth_lens_range i ltac:(lia)).
  destruct (pos_range s ltac:(lia) H1) as [_ [Hs1 Hs2]].
  destruct (pos_range i ltac:(lia) H2) as [_ [Hi1 Hi2]].
  destruct (Z.lt_total (Znth s lens) (Znth i lens)) as [Hl|[Hl|Hl]].
  - pose proof (offsZ_mono cf (S (Z.to_nat (Znth s lens))) (Z.to_nat (Znth i lens)) (countF_nonneg lens) ltac:(lia)).
    lia.
  - unfold pos. rewrite Hl.
    assert (cntZ (lenF lens) (Z.to_nat s) (Znth i lens) < cntZ (lenF lens) (Z.to_nat i) (Znth i lens)).
    { rewrite <- Hl. replace (Znth s lens) with (lenF lens (Z.of_nat (Z.to_nat s))) by (unfold lenF; f_equal; lia).
      apply cntZ_lt; lia. }
    lia.
  - pose proof (offsZ_mono cf (S (Z.to_nat (Znth i lens))) (Z.to_nat (Znth s lens)) (countF_nonneg lens) ltac:(lia)).
    lia.
Qed.
End Pos.

(** * Kraft *)

Lemma krZ_zero cf L : (forall l, 1 <= l -> cf l = 0) -> krZ cf L = 0.
Proof.
  intros H. induction L; [reflexivity|]. rewrite krZ_succ, IHL.
  assert (H1 : 1 <= Z.of_nat (S L)) by (rewrite Nat2Z.inj_succ; lia).
  rewrite (H _ H1). lia.
Qed.

Lemma krZ_over cf L M : (forall l, 0 <= cf l) -> (L <= M)%nat ->
  2 ^ Z.of_nat L < krZ cf L -> 2 ^ Z.of_nat M < krZ cf M.
Proof.
  intros Hc HLM. induction HLM; auto. intros H. specialize (IHHLM H).
  rewrite krZ_succ. pose proof (Hc (Z.of_nat (S m))).
  rewrite Nat2Z.inj_succ in *. rewrite Z.pow_succ_r by lia. lia.
Qed.
