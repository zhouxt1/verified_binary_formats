(* puff's construct() meets construct_spec (Spec_puff.v). *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model VPuff.Spec_puff VPuff.ConstructLemmas.
Require VPuff.Main.
Open Scope Z_scope.

Definition zeros_upto (len : Z) : list val :=
  mk16 (fun l => if l <? len then Vint (Int.repr 0) else Vundef).

Definition cnts (lens : list Z) (i : Z) : list val :=
  mk16 (fun l => Vint (Int.repr (cntZ (lenF lens) (Z.to_nat i) l))).

Lemma zeros_upto_0 : zeros_upto 0 = Zrepeat Vundef 16.
Proof. reflexivity. Qed.

Lemma zeros_upto_succ len : 0 <= len < 16 ->
  upd_Znth len (zeros_upto len) (Vint (Int.repr 0)) = zeros_upto (len + 1).
Proof.
  intros H. unfold zeros_upto. rewrite upd_mk16 by lia. apply mk16_ext. intros l Hl.
  destruct (l =? len) eqn:E, (l <? len) eqn:E1, (l <? len + 1) eqn:E2; auto;
    rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.ltb_lt, ?Z.ltb_ge in *; lia.
Qed.

Lemma zeros_upto_16 lens : zeros_upto 16 = cnts lens 0.
Proof.
  unfold zeros_upto, cnts. apply mk16_ext. intros l Hl.
  destruct (l <? 16) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. lia.
Qed.

Lemma cnts_succ lens i : 0 <= i < Zlength lens -> 0 <= Znth i lens < 16 ->
  upd_Znth (Znth i lens) (cnts lens i)
    (Vint (Int.repr (cntZ (lenF lens) (Z.to_nat i) (Znth i lens) + 1))) = cnts lens (i + 1).
Proof.
  intros Hi Hl. unfold cnts. rewrite upd_mk16 by lia. apply mk16_ext. intros l Hl16.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. cbn [cntZ].
  assert (E0 : lenF lens (Z.of_nat (Z.to_nat i)) = Znth i lens) by (unfold lenF; f_equal; lia).
  rewrite E0.
  destruct (Z.eq_dec l (Znth i lens)) as [->|Hne].
  - rewrite !Z.eqb_refl. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) Hne).
    rewrite (proj2 (Z.eqb_neq (Znth i lens) l)) by auto. f_equal; f_equal; lia.
Qed.

Lemma Znth_cnts lens i l : 0 <= l < 16 ->
  Znth l (cnts lens i) = Vint (Int.repr (cntZ (lenF lens) (Z.to_nat i) l)).
Proof. intros. unfold cnts. rewrite Znth_mk16 by lia. reflexivity. Qed.

Lemma Zlength_cnts lens i : Zlength (cnts lens i) = 16.
Proof. apply Zlength_mk16. Qed.

Lemma sext16 x : -32768 <= x <= 32767 -> Int.sign_ext 16 (Int.repr x) = Int.repr x.
Proof.
  intros H. apply sign_ext_inrange. rewrite Int.signed_repr by rep_lia.
  change (two_p (16 - 1)) with 32768. lia.
Qed.

Lemma cnts_countsOf lens : cnts lens (Zlength lens) = map Vint (map Int.repr (countsOf lens)).
Proof. rewrite countsOf_mk16. reflexivity. Qed.

Lemma all_zero lens : Forall (fun x => 0 <= x <= 15) lens ->
  cntZ (lenF lens) (Z.to_nat (Zlength lens)) 0 = Zlength lens ->
  krZ (countF (countsOf lens)) 15 = 0 /\ forall syms, table lens syms.
Proof.
  intros Hl H.
  assert (Hz : forall i, 0 <= i < Zlength lens -> Znth i lens = 0).
  { intros i Hi. apply (cntZ_zero_all (lenF lens) (Z.to_nat (Zlength lens))); [rewrite H|]; lia. }
  split.
  - apply krZ_zero. intros l Hl1.
    destruct (zlt l 16).
    + rewrite countF_countsOf by lia. apply cntZ_none. intros i Hi.
      unfold lenF. rewrite Hz by lia. lia.
    + unfold countF. apply Znth_overflow. unfold countsOf. rewrite !Zlength_map.
      change (Zlength (seq 0 16)) with 16. lia.
  - intros syms s Hs H1. rewrite Hz in H1 by lia. lia.
Qed.

Lemma shl1 x : Int.shl (Int.repr x) (Int.repr 1) = Int.repr (2 * x).
Proof.
  rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia.
  change (two_p 1) with 2. rewrite mul_repr. f_equal. lia.
Qed.

Section Offs.
Variable lens : list Z.
Hypothesis Hlens : Forall (fun x => 0 <= x <= 15) lens.
Let cf := countF (countsOf lens).

Lemma offs_le_n l : (l <= 16)%nat -> 0 <= offsZ cf l <= Zlength lens.
Proof.
  intros Hl. destruct l as [|[|l]]; [cbn; pose proof (Zlength_nonneg lens); lia|cbn; pose proof (Zlength_nonneg lens); lia|].
  pose proof (offsZ_mono cf 1 (S (S l)) (countF_nonneg lens) ltac:(lia)).
  replace (offsZ cf 1) with 0 in H by reflexivity.
  pose proof (offsZ_mono cf (S (S l)) 16 (countF_nonneg lens) ltac:(lia)).
  unfold cf in *. rewrite (offs_cf lens 16) in H0 by lia.
  pose proof (offs16_le (lenF lens) (Z.to_nat (Zlength lens))).
  pose proof (Zlength_nonneg lens). lia.
Qed.

(* offs[] while it is being filled: offs[1..len] *)
Definition offsl (len : Z) : list val :=
  mk16 (fun l => if andb (1 <=? l) (l <=? len) then Vint (Int.repr (offsZ cf (Z.to_nat l))) else Vundef).

(* offs[] while the symbols are placed: offs[l] = offsZ l + (symbols of length l before i) *)
Definition offs6 (i : Z) : list val :=
  mk16 (fun l => if 1 <=? l then Vint (Int.repr (offsZ cf (Z.to_nat l) + cntZ (lenF lens) (Z.to_nat i) l))
                 else Vundef).

Lemma offsl_1 : upd_Znth 1 (default_val (tarray tshort 16)) (Vint (Int.repr 0)) = offsl 1.
Proof. reflexivity. Qed.

Lemma offsl_succ len : 1 <= len < 15 ->
  upd_Znth (len + 1) (offsl len) (Vint (Int.repr (offsZ cf (Z.to_nat len) + cf len))) = offsl (len + 1).
Proof.
  intros H. unfold offsl. rewrite upd_mk16 by lia. apply mk16_ext. intros l Hl.
  destruct (l =? len + 1) eqn:E.
  - apply Z.eqb_eq in E. subst l. rewrite (proj2 (Z.leb_le 1 (len + 1))), (proj2 (Z.leb_le (len + 1) (len + 1))) by lia.
    replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia. rewrite offsZ_succ by lia.
    rewrite Z2Nat.id by lia. reflexivity.
  - apply Z.eqb_neq in E.
    destruct (1 <=? l) eqn:E1, (l <=? len) eqn:E2, (l <=? len + 1) eqn:E3; cbn [andb]; auto;
      rewrite ?Z.leb_le, ?Z.leb_gt in *; lia.
Qed.

Lemma Znth_offsl len l : 1 <= l <= len -> len < 16 -> Znth l (offsl len) = Vint (Int.repr (offsZ cf (Z.to_nat l))).
Proof.
  intros. unfold offsl. rewrite Znth_mk16 by lia.
  rewrite (proj2 (Z.leb_le 1 l)), (proj2 (Z.leb_le l len)) by lia. reflexivity.
Qed.

Lemma offsl_15 : offsl 15 = offs6 0.
Proof.
  unfold offsl, offs6. apply mk16_ext. intros l Hl.
  destruct (1 <=? l) eqn:E1; [|reflexivity].
  rewrite (proj2 (Z.leb_le l 15)) by lia. cbn. f_equal. f_equal. lia.
Qed.

Lemma Znth_offs6 i l : 1 <= l < 16 ->
  Znth l (offs6 i) = Vint (Int.repr (offsZ cf (Z.to_nat l) + cntZ (lenF lens) (Z.to_nat i) l)).
Proof. intros. unfold offs6. rewrite Znth_mk16 by lia. rewrite (proj2 (Z.leb_le 1 l)) by lia. reflexivity. Qed.

Lemma offs6_succ i : 0 <= i < Zlength lens -> 1 <= Znth i lens ->
  upd_Znth (Znth i lens) (offs6 i) (Vint (Int.repr (pos lens i + 1))) = offs6 (i + 1).
Proof.
  intros Hi H1. assert (Hr : 0 <= Znth i lens <= 15) by (apply Forall_Znth; auto).
  unfold offs6. rewrite upd_mk16 by lia. apply mk16_ext. intros l Hl.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. cbn [cntZ].
  assert (E0 : lenF lens (Z.of_nat (Z.to_nat i)) = Znth i lens) by (unfold lenF; f_equal; lia).
  rewrite E0.
  destruct (Z.eq_dec l (Znth i lens)) as [->|Hne].
  - rewrite Z.eqb_refl, (proj2 (Z.leb_le 1 _)) by lia. unfold pos, cf. f_equal. f_equal. lia.
  - rewrite (proj2 (Z.eqb_neq _ _) Hne), (proj2 (Z.eqb_neq (Znth i lens) l)) by auto.
    destruct (1 <=? l); auto. f_equal. f_equal. lia.
Qed.

Lemma offs6_succ0 i : 0 <= i < Zlength lens -> Znth i lens = 0 -> offs6 i = offs6 (i + 1).
Proof.
  intros Hi H0. unfold offs6. apply mk16_ext. intros l Hl.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. cbn [cntZ].
  assert (E0 : lenF lens (Z.of_nat (Z.to_nat i)) = Znth i lens) by (unfold lenF; f_equal; lia).
  rewrite E0, H0. destruct (1 <=? l) eqn:E; auto. apply Z.leb_le in E.
  rewrite (proj2 (Z.eqb_neq 0 l)) by lia. f_equal. f_equal. lia.
Qed.
End Offs.

Lemma krZ_nonneg cf L : (forall l, 0 <= cf l) -> 0 <= krZ cf L.
Proof.
  intros Hc. induction L as [|L IH]; cbn [krZ]; [lia|].
  specialize (Hc (Z.of_nat (S L))). lia.
Qed.

Lemma body_construct : semax_body Vprog Gprog f_construct construct_spec.
Proof.
  start_function.
  (* count[len] = 0 for len = 0..15 *)
  forward_loop (EX len : Z,
     PROP (0 <= len <= 16)
     LOCAL (temp _len (Vint (Int.repr len)); temp _h h; temp _length length;
            temp _n (Vint (Int.repr (Zlength lens))); lvar _offs (tarray tshort 16) v_offs)
     SEP (data_at sh (Tstruct _huffman noattr) (cnt, sym) h;
          data_at sh (tarray tshort 16) (zeros_upto len) cnt;
          data_at_ sh (tarray tshort (Zlength lens)) sym;
          data_at shl (tarray tshort (Zlength lens)) (map Vint (map Int.repr lens)) length;
          data_at_ Tsh (tarray tshort 16) v_offs))%assert
  continue: (EX len : Z,
     PROP (0 <= len <= 15)
     LOCAL (temp _len (Vint (Int.repr len)); temp _h h; temp _length length;
            temp _n (Vint (Int.repr (Zlength lens))); lvar _offs (tarray tshort 16) v_offs)
     SEP (data_at sh (Tstruct _huffman noattr) (cnt, sym) h;
          data_at sh (tarray tshort 16) (zeros_upto (len + 1)) cnt;
          data_at_ sh (tarray tshort (Zlength lens)) sym;
          data_at shl (tarray tshort (Zlength lens)) (map Vint (map Int.repr lens)) length;
          data_at_ Tsh (tarray tshort 16) v_offs))%assert
  break: (PROP ()
     LOCAL (temp _h h; temp _length length;
            temp _n (Vint (Int.repr (Zlength lens))); lvar _offs (tarray tshort 16) v_offs)
     SEP (data_at sh (Tstruct _huffman noattr) (cnt, sym) h;
          data_at sh (tarray tshort 16) (cnts lens 0) cnt;
          data_at_ sh (tarray tshort (Zlength lens)) sym;
          data_at shl (tarray tshort (Zlength lens)) (map Vint (map Int.repr lens)) length;
          data_at_ Tsh (tarray tshort 16) v_offs)).
  { forward. Exists 0. entailer!; rewrite zeros_upto_0; cancel. }
  { Intros len. forward_if.
    - forward. forward. Exists len. entailer!; rewrite zeros_upto_succ by lia; cancel.
    - forward. entailer!; replace len with 16 by lia; rewrite (zeros_upto_16 lens); cancel. }
  { Intros len. forward. Exists (len + 1). entailer!. }
  (* count[length[symbol]]++ *)
  forward_for_simple_bound (Zlength lens) (EX i : Z,
     PROP ()
     LOCAL (temp _h h; temp _length length;
            temp _n (Vint (Int.repr (Zlength lens))); lvar _offs (tarray tshort 16) v_offs)
     SEP (data_at sh (Tstruct _huffman noattr) (cnt, sym) h;
          data_at sh (tarray tshort 16) (cnts lens i) cnt;
          data_at_ sh (tarray tshort (Zlength lens)) sym;
          data_at shl (tarray tshort (Zlength lens)) (map Vint (map Int.repr lens)) length;
          data_at_ Tsh (tarray tshort 16) v_offs))%assert.
  { entailer!. }
  { assert (Hli : 0 <= Znth i lens <= 15) by (apply Forall_Znth; auto).
    forward. forward. try solve [entailer!; lia].
    forward. forward. try solve [entailer!; lia].
    pose proof (cntZ_le (lenF lens) (Z.to_nat i) (Znth i lens)).
    pose proof (cntZ_nonneg (lenF lens) (Z.to_nat i) (Znth i lens)).
    forward.
    { entailer!. rewrite Znth_cnts by lia. simpl. rewrite Int.signed_repr by rep_lia. lia. }
    rewrite Znth_cnts by lia.
    forward.
    entailer!.
    rewrite sext16 by lia. rewrite cnts_succ by lia. cancel. }
  assert (Hcn : forall l, 0 <= l < 16 -> 0 <= cntZ (lenF lens) (Z.to_nat (Zlength lens)) l <= (Zlength lens)).
  { intros l Hl. split; [apply cntZ_nonneg|]. pose proof (cntZ_le (lenF lens) (Z.to_nat (Zlength lens)) l).
    pose proof (Zlength_nonneg lens).  lia. }
  assert (Hcf : forall l, 0 <= l < 16 -> (countF (countsOf lens)) l = cntZ (lenF lens) (Z.to_nat (Zlength lens)) l)
    by (intros; apply countF_countsOf; lia).
  (* all lengths zero *)
  forward. forward.
  { entailer!. pose proof (Hcn 0 ltac:(lia)). rewrite ZtoNat_Zlength in *. rewrite Int.signed_repr by rep_lia. lia. }
  rewrite Znth_cnts by lia.
  specialize (Hcn 0 ltac:(lia)) as Hc0.
  forward_if.
  { forward. Exists 0 (default_val (tarray tshort (Zlength lens))).
    destruct (all_zero lens H0 H1) as [Hk Ht].
    entailer!.
    split; intros _; [left | reflexivity].
    change (Znth 0 (countsOf lens)) with (countF (countsOf lens) 0).
    rewrite countF_countsOf by lia. assumption. }
  (* the Kraft check *)
  forward.
  forward_loop (EX len : Z,
     PROP (1 <= len <= 16; krZ (countF (countsOf lens)) (Z.to_nat (len - 1)) <= 2 ^ (len - 1))
     LOCAL (temp _len (Vint (Int.repr len)); temp _left (Vint (Int.repr (2 ^ (len - 1) - krZ (countF (countsOf lens)) (Z.to_nat (len - 1)))));
            temp _h h; temp _length length;
            temp _n (Vint (Int.repr (Zlength lens))); lvar _offs (tarray tshort 16) v_offs)
     SEP (data_at sh (Tstruct _huffman noattr) (cnt, sym) h;
          data_at sh (tarray tshort 16) (cnts lens (Zlength lens)) cnt;
          data_at_ sh (tarray tshort (Zlength lens)) sym;
          data_at shl (tarray tshort (Zlength lens)) (map Vint (map Int.repr lens)) length;
          data_at_ Tsh (tarray tshort 16) v_offs))%assert
  continue: (EX len : Z,
     PROP (1 <= len <= 15; krZ (countF (countsOf lens)) (Z.to_nat len) <= 2 ^ len)
     LOCAL (temp _len (Vint (Int.repr len)); temp _left (Vint (Int.repr (2 ^ len - krZ (countF (countsOf lens)) (Z.to_nat len))));
            temp _h h; temp _length length;
            temp _n (Vint (Int.repr (Zlength lens))); lvar _offs (tarray tshort 16) v_offs)
     SEP (data_at sh (Tstruct _huffman noattr) (cnt, sym) h;
          data_at sh (tarray tshort 16) (cnts lens (Zlength lens)) cnt;
          data_at_ sh (tarray tshort (Zlength lens)) sym;
          data_at shl (tarray tshort (Zlength lens)) (map Vint (map Int.repr lens)) length;
          data_at_ Tsh (tarray tshort 16) v_offs))%assert
  break: (PROP (krZ (countF (countsOf lens)) 15 <= 32768)
     LOCAL (temp _left (Vint (Int.repr (32768 - krZ (countF (countsOf lens)) 15)));
            temp _h h; temp _length length;
            temp _n (Vint (Int.repr (Zlength lens))); lvar _offs (tarray tshort 16) v_offs)
     SEP (data_at sh (Tstruct _huffman noattr) (cnt, sym) h;
          data_at sh (tarray tshort 16) (cnts lens (Zlength lens)) cnt;
          data_at_ sh (tarray tshort (Zlength lens)) sym;
          data_at shl (tarray tshort (Zlength lens)) (map Vint (map Int.repr lens)) length;
          data_at_ Tsh (tarray tshort 16) v_offs)).
  { forward. Exists 1. entailer!. simpl. lia. }
  { Intros len. forward_if.
    - assert (Hkr : krZ (countF (countsOf lens)) (Z.to_nat len) = 2 * krZ (countF (countsOf lens)) (Z.to_nat (len - 1)) + (countF (countsOf lens)) len).
      { replace (Z.to_nat len) with (S (Z.to_nat (len - 1))) by lia. rewrite krZ_succ.
        f_equal. f_equal. lia. }
      assert (Hcl : 0 <= (countF (countsOf lens)) len <= Zlength lens) by (rewrite Hcf by lia; apply Hcn; lia).
      assert (Hk0 : 0 <= krZ (countF (countsOf lens)) (Z.to_nat (len - 1))).
      { clear - Hcf Hcn. induction (Z.to_nat (len - 1)); [simpl; lia|].
        rewrite krZ_succ. pose proof (countF_nonneg lens (Z.of_nat (S n))). fold (countF (countsOf lens)) in H. lia. }
      assert (Hp : 2 ^ (len - 1) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia).
      forward.
      rewrite shl1.
      forward. forward.
      { entailer!. rewrite Znth_cnts by lia. simpl. rewrite ZtoNat_Zlength in *.
        pose proof (Hcn len ltac:(lia)). rewrite Int.signed_repr by rep_lia. lia. }
      rewrite Znth_cnts by lia.
      rewrite <- Hcf by lia.
      forward.
      forward_if.
      + forward.
        Exists (2 * (2 ^ (len - 1) - krZ (countF (countsOf lens)) (Z.to_nat (len - 1))) - (countF (countsOf lens)) len) (default_val (tarray tshort (Zlength lens))).
        assert (Hover : 32768 < krZ (countF (countsOf lens)) 15).
        { change 32768 with (2 ^ Z.of_nat 15).
          apply (krZ_over (countF (countsOf lens)) (Z.to_nat len) 15 (countF_nonneg lens)); [lia|].
          rewrite Z2Nat.id by lia. rewrite Hkr.
          replace len with (len - 1 + 1) at 1 by lia. rewrite Z.pow_add_r by lia. lia. }
        entailer!; split; intros; lia.
      + forward. Exists len.
        assert (E : 2 ^ len = 2 * 2 ^ (len - 1))
          by (replace len with (len - 1 + 1) at 1 by lia; rewrite Z.pow_add_r by lia; lia).
        entailer!; rewrite Hkr, E; try split; try lia; f_equal; f_equal; lia.
    - forward. assert (len = 16) by lia. subst len. entailer!. }
  { Intros len. forward. Exists (len + 1). entailer!.
    replace (len + 1 - 1) with len by lia. auto. }
  (* offs[] *)
  forward.
  forward_for_simple_bound 15 (EX len : Z,
     PROP (krZ (countF (countsOf lens)) 15 <= 32768)
     LOCAL (temp _left (Vint (Int.repr (32768 - krZ (countF (countsOf lens)) 15)));
            temp _h h; temp _length length;
            temp _n (Vint (Int.repr (Zlength lens))); lvar _offs (tarray tshort 16) v_offs)
     SEP (data_at sh (Tstruct _huffman noattr) (cnt, sym) h;
          data_at sh (tarray tshort 16) (cnts lens (Zlength lens)) cnt;
          data_at_ sh (tarray tshort (Zlength lens)) sym;
          data_at shl (tarray tshort (Zlength lens)) (map Vint (map Int.repr lens)) length;
          data_at Tsh (tarray tshort 16) (offsl lens len) v_offs))%assert.
  { entailer!. }
  { pose proof (offs_le_n lens (Z.to_nat i) ltac:(lia)).
    assert (Hcl : 0 <= (countF (countsOf lens)) i <= Zlength lens) by (rewrite Hcf by lia; apply Hcn; lia).
    assert (Hsum : offsZ (countF (countsOf lens)) (Z.to_nat i) + (countF (countsOf lens)) i <= Zlength lens).
    { pose proof (offs_le_n lens (S (Z.to_nat i)) ltac:(lia)) as X.
      rewrite offsZ_succ in X by lia. rewrite Z2Nat.id in X by lia.
      lia. }
    forward.
    { entailer!. rewrite Znth_offsl by lia. simpl. rewrite Int.signed_repr by rep_lia. lia. }
    rewrite Znth_offsl by lia.
    forward. forward.
    { entailer!. rewrite Znth_cnts by lia. simpl. rewrite ZtoNat_Zlength in *.
      pose proof (Hcn i ltac:(lia)). rewrite Int.signed_repr by rep_lia. lia. }
    rewrite Znth_cnts by lia. rewrite <- Hcf by lia.
    forward.
    entailer!.
    rewrite sext16 by lia.
    rewrite offsl_succ by auto. cancel. }
  rewrite offsl_15.
  (* place the symbols *)
  forward_for_simple_bound (Zlength lens) (EX i : Z, EX syms : list val,
     PROP (krZ (countF (countsOf lens)) 15 <= 32768; Zlength syms = Zlength lens;
           forall s, 0 <= s < i -> 1 <= Znth s lens -> Znth (pos lens s) syms = Vint (Int.repr s))
     LOCAL (temp _left (Vint (Int.repr (32768 - krZ (countF (countsOf lens)) 15)));
            temp _h h; temp _length length;
            temp _n (Vint (Int.repr (Zlength lens))); lvar _offs (tarray tshort 16) v_offs)
     SEP (data_at sh (Tstruct _huffman noattr) (cnt, sym) h;
          data_at sh (tarray tshort 16) (cnts lens (Zlength lens)) cnt;
          data_at sh (tarray tshort (Zlength lens)) syms sym;
          data_at shl (tarray tshort (Zlength lens)) (map Vint (map Int.repr lens)) length;
          data_at Tsh (tarray tshort 16) (offs6 lens i) v_offs))%assert.
  { Exists (default_val (tarray tshort (Zlength lens))). entailer!.
    unfold default_val; simpl. rewrite Zlength_Zrepeat; lia. }
  { assert (Hr : 0 <= Znth i lens <= 15) by (apply Forall_Znth; auto).
    forward. try solve [entailer!; lia].
    forward_if.
    - assert (H1i : 1 <= Znth i lens) by lia.
      destruct (pos_range lens H0 i ltac:(lia) H1i) as [Hp0 _].
      pose proof (pos_lt_n lens H0 i ltac:(lia) H1i) as Hpn.
      forward. try solve [entailer!; lia].
      forward.
      { entailer!. rewrite Znth_offs6 by lia. simpl. fold (pos lens i).
        rewrite Int.signed_repr by rep_lia. lia. }
      rewrite Znth_offs6 by lia. fold (pos lens i).
      forward. try solve [entailer!; lia].
      forward. forward. forward.
      match goal with HH : forall s : Z, 0 <= s < i -> 1 <= Znth s lens -> _ |- _ => rename HH into Hinv end.
      Exists (upd_Znth (pos lens i) syms (Vint (Int.repr i))).
      entailer!.
      + intros s Hs Hs1. destruct (Z.eq_dec s i) as [->|Hne].
        * rewrite upd_Znth_same by lia. reflexivity.
        * assert (Hs0 := proj1 (pos_range lens H0 s ltac:(lia) Hs1)).
          assert (Hsn := pos_lt_n lens H0 s ltac:(lia) Hs1).
          assert (Hne' := pos_inj lens H0 s i ltac:(lia) ltac:(lia) Hs1 H1i).
          rewrite upd_Znth_diff by lia.
          apply Hinv; lia.
      + rewrite sext16 by lia. rewrite offs6_succ by (auto; lia). cancel.
    - forward. match goal with HH : forall s : Z, 0 <= s < i -> 1 <= Znth s lens -> _ |- _ => rename HH into Hinv end. Exists syms. entailer!.
      + intros s Hs Hs1. destruct (Z.eq_dec s i) as [->|Hne]; [lia|]. apply Hinv; lia.
      + rewrite <- offs6_succ0 by (auto; lia). cancel. }
  Intros syms.
  forward.
  assert (Hk0 : 0 <= krZ (countF (countsOf lens)) 15).
  { apply krZ_nonneg. intros l. eapply VPuff.Main.countF_nonneg; eauto. }
  Exists (32768 - krZ (countF (countsOf lens)) 15) syms.
  entailer!.
  split; [rep_lia|].
  change (Znth 0 (countsOf lens)) with (countF (countsOf lens) 0).
  rewrite countF_countsOf by lia.
  intros [E|E]; [contradiction | lia].
Qed.
