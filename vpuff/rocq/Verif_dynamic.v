(* puff's dynamic() meets dynamic_spec (Spec_puff.v). *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model VPuff.Spec_puff VPuff.DynLemmas.
Require VPuff.Inflate VPuff.InflateFacts.
Import VPuff.Inflate.
Open Scope Z_scope.

Ltac rd_eof :=
  unfold state_rep; forward;
  match goal with |- context [data_at ?sh (Tstruct _state noattr) (?op, (Vint (Int.repr ?ol),
      (Vint (Int.repr ?oc), (?ip, (Vint (Int.repr ?il), (Vint (Int.repr ?ic), (Vint (Int.repr ?bb),
      (Vint (Int.repr ?bc), Vint (Int.repr ?e))))))))) ?s] =>
    fold (state_rep sh s op ol oc ip il ic bb bc e) end.

(** * The code length code lengths: positions written so far *)

Definition Dyn_cldef (i j : Z) : Prop := exists k, 0 <= k < i /\ Znth k orderTab = j.

Lemma Dyn_cldef_succ i j : 0 <= i -> (Dyn_cldef (i + 1) j <-> Dyn_cldef i j \/ Znth i orderTab = j).
Proof.
  intros Hi. unfold Dyn_cldef. split.
  - intros (k & Hk & E). destruct (Z.eq_dec k i) as [->|Hne]; [right; auto|left; exists k; split; [lia|auto]].
  - intros [(k & Hk & E)|E]; [exists k; split; [lia|auto]|exists i; split; [lia|auto]].
Qed.

Lemma Dyn_order_nodup : NoDup orderTab.
Proof. unfold orderTab. repeat constructor; cbn; intros H; repeat destruct H as [H|H]; try discriminate; auto. Qed.

Lemma Dyn_order_inj k1 k2 : 0 <= k1 < 19 -> 0 <= k2 < 19 -> Znth k1 orderTab = Znth k2 orderTab -> k1 = k2.
Proof. intros. eapply NoDup_Znth_inj; eauto using Dyn_order_nodup. Qed.

Lemma Dyn_cldef_all j : 0 <= j < 19 -> Dyn_cldef 19 j.
Proof. intros Hj. destruct (Dyn_order_cover j Hj) as (k & Hk & E). exists k. auto. Qed.

Lemma Dyn_cldef_new i : 0 <= i < 19 -> ~ Dyn_cldef i (Znth i orderTab).
Proof. intros Hi (k & Hk & E). apply Dyn_order_inj in E; lia. Qed.

Lemma Dyn_cl_step i acc (larr : list val) v : 0 <= i < 19 -> Zlength acc = 19 -> Zlength larr = 316 ->
  (forall j, 0 <= j < 19 -> ~ Dyn_cldef i j -> Znth j acc = 0) ->
  (forall j, 0 <= j < 19 -> Dyn_cldef i j -> Znth j larr = Vint (Int.repr (Znth j acc))) ->
  (forall j, 0 <= j < 19 -> ~ Dyn_cldef (i + 1) j -> Znth j (upd_Znth (Znth i orderTab) acc v) = 0) /\
  (forall j, 0 <= j < 19 -> Dyn_cldef (i + 1) j ->
     Znth j (upd_Znth (Znth i orderTab) larr (Vint (Int.repr v))) =
     Vint (Int.repr (Znth j (upd_Znth (Znth i orderTab) acc v)))).
Proof.
  intros Hi La Ll H0 H1. pose proof (Dyn_order_range i Hi) as Ho. split.
  - intros j Hj Hn. rewrite Dyn_cldef_succ in Hn by lia.
    rewrite upd_Znth_diff by (try lia; intros ->; tauto). apply H0; tauto.
  - intros j Hj Hd. rewrite Dyn_cldef_succ in Hd by lia.
    destruct (Z.eq_dec j (Znth i orderTab)) as [->|Hne].
    + rewrite !upd_Znth_same by lia. reflexivity.
    + rewrite !upd_Znth_diff by lia. apply H1; [lia|]. destruct Hd; [auto|congruence].
Qed.

Lemma Dyn_readCL_step bytes p h i acc : 0 <= i < h -> i < 20 ->
  readCLgo bytes p h (Z.to_nat (20 - i)) i acc =
  match getbitsZ bytes (p + 3 * i) 3 with
  | None => None
  | Some v => readCLgo bytes p h (Z.to_nat (20 - (i + 1))) (i + 1) (upd_Znth (Znth i orderTab) acc v)
  end.
Proof.
  intros. replace (Z.to_nat (20 - i)) with (S (Z.to_nat (20 - (i + 1)))) by lia.
  cbn [readCLgo]. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma Dyn_readCL_end bytes p h i acc : h <= i < 20 ->
  readCLgo bytes p h (Z.to_nat (20 - i)) i acc = Some (acc, p + 3 * h).
Proof.
  intros. replace (Z.to_nat (20 - i)) with (S (Z.to_nat (20 - (i + 1)))) by lia.
  cbn [readCLgo]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Lemma sext16 x : -32768 <= x <= 32767 -> Int.sign_ext 16 (Int.repr x) = Int.repr x.
Proof.
  intros H. apply sign_ext_inrange. rewrite Int.signed_repr by rep_lia.
  change (two_p (16 - 1)) with 32768. lia.
Qed.

Lemma Dyn_order_Znth i : 0 <= i < 19 ->
  Znth i (map Vint (map Int.repr orderTab)) = Vint (Int.repr (Znth i orderTab)).
Proof. intros. rewrite !Znth_map by (unfold orderTab; cbn; lia). reflexivity. Qed.

Lemma Dyn_merge sh n k (l1 l2 : list val) p : 0 <= k <= n ->
  data_at sh (tarray tshort k) l1 p *
  data_at sh (tarray tshort (n - k)) l2 (field_address0 (tarray tshort n) (SUB k) p)
  |-- data_at_ sh (tarray tshort n) p.
Proof.
  intros. rewrite (split2_data_at__Tarray_app k n) by lia.
  sep_apply (data_at_data_at_ sh (tarray tshort k) l1 p).
  sep_apply (data_at_data_at_ sh (tarray tshort (n - k)) l2). cancel.
Qed.

Lemma Dyn_merge_ sh n k (l1 : list val) p : 0 <= k <= n ->
  data_at sh (tarray tshort k) l1 p *
  data_at_ sh (tarray tshort (n - k)) (field_address0 (tarray tshort n) (SUB k) p)
  |-- data_at_ sh (tarray tshort n) p.
Proof.
  intros. rewrite (split2_data_at__Tarray_app k n) by lia.
  sep_apply (data_at_data_at_ sh (tarray tshort k) l1 p). cancel.
Qed.

(** * The code lengths: one step of readLensZ *)

Definition nbOf (s : Z) : Z := if s =? 16 then 2 else if s =? 17 then 3 else 7.
Definition baseOf (s : Z) : Z := if s =? 18 then 11 else 3.
Definition lastOf (s : Z) (acc : list Z) : option Z := if s =? 16 then lastZ acc else Some 0.

Lemma Dyn_readLens_done cl bytes f p total acc : total <= Zlength acc ->
  readLensZ cl bytes (S f) p total acc = Some (acc, p).
Proof. intros. cbn [readLensZ]. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. Qed.

Lemma Dyn_readLens_dec cl bytes f p total acc : Zlength acc < total ->
  readLensZ cl bytes (S f) p total acc =
  match lean_decode cl bytes p with
  | None => None
  | Some (s, p1) =>
      if s <? 16 then readLensZ cl bytes f p1 total (acc ++ [s])
      else match getbitsZ bytes p1 (nbOf s) with
           | None => None
           | Some e =>
               match lastOf s acc with
               | None => None
               | Some v =>
                   if Zlength acc + (baseOf s + e) <=? total
                   then readLensZ cl bytes f (p1 + nbOf s) total (acc ++ Zrepeat v (baseOf s + e))
                   else None
               end
           end
  end.
Proof. intros. cbn [readLensZ]. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. Qed.

Lemma Dyn_lastZ acc : acc <> [] -> lastZ acc = Some (Znth (Zlength acc - 1) acc).
Proof.
  intros Hne. unfold lastZ. destruct (rev acc) as [|x t] eqn:E.
  - apply (f_equal (@rev Z)) in E. rewrite rev_involutive in E. subst. contradiction.
  - apply (f_equal (@rev Z)) in E. rewrite rev_involutive in E. subst acc. cbn [rev].
    f_equal. list_solve.
Qed.

Lemma Dyn_pos_ok bytes ic bb bc : buf_ok bytes ic bb bc -> 0 <= 8 * ic - bc <= nbits bytes.
Proof.
  unfold buf_ok, nbits. intros (H1 & H2 & H3 & _).
  destruct (Z.eq_dec ic 0) as [->|]; [specialize (H3 eq_refl); lia|lia].
Qed.

Lemma Dyn_room_mono wr bytes out p q : p <= q -> room wr bytes out p -> room wr bytes out q.
Proof. unfold room. intros Hpq [H|H]; [left; auto|right]. unfold nbits in *. lia. Qed.

Lemma Dyn_counts_len lens : Zlength (countsOf lens) = 16.
Proof. unfold countsOf. rewrite !Zlength_map. reflexivity. Qed.

Lemma Dyn_c01 lens : Dyn_lens_ok lens ->
  0 <= Znth 0 (countsOf lens) /\ 0 <= Znth 1 (countsOf lens) /\
  Znth 0 (countsOf lens) + Znth 1 (countsOf lens) <= Zlength lens.
Proof.
  intros H. rewrite !Dyn_Znth_countsOf by lia. pose proof (Dyn_sum_cntOf lens H) as S.
  assert (N : forall l, 0 <= cntOf lens l) by (intros; unfold cntOf; apply Dyn_cnt_nonneg).
  pose proof (N 0); pose proof (N 1); pose proof (N 2); pose proof (N 3); pose proof (N 4);
  pose proof (N 5); pose proof (N 6); pose proof (N 7); pose proof (N 8); pose proof (N 9);
  pose proof (N 10); pose proof (N 11); pose proof (N 12); pose proof (N 13); pose proof (N 14);
  pose proof (N 15). lia.
Qed.

Lemma Dyn_mk_htable sh h cnt sym lens syms :
  Zlength lens <= 320 -> Forall (fun x => 0 <= x <= 15) lens -> Zlength syms = Zlength lens ->
  table lens syms ->
  data_at sh (Tstruct _huffman noattr) (cnt, sym) h *
  data_at sh (tarray tshort 16) (map Vint (map Int.repr (countsOf lens))) cnt *
  data_at sh (tarray tshort (Zlength lens)) syms sym
  |-- htable sh h cnt sym lens.
Proof. intros. unfold htable. Exists syms. rewrite H1. entailer!. Qed.

Lemma Dyn_fail_ok wr outlen bytes p out r out' ic bb bc e :
  r <> 0 -> (forall lit dist q, ~ Dyn_hdr_ok bytes p lit dist q) ->
  block_ok wr outlen
    (match dynHeaderZ bytes p with
     | Some (lit, dist, q, true) => symsF lit dist bytes q out
     | _ => None
     end) r out' bytes ic bb bc e.
Proof.
  intros Hr H. change (block_ok wr outlen (Dyn_res bytes p out) r out' bytes ic bb bc e).
  rewrite Dyn_res_none by auto. exact Hr.
Qed.

Lemma Dyn_bits_ok bytes p n r : 0 <= n -> p + n <= nbits bytes -> r = lsbZ bytes p (Z.to_nat n) ->
  getbitsZ bytes p n = Some r /\ 0 <= r < 2 ^ n.
Proof.
  intros Hn H ->. split; [apply Dyn_getbits_some; auto|].
  pose proof (Dyn_lsb_range bytes p (Z.to_nat n)). rewrite Z2Nat.id in H0 by lia. lia.
Qed.

Ltac dyn_fail r o ic bb bc e :=
  Exists r o ic bb bc e; unfold all_tables, shortarr at 1; entailer!; apply Dyn_fail_ok; auto; try lia.

Ltac skip_then :=
  forward_if; [exfalso; match goal with H : _ <> _ |- _ => apply H; reflexivity end|].

Ltac no_eof :=
  forward_if; [match goal with H : Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end|].

Ltac hdr_inv :=
  let lit := fresh "lit" in let dist := fresh "dist" in let q := fresh "q" in
  let Hh := fresh "Hh" in
  intros lit dist q Hh; unfold Dyn_hdr_ok in Hh; decompose [ex and] Hh; clear Hh;
  repeat match goal with
         | E1 : ?f = None, E2 : ?f = Some _ |- _ => rewrite E1 in E2; discriminate
         | E1 : ?f = Some ?x, E2 : ?f = Some ?y |- _ =>
             rewrite E1 in E2; injection E2; clear E2; intros; subst
         | E : getbitsZ ?b _ _ = Some _, B : nbits ?b < _ |- _ =>
             rewrite Dyn_getbits_none in E by (unfold nbits in *; lia); discriminate
         end.

Ltac bits_post B Hr Hp Hb :=
  match goal with H : (if ?c then _ else _) |- _ =>
    destruct c eqn:B; [destruct H as (Hr & Hp & Hb & ->) | destruct H as [-> ->]] end.

Ltac fwd_if_temp id v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp id v :: Q) (SEPx R))) end.

Ltac name_cl :=
  repeat match goal with
  | H : Int.repr 0 = Int.zero |- _ => clear H
  | H : Int.zero = Int.zero |- _ => clear H
  end;
  match goal with H : 8 * ?ic - ?bc = 8 * _ - _ + 14 + 3 * _ |- _ => rename H into Hpos end;
  try match goal with H : readCLgo _ _ _ _ _ _ = _ |- _ => rename H into Hrd end;
  match goal with H : Zlength ?a = 19 |- _ => rename H into La end;
  match goal with H : Zlength ?a = 316 |- _ => rename H into Ll end;
  match goal with H : Forall _ _ |- _ => rename H into Hf end;
  match goal with H : forall j, _ -> ~ Dyn_cldef _ _ -> _ |- _ => rename H into Hz end;
  match goal with H : forall j, _ -> Dyn_cldef _ _ -> _ |- _ => rename H into Hd end.

Ltac neq_true := match goal with H' : ?x <> ?y, H : ?x = ?y |- _ => exact (H' H) end.

Ltac rep_range :=
  match goal with H : (if ?c then _ else _) |- _ =>
    destruct c;
    [destruct H as [-> _];
     match goal with |- context [lsbZ ?b ?p ?n] => pose proof (Dyn_lsb_range b p n) end;
     rewrite Z2Nat.id in * by lia; lia
    | destruct H as [_ ->]; lia] end.

Lemma body_dynamic : semax_body Vprog Gprog f_dynamic dynamic_spec.
Proof.
  start_function.
  assert (Hin : 0 <= Zlength bytes <= 1073741824) by (unfold sizes_ok in *; tauto).
  unfold all_tables. Intros. unfold shortarr at 1.
  assert (Lo : Zlength orderTab = 19) by reflexivity.
  forward. forward. forward. forward.
  (* the header's three counts *)
  forward_call (sh, shi, s, outp, outlen, Zlength out, inp, bytes, incnt, bitbuf, bitcnt, 5).
  Intros vret. destruct vret as [[[[r1 ic1] bb1] bc1] e1]. cbn [fst snd] in *.
  bits_post B1 Hr1 Hp1 Hb1.
  2: { forward. rd_eof. forward_if; [|discriminate]. forward. dyn_fail 2 out ic1 bb1 bc1 1.
       apply Z.leb_gt in B1. hdr_inv. }
  apply Z.leb_le in B1. destruct (Dyn_bits_ok _ _ 5 _ ltac:(lia) B1 Hr1) as [G1 R1]. clear Hr1.
  forward. rd_eof. no_eof.
  forward_call (sh, shi, s, outp, outlen, Zlength out, inp, bytes, ic1, bb1, bc1, 5).
  Intros vret. destruct vret as [[[[r2 ic2] bb2] bc2] e2]. cbn [fst snd] in *.
  bits_post B2 Hr2 Hp2 Hb2.
  2: { forward. rd_eof. forward_if; [|discriminate]. forward. dyn_fail 2 out ic2 bb2 bc2 1.
       apply Z.leb_gt in B2. hdr_inv. }
  apply Z.leb_le in B2. destruct (Dyn_bits_ok _ _ 5 _ ltac:(lia) B2 Hr2) as [G2 R2]. clear Hr2.
  forward. rd_eof. no_eof.
  forward_call (sh, shi, s, outp, outlen, Zlength out, inp, bytes, ic2, bb2, bc2, 4).
  Intros vret. destruct vret as [[[[r3 ic3] bb3] bc3] e3]. cbn [fst snd] in *.
  bits_post B3 Hr3 Hp3 Hb3.
  2: { forward. rd_eof. forward_if; [|discriminate]. forward. dyn_fail 2 out ic3 bb3 bc3 1.
       apply Z.leb_gt in B3. hdr_inv. }
  apply Z.leb_le in B3. destruct (Dyn_bits_ok _ _ 4 _ ltac:(lia) B3 Hr3) as [G3 R3]. clear Hr3.
  forward. rd_eof. no_eof.
  rewrite Hp1 in G2. rewrite Hp2, Hp1 in G3.
  change (2 ^ 5) with 32 in *. change (2 ^ 4) with 16 in *.
  fwd_if_temp _t'4 (Val.of_bool (orb (r1 + 257 >? 286) (r2 + 1 >? 30))).
  { forward. entailer!. destruct (r1 + 257 >? 286) eqn:?; [reflexivity|]. lia. }
  { forward. entailer!. destruct (r1 + 257 >? 286) eqn:?; [lia|].
    destruct (r2 + 1 >? 30) eqn:?; cbn; [rewrite Z.gtb_lt in *|rewrite Z.gtb_ltb, Z.ltb_ge in *].
    - destruct (zlt 30 (r2 + 1)); [reflexivity|lia].
    - destruct (zlt 30 (r2 + 1)); [lia|reflexivity]. }
  replace (8 * incnt - bitcnt + 5 + 5) with (8 * incnt - bitcnt + 10) in G3 by lia.
  destruct (orb (r1 + 257 >? 286) (r2 + 1 >? 30)) eqn:Bc.
  { forward_if; [|discriminate]. forward. dyn_fail (-3) out ic3 bb3 bc3 0.
    apply orb_true_iff in Bc. rewrite !Z.gtb_ltb, !Z.ltb_lt in Bc.
    hdr_inv; lia. }
  skip_then.
  apply orb_false_iff in Bc. destruct Bc as [Bc1 Bc2]. rewrite Z.gtb_ltb, Z.ltb_ge in Bc1, Bc2.
  (* the code length code lengths *)
  forward_loop
    (EX i : Z, EX acc : list Z, EX larr : list val, EX ic : Z, EX bb : Z, EX bc : Z,
     PROP (0 <= i <= r3 + 4; buf_ok bytes ic bb bc; (8 * ic - bc = 8 * incnt - bitcnt + 14 + 3 * i)%Z;
           readCLgo bytes (8 * incnt - bitcnt + 14) (r3 + 4) (Z.to_nat (20 - i)) i acc =
             readCLZ bytes (8 * incnt - bitcnt + 14) (r3 + 4);
           Zlength acc = 19; Forall (fun x => 0 <= x < 8) acc;
           forall j, 0 <= j < 19 -> ~ Dyn_cldef i j -> Znth j acc = 0;
           Zlength larr = 316;
           forall j, 0 <= j < 19 -> Dyn_cldef i j -> Znth j larr = Vint (Int.repr (Znth j acc)))
     LOCAL (temp _index (Vint (Int.repr i)); temp _nlen (Vint (Int.repr (r1 + 257)));
            temp _ndist (Vint (Int.repr (r2 + 1))); temp _ncode (Vint (Int.repr (r3 + 4)));
            lvar _lengths (tarray tshort 316) v_lengths; lvar _lencnt (tarray tshort 16) v_lencnt;
            lvar _lensym (tarray tshort 286) v_lensym; lvar _distcnt (tarray tshort 16) v_distcnt;
            lvar _distsym (tarray tshort 30) v_distsym; lvar _lencode (Tstruct _huffman noattr) v_lencode;
            lvar _distcode (Tstruct _huffman noattr) v_distcode; gvars gv; temp _s s)
     SEP (state_rep sh s outp outlen (Zlength out) inp (Zlength bytes) ic bb bc 0;
          data_at Tsh (tarray tshort 316) larr v_lengths;
          data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
          data_at Tsh (Tstruct _huffman noattr) (v_distcnt, v_distsym) v_distcode;
          data_at Tsh (Tstruct _huffman noattr) (v_lencnt, v_lensym) v_lencode;
          data_at_ Tsh (tarray tshort 30) v_distsym; data_at_ Tsh (tarray tshort 16) v_distcnt;
          data_at_ Tsh (tarray tshort 286) v_lensym; data_at_ Tsh (tarray tshort 16) v_lencnt;
          outbuf wr sho outp outlen out; codes_tables gv;
          data_at Ers (tarray tshort 19) (map Vint (map Int.repr orderTab)) (gv _order)))%assert
  break:
    (EX acc : list Z, EX larr : list val, EX ic : Z, EX bb : Z, EX bc : Z,
     PROP (buf_ok bytes ic bb bc; (8 * ic - bc = 8 * incnt - bitcnt + 14 + 3 * (r3 + 4))%Z;
           readCLZ bytes (8 * incnt - bitcnt + 14) (r3 + 4) = Some (acc, (8 * ic - bc)%Z);
           Zlength acc = 19; Forall (fun x => 0 <= x < 8) acc;
           forall j, 0 <= j < 19 -> ~ Dyn_cldef (r3 + 4) j -> Znth j acc = 0;
           Zlength larr = 316;
           forall j, 0 <= j < 19 -> Dyn_cldef (r3 + 4) j -> Znth j larr = Vint (Int.repr (Znth j acc)))
     LOCAL (temp _index (Vint (Int.repr (r3 + 4))); temp _nlen (Vint (Int.repr (r1 + 257)));
            temp _ndist (Vint (Int.repr (r2 + 1))); temp _ncode (Vint (Int.repr (r3 + 4)));
            lvar _lengths (tarray tshort 316) v_lengths; lvar _lencnt (tarray tshort 16) v_lencnt;
            lvar _lensym (tarray tshort 286) v_lensym; lvar _distcnt (tarray tshort 16) v_distcnt;
            lvar _distsym (tarray tshort 30) v_distsym; lvar _lencode (Tstruct _huffman noattr) v_lencode;
            lvar _distcode (Tstruct _huffman noattr) v_distcode; gvars gv; temp _s s)
     SEP (state_rep sh s outp outlen (Zlength out) inp (Zlength bytes) ic bb bc 0;
          data_at Tsh (tarray tshort 316) larr v_lengths;
          data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
          data_at Tsh (Tstruct _huffman noattr) (v_distcnt, v_distsym) v_distcode;
          data_at Tsh (Tstruct _huffman noattr) (v_lencnt, v_lensym) v_lencode;
          data_at_ Tsh (tarray tshort 30) v_distsym; data_at_ Tsh (tarray tshort 16) v_distcnt;
          data_at_ Tsh (tarray tshort 286) v_lensym; data_at_ Tsh (tarray tshort 16) v_lencnt;
          outbuf wr sho outp outlen out; codes_tables gv;
          data_at Ers (tarray tshort 19) (map Vint (map Int.repr orderTab)) (gv _order)))%assert.
  { forward. Exists 0 (Zrepeat 0 19) (default_val (tarray tshort 316)) ic3 bb3 bc3. entailer!.
    split3; [apply Forall_forall; intros x Hx; unfold Zrepeat in Hx; apply repeat_spec in Hx; lia
            |intros; autorewrite with sublist; auto|intros j Hj (k & Hk & _); lia]. }
  { Intros i acc larr ic bb bc. name_cl. forward_if.
    - forward_call (sh, shi, s, outp, outlen, Zlength out, inp, bytes, ic, bb, bc, 3).
      Intros vret. destruct vret as [[[[r ic'] bb'] bc'] e]. cbn [fst snd] in *.
      assert (Ho := Dyn_order_range i ltac:(lia)).
      bits_post Bb Hr Hp Hb.
      + apply Z.leb_le in Bb. destruct (Dyn_bits_ok _ _ 3 _ ltac:(lia) Bb Hr) as [Gb Rb]. clear Hr.
        forward. { entailer!. lia. } forward.
        rd_eof. no_eof. forward.
        Exists (i + 1) (upd_Znth (Znth i orderTab) acc r)
          (upd_Znth (Znth i orderTab) larr (Vint (Int.repr r))) ic' bb' bc'.
        rewrite Hpos in Gb.
        destruct (Dyn_cl_step i acc larr r ltac:(lia) La Ll Hz Hd) as [S1 S2].
        rewrite Dyn_readCL_step in Hrd by lia. rewrite Gb in Hrd.
        entailer!.
        repeat split; auto; try lia; try list_solve; try (apply Forall_upd_Znth; auto; lia);
          try (rewrite <- Hrd; f_equal; lia).
      + forward. { entailer!. lia. } forward.
        rd_eof. forward_if; [|discriminate]. forward. dyn_fail 2 out ic' bb' bc' 1.
        apply Z.leb_gt in Bb.
        assert (RN : readCLZ bytes (8 * incnt - bitcnt + 14) (r3 + 4) = None).
        { rewrite <- Hrd, Dyn_readCL_step by lia. rewrite <- Hpos, Dyn_getbits_none by (unfold nbits in *; lia).
          reflexivity. }
        hdr_inv.
    - assert (i = r3 + 4) by lia. subst i.
      forward. Exists acc larr ic bb bc.
      rewrite Dyn_readCL_end in Hrd by lia. rewrite <- Hpos in Hrd. entailer!. }
  (* the missing ones are zero *)
  Intros cl larr ic bb bc. name_cl.
  match goal with H : readCLZ _ _ _ = Some _ |- _ => rename H into Hcl end.
  forward_loop
    (EX i : Z, EX larr : list val,
     PROP (r3 + 4 <= i <= 19; Zlength larr = 316;
           forall j, 0 <= j < 19 -> ~ Dyn_cldef i j -> Znth j cl = 0;
           forall j, 0 <= j < 19 -> Dyn_cldef i j -> Znth j larr = Vint (Int.repr (Znth j cl)))
     LOCAL (temp _index (Vint (Int.repr i)); temp _nlen (Vint (Int.repr (r1 + 257)));
            temp _ndist (Vint (Int.repr (r2 + 1))); temp _ncode (Vint (Int.repr (r3 + 4)));
            lvar _lengths (tarray tshort 316) v_lengths; lvar _lencnt (tarray tshort 16) v_lencnt;
            lvar _lensym (tarray tshort 286) v_lensym; lvar _distcnt (tarray tshort 16) v_distcnt;
            lvar _distsym (tarray tshort 30) v_distsym; lvar _lencode (Tstruct _huffman noattr) v_lencode;
            lvar _distcode (Tstruct _huffman noattr) v_distcode; gvars gv; temp _s s)
     SEP (state_rep sh s outp outlen (Zlength out) inp (Zlength bytes) ic bb bc 0;
          data_at Tsh (tarray tshort 316) larr v_lengths;
          data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
          data_at Tsh (Tstruct _huffman noattr) (v_distcnt, v_distsym) v_distcode;
          data_at Tsh (Tstruct _huffman noattr) (v_lencnt, v_lensym) v_lencode;
          data_at_ Tsh (tarray tshort 30) v_distsym; data_at_ Tsh (tarray tshort 16) v_distcnt;
          data_at_ Tsh (tarray tshort 286) v_lensym; data_at_ Tsh (tarray tshort 16) v_lencnt;
          outbuf wr sho outp outlen out; codes_tables gv;
          data_at Ers (tarray tshort 19) (map Vint (map Int.repr orderTab)) (gv _order)))%assert
  break:
    (EX larr : list val,
     PROP (Zlength larr = 316; sublist 0 19 larr = map Vint (map Int.repr cl))
     LOCAL (temp _nlen (Vint (Int.repr (r1 + 257)));
            temp _ndist (Vint (Int.repr (r2 + 1))); temp _ncode (Vint (Int.repr (r3 + 4)));
            lvar _lengths (tarray tshort 316) v_lengths; lvar _lencnt (tarray tshort 16) v_lencnt;
            lvar _lensym (tarray tshort 286) v_lensym; lvar _distcnt (tarray tshort 16) v_distcnt;
            lvar _distsym (tarray tshort 30) v_distsym; lvar _lencode (Tstruct _huffman noattr) v_lencode;
            lvar _distcode (Tstruct _huffman noattr) v_distcode; gvars gv; temp _s s)
     SEP (state_rep sh s outp outlen (Zlength out) inp (Zlength bytes) ic bb bc 0;
          data_at Tsh (tarray tshort 316) larr v_lengths;
          data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
          data_at Tsh (Tstruct _huffman noattr) (v_distcnt, v_distsym) v_distcode;
          data_at Tsh (Tstruct _huffman noattr) (v_lencnt, v_lensym) v_lencode;
          data_at_ Tsh (tarray tshort 30) v_distsym; data_at_ Tsh (tarray tshort 16) v_distcnt;
          data_at_ Tsh (tarray tshort 286) v_lensym; data_at_ Tsh (tarray tshort 16) v_lencnt;
          outbuf wr sho outp outlen out; codes_tables gv;
          data_at Ers (tarray tshort 19) (map Vint (map Int.repr orderTab)) (gv _order)))%assert.
  { Exists (r3 + 4) larr. entailer!. }
  { Intros i larr'. forward_if.
    - assert (Ho := Dyn_order_range i ltac:(lia)).
      forward. { entailer!. lia. } forward. forward.
      match goal with H : forall j, _ -> ~ Dyn_cldef _ _ -> _ |- _ => rename H into Hz2 end.
      match goal with H : forall j, _ -> Dyn_cldef _ _ -> _ |- _ => rename H into Hd2 end.
      assert (Hz0 : Znth (Znth i orderTab) cl = 0) by (apply Hz2; [lia|apply Dyn_cldef_new; lia]).
      destruct (Dyn_cl_step i cl larr' 0 ltac:(lia) La ltac:(assumption) Hz2 Hd2) as [S1 S2].
      rewrite upd_Znth_triv in S1, S2 by (try lia; auto).
      Exists (i + 1) (upd_Znth (Znth i orderTab) larr' (Vint (Int.repr 0))).
      entailer!; repeat split; auto; try list_solve.
    - forward. Exists larr'. entailer!.
      assert (i = 19) by lia. subst i.
      apply Znth_eq_ext; [list_solve|]. intros j Hj. autorewrite with sublist in *.
      rewrite Znth_sublist by lia. rewrite Z.add_0_r.
      match goal with H : forall j, _ -> Dyn_cldef _ _ -> _ |- _ => rewrite H by (try apply Dyn_cldef_all; lia) end.
      rewrite !Znth_map by list_solve. reflexivity. }
  Intros larr2.
  match goal with H : sublist 0 19 larr2 = _ |- _ => rename H into Hs2 end.
  match goal with H : Zlength larr2 = 316 |- _ => rename H into Hl2 end.
  (* the code length code *)
  assert (Elen : larr2 = map Vint (map Int.repr cl) ++ sublist 19 316 larr2).
  { rewrite <- Hs2, <- sublist_split, sublist_same by lia. reflexivity. }
  rewrite Elen.
  rewrite (split2_data_at_Tarray_app (Zlength cl) 316 Tsh tshort) by list_solve.
  rewrite (split2_data_at__Tarray_app (Zlength cl) 286 Tsh tshort v_lensym) by lia.
  Intros.
  forward_call (Tsh, Tsh, v_lencode, v_lencnt, v_lensym, v_lengths, cl).
  { entailer!. rewrite La. reflexivity. }
  { rewrite Forall_forall in Hf |- *. intros x Hx. specialize (Hf x Hx). lia. }
  Intros vret. destruct vret as [rc symsc]. cbn [fst snd] in *.
  match goal with H : rc < 0 <-> _ |- _ => rename H into Hc1 end.
  match goal with H : 0 <= rc -> rc = 0 <-> _ |- _ => rename H into Hc2 end.
  match goal with H : 0 <= rc -> table _ _ |- _ => rename H into Htc end.
  assert (Hco : Dyn_cons_ok cl rc) by (split; auto).
  forward_if.
  { sep_apply (Dyn_merge Tsh 316 (Zlength cl) (map Vint (map Int.repr cl)) (sublist 19 316 larr2) v_lengths ltac:(lia)).
    sep_apply (Dyn_merge_ Tsh 286 (Zlength cl) symsc v_lensym ltac:(lia)).
    forward. dyn_fail (-4) out ic bb bc 0.
    assert (Hb : andb (notOversubZ cl) (zlibOkZ cl true) <> true)
      by (rewrite <- (Dyn_cl_check cl rc Hco); auto).
    hdr_inv; try neq_true. }
  subst rc. specialize (Htc ltac:(lia)).
  assert_PROP (Zlength symsc = Zlength cl) as Hsy by entailer!.
  (* the literal/length and distance code lengths *)
  forward.
  forward_while
    (EX acc : list Z, EX rest : list val, EX ica : Z, EX bba : Z, EX bca : Z,
     PROP (Zlength acc <= r1 + 257 + (r2 + 1); Forall (fun x => 0 <= x <= 15) acc;
           Zlength rest = 316 - Zlength acc; buf_ok bytes ica bba bca;
           8 * ic - bc <= 8 * ica - bca;
           readLensZ cl bytes (Z.to_nat (r1 + 257 + (r2 + 1) - Zlength acc) + 1) (8 * ica - bca)
             (r1 + 257 + (r2 + 1)) acc =
           readLensZ cl bytes (Z.to_nat (r1 + 257 + (r2 + 1)) + 1) (8 * ic - bc) (r1 + 257 + (r2 + 1)) [])
     LOCAL (temp _index (Vint (Int.repr (Zlength acc))); temp _nlen (Vint (Int.repr (r1 + 257)));
            temp _ndist (Vint (Int.repr (r2 + 1))); temp _ncode (Vint (Int.repr (r3 + 4)));
            lvar _lengths (tarray tshort 316) v_lengths; lvar _lencnt (tarray tshort 16) v_lencnt;
            lvar _lensym (tarray tshort 286) v_lensym; lvar _distcnt (tarray tshort 16) v_distcnt;
            lvar _distsym (tarray tshort 30) v_distsym; lvar _lencode (Tstruct _huffman noattr) v_lencode;
            lvar _distcode (Tstruct _huffman noattr) v_distcode; gvars gv; temp _s s)
     SEP (state_rep sh s outp outlen (Zlength out) inp (Zlength bytes) ica bba bca 0;
          data_at Tsh (tarray tshort 316) (map Vint (map Int.repr acc) ++ rest) v_lengths;
          data_at Tsh (Tstruct _huffman noattr) (v_lencnt, v_lensym) v_lencode;
          data_at Tsh (tarray tshort 16) (map Vint (map Int.repr (countsOf cl))) v_lencnt;
          data_at Tsh (tarray tshort (Zlength symsc)) symsc v_lensym;
          data_at_ Tsh (tarray tshort (286 - Zlength symsc))
            (field_address0 (tarray tshort 286) (SUB Zlength symsc) v_lensym);
          data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
          data_at Tsh (Tstruct _huffman noattr) (v_distcnt, v_distsym) v_distcode;
          data_at_ Tsh (tarray tshort 30) v_distsym; data_at_ Tsh (tarray tshort 16) v_distcnt;
          outbuf wr sho outp outlen out; codes_tables gv;
          data_at Ers (tarray tshort 19) (map Vint (map Int.repr orderTab)) (gv _order)))%assert.
  { Exists (@nil Z) (map Vint (map Int.repr cl) ++ sublist 19 316 larr2) ic bb bc.
    change (map Vint (map Int.repr (@nil Z)) ++ (map Vint (map Int.repr cl) ++ sublist 19 316 larr2))
      with (map Vint (map Int.repr cl) ++ sublist 19 316 larr2).
    rewrite (split2_data_at_Tarray_app (Zlength cl) 316 Tsh tshort (map Vint (map Int.repr cl))
      (sublist 19 316 larr2)) by list_solve.
    rewrite Hsy. entailer!. split; [rewrite Zlength_nil; lia|list_solve]. }
  { entailer!. }
  { match goal with H : readLensZ _ _ _ _ _ acc = _ |- _ => rename H into Hrl end.
    match goal with H : buf_ok bytes ica bba bca |- _ => rename H into Hba end.
    match goal with H : 8 * ic - bc <= 8 * ica - bca |- _ => rename H into Hmon end.
    match goal with H : Forall _ acc |- _ => rename H into Hfa end.
    match goal with H : Zlength rest = _ |- _ => rename H into Hra end.
    pose proof (Dyn_pos_ok _ _ _ _ Hba) as Hpa.
    assert (Hfc : Forall (fun x => 0 <= x <= 15) cl).
    { rewrite Forall_forall in Hf |- *. intros x Hx. specialize (Hf x Hx). lia. }
    forward_call (sh, shi, Tsh, s, outp, outlen, Zlength out, inp, bytes, ica, bba, bca,
                  v_lencode, v_lencnt, v_lensym, cl, symsc).
    Intros vret. destruct vret as [[[[rd icd] bbd] bcd] ed]. cbn [fst snd] in *.
    rewrite Nat.add_1_r, Dyn_readLens_dec in Hrl by lia.
    destruct (lean_decode cl bytes (8 * ica - bca)) as [[v p1]|] eqn:Ed.
    2: { (* no symbol *)
      forward_if; [|exfalso; lia]. forward.
      sep_apply (Dyn_merge_ Tsh 286 (Zlength symsc) symsc v_lensym ltac:(lia)).
      dyn_fail rd out icd bbd bcd ed. symmetry in Hrl. hdr_inv. }
    match goal with H : rd = v /\ _ |- _ => destruct H as (-> & Hpd & Hbd & ->) end.
    destruct (VPuff.InflateFacts.lean_decode_bounds cl bytes (8 * ica - bca) v p1 ltac:(lia) Ed) as [Hq1 Hv].
    rewrite La in Hv.
    forward_if; [exfalso; lia|].
    forward_if.
    - (* a length *)
      rewrite (proj2 (Z.ltb_lt _ _)) in Hrl by lia.
      forward. forward.
      assert (0 <= Zlength acc < 316) by (pose proof (Zlength_nonneg acc); lia).
      forward.
      Exists (acc ++ [v], sublist 1 (Zlength rest) rest, icd, bbd, bcd). cbn [fst snd].
      assert (Ea : upd_Znth (Zlength acc) (map Vint (map Int.repr acc) ++ rest) (Vint (Int.repr v)) =
                   map Vint (map Int.repr (acc ++ [v])) ++ sublist 1 (Zlength rest) rest) by list_solve.
      rewrite Ea; entailer!; split; [list_solve|];
        split; [apply Forall_app; split; auto; constructor; [lia|constructor]|];
        split; [list_solve|]; split; [|f_equal; f_equal; list_solve];
        rewrite <- Hrl; f_equal; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
    - (* a repeat *)
      rewrite (proj2 (Z.ltb_ge _ _)) in Hrl by lia.
      forward.
      forward_if
        (EX rep : Z, EX ic4 : Z, EX bb4 : Z, EX bc4 : Z, EX e4 : Z, EX lv : Z,
         PROP ((if p1 + nbOf v <=? nbits bytes
                then rep = lsbZ bytes p1 (Z.to_nat (nbOf v)) /\ (8 * ic4 - bc4 = p1 + nbOf v)%Z /\
                     buf_ok bytes ic4 bb4 bc4 /\ e4 = 0
                else e4 = 1 /\ rep = 0);
               lastOf v acc = Some lv; 0 <= lv <= 15)
         LOCAL (temp _symbol (Vint (Int.repr (baseOf v + rep))); temp _len (Vint (Int.repr lv));
                temp _index (Vint (Int.repr (Zlength acc))); temp _nlen (Vint (Int.repr (r1 + 257)));
              temp _ndist (Vint (Int.repr (r2 + 1))); temp _ncode (Vint (Int.repr (r3 + 4)));
                lvar _lengths (tarray tshort 316) v_lengths; lvar _lencnt (tarray tshort 16) v_lencnt;
              lvar _lensym (tarray tshort 286) v_lensym; lvar _distcnt (tarray tshort 16) v_distcnt;
              lvar _distsym (tarray tshort 30) v_distsym; lvar _lencode (Tstruct _huffman noattr) v_lencode;
              lvar _distcode (Tstruct _huffman noattr) v_distcode; gvars gv; temp _s s)
         SEP (state_rep sh s outp outlen (Zlength out) inp (Zlength bytes) ic4 bb4 bc4 e4;
              data_at Tsh (tarray tshort 316) (map Vint (map Int.repr acc) ++ rest) v_lengths;
              data_at Tsh (Tstruct _huffman noattr) (v_lencnt, v_lensym) v_lencode;
            data_at Tsh (tarray tshort 16) (map Vint (map Int.repr (countsOf cl))) v_lencnt;
            data_at Tsh (tarray tshort (Zlength symsc)) symsc v_lensym;
            data_at_ Tsh (tarray tshort (286 - Zlength symsc))
              (field_address0 (tarray tshort 286) (SUB Zlength symsc) v_lensym);
            data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
            data_at Tsh (Tstruct _huffman noattr) (v_distcnt, v_distsym) v_distcode;
            data_at_ Tsh (tarray tshort 30) v_distsym; data_at_ Tsh (tarray tshort 16) v_distcnt;
            outbuf wr sho outp outlen out; codes_tables gv;
            data_at Ers (tarray tshort 19) (map Vint (map Int.repr orderTab)) (gv _order)))%assert.
      + (* 16: repeat the last length *)
        assert (v = 16) by lia. subst v.
        forward_if.
        * (* there is no last length *)
          forward; sep_apply (Dyn_merge_ Tsh 286 (Zlength symsc) symsc v_lensym ltac:(lia));
          dyn_fail (-5) out icd bbd bcd 0;
          assert (acc = []) by (apply Zlength_nil_inv; lia); subst acc;
          assert (RN : readLensZ cl bytes (Z.to_nat (r1 + 257 + (r2 + 1)) + 1) (8 * ic - bc)
                         (r1 + 257 + (r2 + 1)) [] = None)
            by (rewrite <- Hrl; destruct (getbitsZ _ _ (nbOf 16)); reflexivity);
          hdr_inv.
        * assert (Hne : acc <> []) by (intros ->; rewrite Zlength_nil in *; contradiction).
          assert (El : Znth (Zlength acc - 1) (map Vint (map Int.repr acc) ++ rest) =
                       Vint (Int.repr (Znth (Zlength acc - 1) acc)))
            by (pose proof (Zlength_nonneg acc); destruct acc; [contradiction|];
                rewrite app_Znth1 by list_solve; rewrite !Znth_map by list_solve; reflexivity).
          assert (Hlv : 0 <= Znth (Zlength acc - 1) acc <= 15)
            by (rewrite Forall_Znth in Hfa; apply Hfa; destruct acc; [contradiction|list_solve]).
          forward.
          { entailer!. }
          { entailer!.
            match goal with |- is_int _ _ ?x =>
              replace x with (Vint (Int.repr (Znth (Zlength acc - 1) acc))) by (rewrite <- El; reflexivity) end;
            simpl; rewrite Int.signed_repr by rep_lia; rep_lia. }
          match goal with |- context [temp _len ?x] =>
            replace x with (Vint (Int.repr (Znth (Zlength acc - 1) acc))) by (rewrite <- El; reflexivity) end.
          forward_call (sh, shi, s, outp, outlen, Zlength out, inp, bytes, icd, bbd, bcd, 2).
          Intros vret. destruct vret as [[[[rep ic4] bb4] bc4] e4]. cbn [fst snd] in *.
          assert (Rr : 0 <= rep < 2 ^ 2) by rep_range.
          forward.
          Exists rep ic4 bb4 bc4 e4 (Znth (Zlength acc - 1) acc).
          change (nbOf 16) with 2. change (baseOf 16) with 3. rewrite Hpd in *.
          entailer!.
          unfold lastOf. cbn [Z.eqb Pos.eqb]. apply Dyn_lastZ; auto.
      + forward_if.
        * (* 17 *)
          assert (v = 17) by lia. subst v.
          forward_call (sh, shi, s, outp, outlen, Zlength out, inp, bytes, icd, bbd, bcd, 3).
          Intros vret. destruct vret as [[[[rep ic4] bb4] bc4] e4]. cbn [fst snd] in *.
          assert (Rr : 0 <= rep < 2 ^ 3) by rep_range.
          forward.
          Exists rep ic4 bb4 bc4 e4 0.
          change (nbOf 17) with 3. change (baseOf 17) with 3. change (lastOf 17 acc) with (Some 0).
          rewrite Hpd in *. entailer!.
        * (* 18 *)
          assert (v = 18) by lia. subst v.
          forward_call (sh, shi, s, outp, outlen, Zlength out, inp, bytes, icd, bbd, bcd, 7).
          Intros vret. destruct vret as [[[[rep ic4] bb4] bc4] e4]. cbn [fst snd] in *.
          assert (Rr : 0 <= rep < 2 ^ 7) by rep_range.
          forward.
          Exists rep ic4 bb4 bc4 e4 0.
          change (nbOf 18) with 7. change (baseOf 18) with 11. change (lastOf 18 acc) with (Some 0).
          rewrite Hpd in *. entailer!.
      + Intros rep ic4 bb4 bc4 e4 lv.
        match goal with H : lastOf v acc = Some lv |- _ => rename H into Hlast end.
          assert (Hnb : 0 <= nbOf v) by (unfold nbOf; repeat destruct (_ =? _); lia).
          assert (Hbase : 3 <= baseOf v <= 11) by (unfold baseOf; destruct (_ =? _); lia).
          rd_eof.
          bits_post Bn Hrr Hpr Hbr.
          2: { forward_if; [|discriminate]. forward.
               sep_apply (Dyn_merge_ Tsh 286 (Zlength symsc) symsc v_lensym ltac:(lia)).
               dyn_fail 2 out ic4 bb4 bc4 1.
               apply Z.leb_gt in Bn. rewrite Dyn_getbits_none in Hrl by (unfold nbits in *; lia).
               symmetry in Hrl. hdr_inv. }
          apply Z.leb_le in Bn.
          destruct (Dyn_bits_ok _ _ (nbOf v) _ Hnb Bn Hrr) as [Gr Rr]. clear Hrr.
          rewrite Gr, Hlast in Hrl.
          no_eof.
          forward_if.
          -- assert (Rr' : 0 <= rep < 128) by (unfold nbOf in Rr; destruct (v =? 16), (v =? 17); simpl in Rr; lia).
             apply prop_right. rewrite Int.signed_repr by rep_lia. rep_lia.
          -- (* too many lengths *)
             assert (Rr' : 0 <= rep < 128) by (unfold nbOf in Rr; destruct (v =? 16), (v =? 17); simpl in Rr; lia).
             rewrite Int.signed_repr in * by rep_lia.
             forward.
             sep_apply (Dyn_merge_ Tsh 286 (Zlength symsc) symsc v_lensym ltac:(lia)).
             dyn_fail (-6) out ic4 bb4 bc4 0.
             rewrite (proj2 (Z.leb_gt _ _)) in Hrl by lia. symmetry in Hrl. hdr_inv.
          -- assert (Rr' : 0 <= rep < 128) by (unfold nbOf in Rr; destruct (v =? 16), (v =? 17); simpl in Rr; lia).
             rewrite Int.signed_repr in * by rep_lia.
             rewrite (proj2 (Z.leb_le _ _)) in Hrl by lia.
             abbreviate_semax.
             forward_loop
               (EX k : Z,
                PROP (0 <= k <= baseOf v + rep)
                LOCAL (temp _symbol (Vint (Int.repr (baseOf v + rep - k))); temp _len (Vint (Int.repr lv));
                       temp _index (Vint (Int.repr (Zlength acc + k))); temp _nlen (Vint (Int.repr (r1 + 257)));
                        temp _ndist (Vint (Int.repr (r2 + 1))); temp _ncode (Vint (Int.repr (r3 + 4)));
                        lvar _lengths (tarray tshort 316) v_lengths; lvar _lencnt (tarray tshort 16) v_lencnt;
                        lvar _lensym (tarray tshort 286) v_lensym; lvar _distcnt (tarray tshort 16) v_distcnt;
                        lvar _distsym (tarray tshort 30) v_distsym; lvar _lencode (Tstruct _huffman noattr) v_lencode;
                        lvar _distcode (Tstruct _huffman noattr) v_distcode; gvars gv; temp _s s)
                SEP (state_rep sh s outp outlen (Zlength out) inp (Zlength bytes) ic4 bb4 bc4 0;
                     data_at Tsh (tarray tshort 316)
                       (map Vint (map Int.repr (acc ++ Zrepeat lv k)) ++ sublist k (Zlength rest) rest) v_lengths;
                      data_at Tsh (Tstruct _huffman noattr) (v_lencnt, v_lensym) v_lencode;
                      data_at Tsh (tarray tshort 16) (map Vint (map Int.repr (countsOf cl))) v_lencnt;
                      data_at Tsh (tarray tshort (Zlength symsc)) symsc v_lensym;
                      data_at_ Tsh (tarray tshort (286 - Zlength symsc))
                        (field_address0 (tarray tshort 286) (SUB Zlength symsc) v_lensym);
                      data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
                      data_at Tsh (Tstruct _huffman noattr) (v_distcnt, v_distsym) v_distcode;
                      data_at_ Tsh (tarray tshort 30) v_distsym; data_at_ Tsh (tarray tshort 16) v_distcnt;
                      outbuf wr sho outp outlen out; codes_tables gv;
                      data_at Ers (tarray tshort 19) (map Vint (map Int.repr orderTab)) (gv _order)))%assert.
             { Exists 0. change (Zrepeat lv 0) with (@nil Z). rewrite app_nil_r, sublist_same by lia.
               entailer!. }
             Intros k. forward. forward. forward_if.
             ++ assert (0 <= Zlength acc + k < 316) by (pose proof (Zlength_nonneg acc); lia).
                forward. forward. forward.
                Exists (k + 1).
                assert (Ek : upd_Znth (Zlength acc + k)
                               (map Vint (map Int.repr (acc ++ Zrepeat lv k)) ++ sublist k (Zlength rest) rest)
                               (Vint (Int.repr lv)) =
                             map Vint (map Int.repr (acc ++ Zrepeat lv (k + 1))) ++
                               sublist (k + 1) (Zlength rest) rest) by list_solve.
                rewrite Ek. entailer!.
                split; f_equal; f_equal; lia.
             ++ forward.
                match goal with H : Int.repr (baseOf v + rep - k) = Int.zero |- _ =>
                  apply (f_equal Int.signed) in H; rewrite Int.signed_repr in H by rep_lia;
                  change (Int.signed Int.zero) with 0 in H end.
                assert (k = baseOf v + rep) by lia. subst k.
                Exists (acc ++ Zrepeat lv (baseOf v + rep), sublist (baseOf v + rep) (Zlength rest) rest,
                        ic4, bb4, bc4).
                cbn [fst snd]. entailer!.
                split; [rewrite Zlength_app, Zlength_Zrepeat by lia; lia|].
                split; [apply Forall_app; split; auto; apply Forall_forall; intros x Hx;
                        unfold Zrepeat in Hx; apply repeat_spec in Hx; lia|].
                split; [rewrite Zlength_app, Zlength_Zrepeat by lia; rewrite Zlength_sublist by lia; lia|].
                split; [|f_equal; f_equal; rewrite Zlength_app, Zlength_Zrepeat by lia; lia].
                match type of Hrl with readLensZ _ _ _ ?q _ _ = _ =>
                  replace (8 * ic4 - bc4) with q by lia end.
                rewrite <- Hrl. apply Dyn_readLens_fuel; rewrite Zlength_app, Zlength_Zrepeat by lia; lia. }
  (* all nlen + ndist lengths are read *)
  match goal with H : readLensZ _ _ _ _ _ acc = _ |- _ => rename H into Hrl end.
  match goal with H : buf_ok bytes ica bba bca |- _ => rename H into Hba end.
  match goal with H : 8 * ic - bc <= 8 * ica - bca |- _ => rename H into Hmon end.
  match goal with H : Forall _ acc |- _ => rename H into Hfa end.
  match goal with H : Zlength rest = _ |- _ => rename H into Hra end.
  assert (Lacc : Zlength acc = r1 + 257 + (r2 + 1)) by lia.
  rewrite Lacc, Z.sub_diag in Hrl. change (Z.to_nat 0 + 1)%nat with 1%nat in Hrl.
  rewrite Dyn_readLens_done in Hrl by lia. symmetry in Hrl.
  assert (Hsp : exists lit dist, acc = lit ++ dist /\ Zlength lit = r1 + 257 /\ Zlength dist = r2 + 1).
  { exists (sublist 0 (r1 + 257) acc), (sublist (r1 + 257) (Zlength acc) acc).
    split; [rewrite <- sublist_split, sublist_same by lia; reflexivity|split; list_solve]. }
  destruct Hsp as (lit & dist & -> & Llit & Ldist).
  assert (Sl : sublist 0 (r1 + 257) (lit ++ dist) = lit) by list_solve.
  assert (Sd : sublist (r1 + 257) (r1 + 257 + (r2 + 1)) (lit ++ dist) = dist) by list_solve.
  assert (Hflit : Forall (fun x => 0 <= x <= 15) lit) by (apply Forall_app in Hfa; tauto).
  assert (Hfdist : Forall (fun x => 0 <= x <= 15) dist) by (apply Forall_app in Hfa; tauto).
  (* the end-of-block code must have a length *)
  assert (E256 : Znth 256 (map Vint (map Int.repr (lit ++ dist)) ++ rest) = Vint (Int.repr (Znth 256 lit))).
  { rewrite app_Znth1 by list_solve. rewrite !Znth_map by list_solve. rewrite app_Znth1 by lia. reflexivity. }
  assert (R256 : 0 <= Znth 256 lit <= 15) by (rewrite Forall_Znth in Hflit; apply Hflit; lia).
  forward.
  { entailer!.
    match goal with |- is_int _ _ ?x =>
      replace x with (Vint (Int.repr (Znth 256 lit))) by (rewrite <- E256; reflexivity) end;
    simpl; rewrite Int.signed_repr by rep_lia; rep_lia. }
  match goal with |- context [temp _t'27 ?x] =>
    replace x with (Vint (Int.repr (Znth 256 lit))) by (rewrite <- E256; reflexivity) end.
  forward_if.
  { assert (Z0 : Znth 256 (sublist 0 (r1 + 257) (lit ++ dist)) = 0) by (rewrite Sl; auto);
    forward; sep_apply (Dyn_merge_ Tsh 286 (Zlength symsc) symsc v_lensym ltac:(lia));
    dyn_fail (-9) out ica bba bca 0; hdr_inv; neq_true. }
  rewrite map_app, map_app, <- app_assoc;
  rewrite (split2_data_at_Tarray_app (Zlength lit) 316 Tsh tshort (map Vint (map Int.repr lit))) by list_solve;
  sep_apply (Dyn_merge_ Tsh 286 (Zlength symsc) symsc v_lensym ltac:(lia));
  rewrite (split2_data_at__Tarray_app (Zlength lit) 286 Tsh tshort v_lensym) by lia;
  sep_apply (data_at_data_at_ Tsh (tarray tshort 16) (map Vint (map Int.repr (countsOf cl))) v_lencnt);
  Intros.
  forward_call (Tsh, Tsh, v_lencode, v_lencnt, v_lensym, v_lengths, lit).
  { entailer!. rewrite Llit. reflexivity. }
  Intros vret. destruct vret as [rl symsl]. cbn [fst snd] in *.
  match goal with H : rl < 0 <-> _ |- _ => rename H into Hl1 end.
  match goal with H : 0 <= rl -> table _ _ |- _ => rename H into Htl end.
  assert (Hlo : Dyn_lens_ok lit) by exact Hflit.
  assert (Hcol : Dyn_cons_ok lit rl) by (split; auto).
  pose proof (Dyn_c01 lit Hlo) as C01.
  pose proof (Dyn_counts_len lit) as CL.
  fwd_if_temp _t'15 (Val.of_bool (if rl =? 0 then false else if rl <? 0 then true
                                  else negb (r1 + 257 =? Znth 0 (countsOf lit) + Znth 1 (countsOf lit)))).
  { fwd_if_temp _t'15 (Val.of_bool (if rl <? 0 then true
                         else negb (r1 + 257 =? Znth 0 (countsOf lit) + Znth 1 (countsOf lit)))).
    { forward. entailer!. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    { forward; forward.
      { entailer!; lia. }
      forward; forward.
      { entailer!; lia. }
      forward.
      forward.
      entailer!.
      rewrite (proj2 (Z.ltb_ge _ _)) by lia; destruct (zeq (r1 + 257) (Znth 0 (countsOf lit) + Znth 1 (countsOf lit))) as [E|E]; [rewrite (proj2 (Z.eqb_eq _ _) E)|rewrite (proj2 (Z.eqb_neq _ _) E)]; reflexivity.
    }
    entailer!. rewrite (proj2 (Z.eqb_neq _ _)) by auto. reflexivity.
  }
  { assert (rl = 0) by (match goal with H : Int.repr rl = Int.zero |- _ => apply (f_equal Int.signed) in H; rewrite Int.signed_repr in H by rep_lia; exact H end); subst rl; forward; entailer!. }
  destruct (if rl =? 0 then false else if rl <? 0 then true
            else negb (r1 + 257 =? Znth 0 (countsOf lit) + Znth 1 (countsOf lit))) eqn:B7.
  forward_if; [|discriminate].
  {
    assert (Hb : andb (notOversubZ (sublist 0 (r1 + 257) (lit ++ dist)))
                      (zlibOkZ (sublist 0 (r1 + 257) (lit ++ dist)) false) <> true)
      by (rewrite Sl, <- (Dyn_lit_check lit rl Hlo Hcol); intros [->|[Hp7 Hz7]];
          [simpl in B7; discriminate
          |rewrite (proj2 (Z.eqb_neq _ _)), (proj2 (Z.ltb_ge _ _)) in B7 by lia;
           rewrite Llit in Hz7; rewrite <- Hz7, Z.eqb_refl in B7; discriminate]);
    forward;
    sep_apply (Dyn_merge Tsh 316 (Zlength lit) (map Vint (map Int.repr lit))
                 (map Vint (map Int.repr dist) ++ rest) v_lengths ltac:(lia));
    sep_apply (Dyn_merge_ Tsh 286 (Zlength lit) symsl v_lensym ltac:(lia));
    dyn_fail (-7) out ica bba bca 0; hdr_inv; neq_true.
  }
  skip_then.
  assert (Hlit : andb (notOversubZ lit) (zlibOkZ lit false) = true)
    by (rewrite <- (Dyn_lit_check lit rl Hlo Hcol);
        destruct (Z.eq_dec rl 0) as [->|Hn0]; [left; auto|right];
        rewrite (proj2 (Z.eqb_neq _ _)) in B7 by auto;
        destruct (rl <? 0) eqn:Bn0; [discriminate|apply Z.ltb_ge in Bn0];
        apply negb_false_iff, Z.eqb_eq in B7; split; [lia|rewrite Llit; exact B7]).
  assert (Hrl0 : 0 <= rl) by (destruct (rl =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|];
                              destruct (rl <? 0) eqn:E1; [discriminate|apply Z.ltb_ge in E1; lia]).
  specialize (Htl Hrl0).
  assert_PROP (Zlength symsl = Zlength lit) as Hsyl by entailer!.
  rewrite (split2_data_at_Tarray_app (Zlength dist) (316 - Zlength lit) Tsh tshort (map Vint (map Int.repr dist))) by list_solve.
  rewrite (split2_data_at__Tarray_app (Zlength dist) 30 Tsh tshort v_distsym) by lia.
  Intros.
  forward_call (Tsh, Tsh, v_distcode, v_distcnt, v_distsym,
                field_address0 (tarray tshort 316) (SUB Zlength lit) v_lengths, dist).
  { entailer!.
match goal with H : field_compatible _ [] (field_address0 (tarray tshort 316) (SUB Zlength lit) v_lengths) |- _ =>
  assert (Fc : field_compatible0 (tarray tshort 316) (SUB Zlength lit) v_lengths)
    by (unfold field_address0 in H; destruct (field_compatible0_dec _ _ _); [auto|destruct H; contradiction]) end;
rewrite field_address0_offset by auto; simpl.
rewrite Llit, Ldist; f_equal; f_equal; f_equal; lia.
  }
  Intros vret. destruct vret as [rd2 symsd]. cbn [fst snd] in *.
  match goal with H : rd2 < 0 <-> _ |- _ => rename H into Hd1 end.
  match goal with H : 0 <= rd2 -> table _ _ |- _ => rename H into Htd end.
  assert (Hdo : Dyn_lens_ok dist) by exact Hfdist.
  assert (Hcod : Dyn_cons_ok dist rd2) by (split; auto).
  pose proof (Dyn_c01 dist Hdo) as D01.
  pose proof (Dyn_counts_len dist) as DL.
  fwd_if_temp _t'17 (Val.of_bool (if rd2 =? 0 then false else if rd2 <? 0 then true
                                  else negb (r2 + 1 =? Znth 0 (countsOf dist) + Znth 1 (countsOf dist)))).
  { fwd_if_temp _t'17 (Val.of_bool (if rd2 <? 0 then true
                         else negb (r2 + 1 =? Znth 0 (countsOf dist) + Znth 1 (countsOf dist)))).
    { forward. entailer!. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    { forward; forward.
      { entailer!; lia. }
      forward; forward.
      { entailer!; lia. }
      forward.
      forward.
      entailer!.
      rewrite (proj2 (Z.ltb_ge _ _)) by lia;
      destruct (zeq (r2 + 1) (Znth 0 (countsOf dist) + Znth 1 (countsOf dist))) as [E|E];
      [rewrite (proj2 (Z.eqb_eq _ _) E)|rewrite (proj2 (Z.eqb_neq _ _) E)]; reflexivity. }
    entailer!. rewrite (proj2 (Z.eqb_neq _ _)) by auto. reflexivity.
  }
  { assert (rd2 = 0) by (match goal with H : Int.repr rd2 = Int.zero |- _ => apply (f_equal Int.signed) in H; rewrite Int.signed_repr in H by rep_lia; exact H end); subst rd2; forward; entailer!. }
  destruct (if rd2 =? 0 then false else if rd2 <? 0 then true
            else negb (r2 + 1 =? Znth 0 (countsOf dist) + Znth 1 (countsOf dist))) eqn:B8.
  { forward_if; [|discriminate].
    assert (Hb : andb (notOversubZ (sublist (r1 + 257) (r1 + 257 + (r2 + 1)) (lit ++ dist)))
                      (zlibOkZ (sublist (r1 + 257) (r1 + 257 + (r2 + 1)) (lit ++ dist)) false) <> true)
      by (rewrite Sd, <- (Dyn_lit_check dist rd2 Hdo Hcod); intros [->|[Hp8 Hz8]];
          [simpl in B8; discriminate
          |rewrite (proj2 (Z.eqb_neq _ _)), (proj2 (Z.ltb_ge _ _)) in B8 by lia;
           rewrite Ldist in Hz8; rewrite <- Hz8, Z.eqb_refl in B8; discriminate]);
    forward;
    sep_apply (Dyn_merge Tsh (316 - Zlength lit) (Zlength dist) (map Vint (map Int.repr dist)) rest
                 (field_address0 (tarray tshort 316) (SUB Zlength lit) v_lengths) ltac:(lia));
    sep_apply (Dyn_merge_ Tsh 316 (Zlength lit) (map Vint (map Int.repr lit)) v_lengths ltac:(lia));
    sep_apply (Dyn_merge_ Tsh 286 (Zlength lit) symsl v_lensym ltac:(lia));
    sep_apply (Dyn_merge_ Tsh 30 (Zlength dist) symsd v_distsym ltac:(lia));
    dyn_fail (-8) out ica bba bca 0; hdr_inv; neq_true. }
  skip_then.
  assert (Hdist : andb (notOversubZ dist) (zlibOkZ dist false) = true)
    by (rewrite <- (Dyn_lit_check dist rd2 Hdo Hcod);
        destruct (Z.eq_dec rd2 0) as [->|Hn0]; [left; auto|right];
        rewrite (proj2 (Z.eqb_neq _ _)) in B8 by auto;
        destruct (rd2 <? 0) eqn:Bn0; [discriminate|apply Z.ltb_ge in Bn0];
        apply negb_false_iff, Z.eqb_eq in B8; split; [lia|rewrite Ldist; exact B8]).
  assert (Hrd0 : 0 <= rd2) by (destruct (rd2 =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|];
                               destruct (rd2 <? 0) eqn:E1; [discriminate|apply Z.ltb_ge in E1; lia]).
  specialize (Htd Hrd0).
  assert_PROP (Zlength symsd = Zlength dist) as Hsyd by entailer!.
  (* the header is the spec's *)
  assert (Hok : Dyn_hdr_ok bytes (8 * incnt - bitcnt) lit dist (8 * ica - bca)).
  { assert (Hclok : andb (notOversubZ cl) (zlibOkZ cl true) = true)
      by (apply (Dyn_cl_check cl 0 Hco); auto).
    exists r1, r2, r3, cl, (8 * ic - bc), (lit ++ dist).
    repeat split; auto; try lia. }
  assert (Hroom : room wr bytes out (8 * ica - bca))
    by (apply (Dyn_room_mono _ _ _ (8 * incnt - bitcnt)); [lia|auto]).
  sep_apply (Dyn_mk_htable Tsh v_lencode v_lencnt v_lensym lit symsl ltac:(lia) Hflit Hsyl Htl).
  sep_apply (Dyn_mk_htable Tsh v_distcode v_distcnt v_distsym dist symsd ltac:(lia) Hfdist Hsyd Htd).
  forward_call (sh, shi, sho, Tsh, s, outp, outlen, out, wr, inp, bytes, ica, bba, bca,
                v_lencode, (v_lencnt, v_lensym), lit, v_distcode, (v_distcnt, v_distsym), dist, gv).
  { cbn [fst snd]. cancel. }
  Intros vret. destruct vret as [[[[[r out'] ic'] bb'] bc'] e']. cbn [fst snd] in *.
  assert (Hbo : block_ok wr outlen
                  (match dynHeaderZ bytes (8 * incnt - bitcnt) with
                   | Some (lit, dist, q, true) => symsF lit dist bytes q out
                   | _ => None
                   end) r out' bytes ic' bb' bc' e').
  { change (block_ok wr outlen (Dyn_res bytes (8 * incnt - bitcnt) out) r out' bytes ic' bb' bc' e').
    rewrite (Dyn_res_some _ _ _ _ _ _ Hok). assumption. }
  forward.
  unfold htable. Intros syms1 syms2.
  match goal with H : Zlength syms1 = Zlength _ |- _ => rewrite H end;
  match goal with H : Zlength syms2 = Zlength _ |- _ => rewrite H end;
  sep_apply (Dyn_merge Tsh (316 - Zlength lit) (Zlength dist) (map Vint (map Int.repr dist)) rest
               (field_address0 (tarray tshort 316) (SUB Zlength lit) v_lengths) ltac:(lia));
  sep_apply (Dyn_merge_ Tsh 316 (Zlength lit) (map Vint (map Int.repr lit)) v_lengths ltac:(lia)).
  sep_apply (Dyn_merge_ Tsh 286 (Zlength lit) syms2 v_lensym ltac:(lia));
  sep_apply (Dyn_merge_ Tsh 30 (Zlength dist) syms1 v_distsym ltac:(lia));
  Exists r out' ic' bb' bc' e'; unfold all_tables, shortarr at 1; entailer!.
Qed.
