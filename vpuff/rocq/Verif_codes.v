(* puff's codes(): one block's literals and length/distance pairs, as the
   spec's inflateSyms (Inflate.symsF). VST proof of Spec_puff.codes_spec. *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model VPuff.Spec_puff VPuff.Inflate VPuff.CodesLemmas.
Require VPuff.InflateFacts.
Open Scope Z_scope.

Lemma fold_state_eq sh s outp outlen outcnt inp inlen incnt bitbuf bitcnt eof :
  data_at sh (Tstruct _state noattr)
    (outp, (Vint (Int.repr outlen), (Vint (Int.repr outcnt), (inp, (Vint (Int.repr inlen),
      (Vint (Int.repr incnt), (Vint (Int.repr bitbuf), (Vint (Int.repr bitcnt), Vint (Int.repr eof))))))))) s =
  state_rep sh s outp outlen outcnt inp inlen incnt bitbuf bitcnt eof.
Proof. reflexivity. Qed.

Ltac fold_state := rewrite fold_state_eq.

(* return from inside the loop: the tables back into htable *)
Ltac ret_tac r o ic bb bc ef symsl symsd :=
  forward; Exists r o ic bb bc ef; unfold htable;
  Exists symsl symsd; unfold state_rep, codes_tables, shortarr; entailer!.

Lemma buf_pos bytes ic bb bc : buf_ok bytes ic bb bc -> 0 <= 8 * ic - bc.
Proof. unfold buf_ok. lia. Qed.

Lemma body_codes : semax_body Vprog Gprog f_codes codes_spec.
Proof.
  start_function.
  destruct lt as [cntl syml], dt as [cntd symd]. cbn [fst snd] in *.
  unfold htable. Intros symsl symsd.
  assert (Hin : 0 <= Zlength bytes <= 1073741824) by (unfold sizes_ok in *; tauto).
  assert (Zlength lensTab = 29 /\ Zlength lextTab = 29 /\ Zlength distsTab = 30 /\ Zlength dextTab = 30)
    as (Htl1 & Htl2 & Htl3 & Htl4) by (repeat split; reflexivity).
  assert_PROP (if wr then isptr outp else outp = nullval) as Hout.
  { destruct wr; unfold outbuf; entailer!. unfold sizes_ok in *; tauto. }
  assert (Hpn : is_pointer_or_null outp) by (destruct wr; [destruct outp; try contradiction; exact I | subst; hnf; auto]).
  remember (symsF lit dist bytes (8 * incnt - bitcnt) out) as target eqn:Htarget.
  forward_loop
    (EX out_c : list Z, EX ic : Z, EX bb : Z, EX bc : Z,
     PROP (out_ok wr outlen out_c; buf_ok bytes ic bb bc; room wr bytes out_c (8 * ic - bc);
           symsF lit dist bytes (8 * ic - bc) out_c = target)
     LOCAL (temp _s s; temp _lencode hl; temp _distcode hd; gvars gv)
     SEP (state_rep sh s outp outlen (Zlength out_c) inp (Zlength bytes) ic bb bc 0;
          data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
          outbuf wr sho outp outlen out_c;
          data_at shh (Tstruct _huffman noattr) (cntl, syml) hl;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf lit))) cntl;
          data_at shh (tarray tshort (Zlength symsl)) symsl syml;
          data_at shh (Tstruct _huffman noattr) (cntd, symd) hd;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf dist))) cntd;
          data_at shh (tarray tshort (Zlength symsd)) symsd symd;
          codes_tables gv))%assert
  break:
    (EX out_c : list Z, EX ic : Z, EX bb : Z, EX bc : Z,
     PROP (out_ok wr outlen out_c; buf_ok bytes ic bb bc; room wr bytes out_c (8 * ic - bc);
           target = Some (out_c, 8 * ic - bc))
     LOCAL (temp _s s; temp _lencode hl; temp _distcode hd; gvars gv)
     SEP (state_rep sh s outp outlen (Zlength out_c) inp (Zlength bytes) ic bb bc 0;
          data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
          outbuf wr sho outp outlen out_c;
          data_at shh (Tstruct _huffman noattr) (cntl, syml) hl;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf lit))) cntl;
          data_at shh (tarray tshort (Zlength symsl)) symsl syml;
          data_at shh (Tstruct _huffman noattr) (cntd, symd) hd;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf dist))) cntd;
          data_at shh (tarray tshort (Zlength symsd)) symsd symd;
          codes_tables gv))%assert.
  { Exists out incnt bitbuf bitcnt. entailer!. }
  2: { (* the end-of-block symbol *)
    Intros out_c ic bb bc. forward.
    Exists 0 out_c ic bb bc 0. unfold htable.
    Exists symsl symsd. entailer!.
    match goal with H : _ = Some (out_c, _) |- _ => rewrite H end.
    match goal with H : out_ok _ _ _ |- _ => destruct H as (? & Hf & ?) end.
    unfold block_ok. rewrite Hf. refine (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj eq_refl _))))); auto. }
  Intros out_c ic bb bc.
  match goal with H : out_ok _ _ out_c |- _ => rename H into Hok end.
  match goal with H : buf_ok _ ic _ _ |- _ => rename H into Hbuf end.
  match goal with H : room _ _ out_c _ |- _ => rename H into Hroom end.
  match goal with H : symsF _ _ _ _ out_c = target |- _ => rename H into Hinv end.
  pose proof (buf_pos _ _ _ _ Hbuf) as Hp.
  assert (Hlen : Zlength out_c <= 2147483647) by (destruct Hok as (_ & _ & ?); auto).
  forward_call (sh, shi, shh, s, outp, outlen, Zlength out_c, inp, bytes, ic, bb, bc, hl, cntl, syml, lit, symsl).
  Intros vret. destruct vret as [[[[r ic1] bb1] bc1] eof1]. cbn [fst snd] in *.
  match goal with H : match lean_decode lit _ _ with _ => _ end |- _ => rename H into Hdec end.
  destruct (lean_decode lit bytes (8 * ic - bc)) as [[sym p1]|] eqn:Ed.
  2: { (* invalid symbol *)
    forward_if.
    - ret_tac r out_c ic1 bb1 bc1 eof1 symsl symsd.
      rewrite <- Hinv, step_none by auto. apply block_none. lia.
    - try rewrite Int.signed_repr in * by rep_lia. lia. }
  destruct Hdec as (-> & Hp1 & Hbuf1 & ->).
  destruct (InflateFacts.lean_decode_bounds _ _ _ _ _ Hp Ed) as [Hpp1 Hsym].
  subst p1.
  forward_if; [lia|].
  forward_if
    (EX v : Z, EX o : list Z, EX ic' : Z, EX bb' : Z, EX bc' : Z,
     PROP (0 <= v <= 256; out_ok wr outlen o; buf_ok bytes ic' bb' bc'; room wr bytes o (8 * ic' - bc');
           if v =? 256 then target = Some (o, 8 * ic' - bc')
           else symsF lit dist bytes (8 * ic' - bc') o = target)
     LOCAL (temp _symbol (Vint (Int.repr v)); temp _s s; temp _lencode hl; temp _distcode hd; gvars gv)
     SEP (state_rep sh s outp outlen (Zlength o) inp (Zlength bytes) ic' bb' bc' 0;
          data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
          outbuf wr sho outp outlen o;
          data_at shh (Tstruct _huffman noattr) (cntl, syml) hl;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf lit))) cntl;
          data_at shh (tarray tshort (Zlength symsl)) symsl syml;
          data_at shh (Tstruct _huffman noattr) (cntd, symd) hd;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf dist))) cntd;
          data_at shh (tarray tshort (Zlength symsd)) symsd symd;
          codes_tables gv))%assert.
  { (* a literal *)
    pose proof (step_lit lit dist bytes out_c _ Hp _ _ Ed ltac:(lia)) as Hstep.
    unfold state_rep. forward.
    forward_if
      (PROP (out_ok wr outlen (out_c ++ [sym]))
       LOCAL (temp _symbol (Vint (Int.repr sym)); temp _s s; temp _lencode hl; temp _distcode hd; gvars gv)
       SEP (data_at sh (Tstruct _state noattr)
              (outp, (Vint (Int.repr outlen), (Vint (Int.repr (Zlength out_c)), (inp, (Vint (Int.repr (Zlength bytes)),
               (Vint (Int.repr ic1), (Vint (Int.repr bb1), (Vint (Int.repr bc1), Vint (Int.repr 0))))))))) s;
            data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
            outbuf wr sho outp outlen (out_c ++ [sym]);
            data_at shh (Tstruct _huffman noattr) (cntl, syml) hl;
            data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf lit))) cntl;
            data_at shh (tarray tshort (Zlength symsl)) symsl syml;
            data_at shh (Tstruct _huffman noattr) (cntd, symd) hd;
            data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf dist))) cntd;
            data_at shh (tarray tshort (Zlength symsd)) symsd symd;
            codes_tables gv)).
    { destruct wr; unfold outbuf.
      - assert (0 < outlen) by (unfold sizes_ok in *; tauto). entailer!.
      - subst outp. entailer!. }
    - (* out != NULL: write the literal *)
      destruct wr; [|subst outp; contradiction].
      unfold outbuf.
      assert (Hfit : Zlength out_c <= outlen) by
        (destruct Hok as (_ & Hf & _); apply Z.leb_le in Hf; auto).
      assert (Hol : 0 < outlen <= 2147483647) by (unfold sizes_ok in *; tauto).
      forward. forward.
      forward_if.
      + ret_tac 1 out_c ic1 bb1 bc1 0 symsl symsd.
        apply block_fail; [lia|]. intros o q E. rewrite <- Hinv, Hstep in E.
        eapply nospace; [|exact E]. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      + 
        forward. forward. forward; [entailer!; lia|].
        rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; lia).
        rewrite out_upd by lia.
        entailer!.
        apply out_ok_wr; [apply bytes_ok_app1; [apply Hok|lia] | list_solve].
    - (* NIL: count only *)
      destruct wr; [subst outp; contradiction|].
      forward. entailer!.
      apply out_ok_nil with (bytes := bytes) (p := 8 * ic1 - bc1).
      + apply bytes_ok_app1; [apply Hok|lia].
      + apply room_lit with (p := 8 * ic - bc); [auto|lia].
      + lia.
    - Intros. forward. forward.
      Exists sym (out_c ++ [sym]) ic1 bb1 bc1. unfold state_rep.
      rewrite Zlength_app, Zlength_cons, Zlength_nil.
      entailer!.
      split; [apply room_lit with (p := 8 * ic - bc); [auto|lia]|].
      rewrite (proj2 (Z.eqb_neq _ _)) by lia. congruence. }
  (* not a literal *)
  forward_if.
  2: { (* the end of the block *)
    assert (sym = 256) by lia. subst sym.
    forward. Exists 256 out_c ic1 bb1 bc1. entailer!.
    split; [eapply room_mono; [eassumption|lia]|].
    rewrite Z.eqb_refl, <- Hinv. exact (step_end lit dist bytes out_c _ Hp _ _ Ed eq_refl). }
  (* a length *)
  forward. rewrite sub_repr.
  forward_if.
  { ret_tac (-10) out_c ic1 bb1 bc1 0 symsl symsd.
    apply block_fail; [lia|]. intros o q E.
    rewrite <- Hinv, (step_badlen lit dist bytes out_c _ Hp _ _ Ed) in E by lia. discriminate. }
  destruct (lensTab_ok (sym - 257) ltac:(lia)) as (Hlb & Hlx & Hlxr & Hlb3 & Hlbx).
  unfold codes_tables, shortarr. Intros.
  forward; [rewrite Hlx; entailer!; lia|].
  rewrite Hlx.
  forward_call (sh, shi, s, outp, outlen, Zlength out_c, inp, bytes, ic1, bb1, bc1, lenExtraZ (sym - 257)).
  Intros vret. destruct vret as [[[[e ic2] bb2] bc2] eof2]. cbn [fst snd] in *.
  match goal with H : context [Spec_puff.lsbZ] |- _ => rename H into Hbits end.
  destruct (_ <=? _) eqn:Eb in Hbits.
  2: { (* out of input *)
    destruct Hbits as [-> ->]. apply Z.leb_gt in Eb.
    unfold state_rep. forward. forward. forward_if.
    - ret_tac 2 out_c ic2 bb2 bc2 1 symsl symsd.
      apply block_fail; [lia|]. intros o q E.
      rewrite <- Hinv, (step_len_eof lit dist bytes out_c _ Hp _ _ Ed (sym - 257)) in E by lia.
      discriminate.
    - exfalso. match goal with H : Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
  destruct Hbits as (-> & Hp2 & Hbuf2 & ->). apply Z.leb_le in Eb.
  unfold state_rep. forward. forward. forward_if; [exfalso; match goal with H : Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end|].
  pose proof (lsbZ_range bytes (8 * ic1 - bc1) (Z.to_nat (lenExtraZ (sym - 257)))) as He.
  rewrite Z2Nat.id in He by lia.
  forward; [rewrite Hlb; entailer!; lia|].
  rewrite Hlb. forward.
  fold_state.
  forward_call (sh, shi, shh, s, outp, outlen, Zlength out_c, inp, bytes, ic2, bb2, bc2, hd, cntd, symd, dist, symsd).
  Intros vret. destruct vret as [[[[ds ic3] bb3] bc3] eof3]. cbn [fst snd] in *.
  match goal with H : match lean_decode dist _ _ with _ => _ end |- _ => rename H into Hdec2 end.
  rewrite Hp2 in Hdec2.
  destruct (lean_decode dist bytes (8 * ic1 - bc1 + lenExtraZ (sym - 257))) as [[ds' p3]|] eqn:Edd.
  2: { (* invalid distance symbol *)
    forward_if.
    - ret_tac ds out_c ic3 bb3 bc3 eof3 symsl symsd.
      rewrite <- Hinv, (step_dist_none lit dist bytes out_c _ Hp _ _ Ed (sym - 257)) by (auto; lia).
      apply block_none. lia.
    - exfalso. try rewrite Int.signed_repr in * by rep_lia. lia. }
  destruct Hdec2 as (<- & Hp3 & Hbuf3 & ->). subst p3.
  destruct (InflateFacts.lean_decode_bounds _ _ _ _ _
    (ltac:(lia) : 0 <= 8 * ic1 - bc1 + lenExtraZ (sym - 257)) Edd) as [Hpp3 Hds].
  forward_if; [lia|].
  destruct (distsTab_ok ds ltac:(lia)) as (Hdb & Hdx & Hdxr & Hdb1 & Hdbx).
  forward; [rewrite Hdx; entailer!; lia|].
  rewrite Hdx.
  forward_call (sh, shi, s, outp, outlen, Zlength out_c, inp, bytes, ic3, bb3, bc3, distExtraZ ds).
  Intros vret. destruct vret as [[[[e2 ic4] bb4] bc4] eof4]. cbn [fst snd] in *.
  match goal with H : context [Spec_puff.lsbZ] |- _ => rename H into Hbits2 end.
  destruct (_ <=? _) eqn:Eb2 in Hbits2.
  2: { (* out of input *)
    destruct Hbits2 as [-> ->]. apply Z.leb_gt in Eb2.
    unfold state_rep. forward. forward. forward_if.
    - ret_tac 2 out_c ic4 bb4 bc4 1 symsl symsd.
      apply block_fail; [lia|]. intros o q E.
      rewrite <- Hinv, (step_dist_eof lit dist bytes out_c _ Hp _ _ Ed (sym - 257) ltac:(lia) eq_refl
        ltac:(lia) ltac:(lia) ds _ Edd ltac:(lia)) in E by lia.
      discriminate.
    - exfalso. match goal with H : Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
  destruct Hbits2 as (-> & Hp4 & Hbuf4 & ->). apply Z.leb_le in Eb2.
  pose proof (lsbZ_range bytes (8 * ic3 - bc3) (Z.to_nat (distExtraZ ds))) as He2.
  rewrite Z2Nat.id in He2 by lia.
  unfold state_rep. forward. forward.
  forward_if; [exfalso; match goal with H : Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end|].
  forward; [rewrite Hdb; entailer!; lia|].
  rewrite Hdb. forward. forward.
  rewrite !add_repr.
  pose proof (step_far lit dist bytes out_c _ Hp _ _ Ed (sym - 257) ltac:(lia) eq_refl
      ltac:(lia) ltac:(lia) ds _ Edd ltac:(lia) ltac:(lia)) as Hfar_step.
  pose proof (step_copy lit dist bytes out_c _ Hp _ _ Ed (sym - 257) ltac:(lia) eq_refl ltac:(lia) ltac:(lia)
                ds _ Edd ltac:(lia) ltac:(lia)) as Hcopy_step.
  set (E := Spec_puff.lsbZ bytes (8 * ic1 - bc1) (Z.to_nat (lenExtraZ (sym - 257)))) in *.
  set (E2 := Spec_puff.lsbZ bytes (8 * ic3 - bc3) (Z.to_nat (distExtraZ ds))) in *.
  clearbody E E2.
  rewrite (Z.add_comm E2), (Z.add_comm E).
  forward_if.
  { (* too far back *)
    ret_tac (-11) out_c ic4 bb4 bc4 0 symsl symsd.
    rewrite <- Hinv, Hfar_step by
      (repeat match goal with H : context [Int.unsigned (Int.repr ?x)] |- _ =>
                rewrite (Int.unsigned_repr x) in H by rep_lia end; lia).
    apply block_none. lia. }
  assert (Hfar : distBaseZ ds + E2 <= Zlength out_c) by
    (repeat match goal with H : context [Int.unsigned (Int.repr ?x)] |- _ =>
              rewrite (Int.unsigned_repr x) in H by rep_lia end; lia).
  pose proof (Hcopy_step Hfar ltac:(lia) ltac:(lia)) as Hstep.
  set (D := distBaseZ ds + E2) in *. set (L := lenBaseZ (sym - 257) + E) in *.
  assert (HL : 3 <= L <= 258) by lia.
  assert (HD : 1 <= D <= Zlength out_c) by lia.
  assert (Hpos : 8 * ic - bc + 2 <= 8 * ic4 - bc4) by lia.
  clearbody D L.
  forward.
  forward_if
    (PROP (out_ok wr outlen (lzCopyZ out_c D (Z.to_nat L)))
     LOCAL (temp _symbol (Vint (Int.repr ds)); temp _s s; temp _lencode hl; temp _distcode hd; gvars gv)
     SEP (data_at sh (Tstruct _state noattr)
            (outp, (Vint (Int.repr outlen), (Vint (Int.repr (Zlength (lzCopyZ out_c D (Z.to_nat L)))), (inp, (Vint (Int.repr (Zlength bytes)),
             (Vint (Int.repr ic4), (Vint (Int.repr bb4), (Vint (Int.repr bc4), Vint (Int.repr 0))))))))) s;
          outbuf wr sho outp outlen (lzCopyZ out_c D (Z.to_nat L));
          data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
          data_at shh (Tstruct _huffman noattr) (cntl, syml) hl;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf lit))) cntl;
          data_at shh (tarray tshort (Zlength symsl)) symsl syml;
          data_at shh (Tstruct _huffman noattr) (cntd, symd) hd;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf dist))) cntd;
          data_at shh (tarray tshort (Zlength symsd)) symsd symd;
          data_at Ers (tarray tshort 29) (map Vint (map Int.repr lensTab)) (gv _lens);
          data_at Ers (tarray tshort 29) (map Vint (map Int.repr lextTab)) (gv _lext);
          data_at Ers (tarray tshort 30) (map Vint (map Int.repr distsTab)) (gv _dists);
          data_at Ers (tarray tshort 30) (map Vint (map Int.repr dextTab)) (gv _dext))).
  { destruct wr; unfold outbuf.
    - assert (0 < outlen) by (unfold sizes_ok in *; tauto). entailer!.
    - subst outp. entailer!. }
  - (* out != NULL: copy *)
    destruct wr; [|subst outp; contradiction].
    unfold outbuf.
    assert (Hfit : Zlength out_c <= outlen) by
      (destruct Hok as (_ & Hf & _); apply Z.leb_le in Hf; auto).
    assert (Hol : 0 < outlen <= 2147483647) by (unfold sizes_ok in *; tauto).
    forward. forward.
    forward_if.
    { ret_tac 1 out_c ic4 bb4 bc4 0 symsl symsd.
      apply block_fail; [lia|]. intros o q E'. rewrite <- Hinv, Hstep in E'.
      eapply nospace; [|exact E']. rewrite lzCopyZ_length, Z2Nat.id by lia.
      repeat match goal with H : context [Int.unsigned (Int.repr ?x)] |- _ =>
                rewrite (Int.unsigned_repr x) in H by rep_lia end; lia. }
    assert (Hroom2 : Zlength out_c + L <= outlen) by
      (repeat match goal with H : context [Int.unsigned (Int.repr ?x)] |- _ =>
                rewrite (Int.unsigned_repr x) in H by rep_lia end; lia).
    forward_loop
      (EX k : Z,
       PROP (0 <= k <= L)
       LOCAL (temp _len (Vint (Int.repr (L - k))); temp _dist (Vint (Int.repr D));
              temp _symbol (Vint (Int.repr ds)); temp _s s; temp _lencode hl; temp _distcode hd; gvars gv)
       SEP (data_at sh (Tstruct _state noattr)
            (outp, (Vint (Int.repr outlen), (Vint (Int.repr (Zlength out_c + k)), (inp, (Vint (Int.repr (Zlength bytes)),
             (Vint (Int.repr ic4), (Vint (Int.repr bb4), (Vint (Int.repr bc4), Vint (Int.repr 0))))))))) s;
            data_at sho (tarray tuchar outlen)
              (map Vint (map Int.repr (lzCopyZ out_c D (Z.to_nat k))) ++
               Zrepeat Vundef (outlen - Zlength (lzCopyZ out_c D (Z.to_nat k)))) outp;
            data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
          data_at shh (Tstruct _huffman noattr) (cntl, syml) hl;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf lit))) cntl;
          data_at shh (tarray tshort (Zlength symsl)) symsl syml;
          data_at shh (Tstruct _huffman noattr) (cntd, symd) hd;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf dist))) cntd;
          data_at shh (tarray tshort (Zlength symsd)) symsd symd;
          data_at Ers (tarray tshort 29) (map Vint (map Int.repr lensTab)) (gv _lens);
          data_at Ers (tarray tshort 29) (map Vint (map Int.repr lextTab)) (gv _lext);
          data_at Ers (tarray tshort 30) (map Vint (map Int.repr distsTab)) (gv _dists);
          data_at Ers (tarray tshort 30) (map Vint (map Int.repr dextTab)) (gv _dext)))%assert
    break:
      (PROP (out_ok true outlen (lzCopyZ out_c D (Z.to_nat L)))
       LOCAL (temp _symbol (Vint (Int.repr ds)); temp _s s; temp _lencode hl; temp _distcode hd; gvars gv)
       SEP (data_at sh (Tstruct _state noattr)
            (outp, (Vint (Int.repr outlen), (Vint (Int.repr (Zlength (lzCopyZ out_c D (Z.to_nat L)))), (inp, (Vint (Int.repr (Zlength bytes)),
             (Vint (Int.repr ic4), (Vint (Int.repr bb4), (Vint (Int.repr bc4), Vint (Int.repr 0))))))))) s;
            outbuf true sho outp outlen (lzCopyZ out_c D (Z.to_nat L));
            data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
          data_at shh (Tstruct _huffman noattr) (cntl, syml) hl;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf lit))) cntl;
          data_at shh (tarray tshort (Zlength symsl)) symsl syml;
          data_at shh (Tstruct _huffman noattr) (cntd, symd) hd;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf dist))) cntd;
          data_at shh (tarray tshort (Zlength symsd)) symsd symd;
          data_at Ers (tarray tshort 29) (map Vint (map Int.repr lensTab)) (gv _lens);
          data_at Ers (tarray tshort 29) (map Vint (map Int.repr lextTab)) (gv _lext);
          data_at Ers (tarray tshort 30) (map Vint (map Int.repr distsTab)) (gv _dists);
          data_at Ers (tarray tshort 30) (map Vint (map Int.repr dextTab)) (gv _dext))).
    { Exists 0. change (Z.to_nat 0) with O. cbn [lzCopyZ]. rewrite Z.add_0_r, Z.sub_0_r. entailer!. }
    Intros k. forward. forward.
    forward_if.
    2: { (* len was 0: done *)
      assert (k = L).
      { match goal with H : Int.repr (L - k) = _ |- _ =>
          apply (f_equal Int.signed) in H; rewrite !Int.signed_repr in H by rep_lia;
          rewrite ?Int.signed_zero in H end. lia. }
      subst k. forward.
      unfold outbuf. rewrite !lzCopyZ_length, Z2Nat.id by lia. entailer!.
      apply out_ok_wr; [apply lzCopyZ_bytes, Hok|]. rewrite lzCopyZ_length, Z2Nat.id; lia. }
    assert (Hk : k < L).
    { assert (k <> L); [|lia]. intro; subst k.
      match goal with H : Int.repr (L - L) <> _ |- _ => apply H; rewrite Z.sub_diag; reflexivity end. }
    assert (Hcl : Zlength (lzCopyZ out_c D (Z.to_nat k)) = Zlength out_c + k)
      by (rewrite lzCopyZ_length, Z2Nat.id; lia).
    assert (Hcb : bytes_ok (lzCopyZ out_c D (Z.to_nat k))) by (apply lzCopyZ_bytes, Hok).
    assert (Hx : 0 <= Znth (Zlength out_c + k - D) (lzCopyZ out_c D (Z.to_nat k)) < 256)
      by (apply (sublist.Forall_Znth (fun b => 0 <= b < 256)); [lia | exact Hcb]).
    forward. forward. forward. forward.
    forward.
    { entailer!. rewrite copy_read by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite copy_read by lia.
    forward. forward. forward.
    Exists (k + 1).
    rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; lia).
    rewrite copy_write by lia.
    replace (Zlength out_c + (k + 1)) with (Zlength out_c + k + 1) by lia.
    replace (L - (k + 1)) with (L - k - 1) by lia.
    entailer!.
  - (* NIL: count only *)
    destruct wr; [subst outp; contradiction|].
    forward. forward. rewrite add_repr, lzCopyZ_length, Z2Nat.id by lia. entailer!.
    apply out_ok_nil with (bytes := bytes) (p := 8 * ic4 - bc4).
    + apply lzCopyZ_bytes, Hok.
    + apply room_copy with (p := 8 * ic - bc); auto; lia.
    + lia.
  - Exists ds (lzCopyZ out_c D (Z.to_nat L)) ic4 bb4 bc4. unfold state_rep, codes_tables, shortarr. entailer!.
    split; [apply room_copy with (p := 8 * ic - bc); auto; lia|].
    rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite <- Hinv, Hstep. f_equal. lia.
  - (* the loop test *)
    Intros v o ic' bb' bc'.
    forward_if.
    + forward. Exists o ic' bb' bc'.
      entailer!; rewrite (proj2 (Z.eqb_neq _ _)) in * by lia; auto.
    + forward. Exists o ic' bb' bc'.
      entailer!; rewrite (proj2 (Z.eqb_eq _ _)) in * by lia; auto.
Qed.
