(* puff's stored(): a stored block, as the spec's storedZ (Inflate.v). VST
   proof of Spec_puff.stored_spec. *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model VPuff.Spec_puff VPuff.P2_Bits VPuff.P2_Stored.
Open Scope Z_scope.

Ltac tcb := entailer!; try (simpl; rewrite ?Int.unsigned_repr by rep_lia; rep_lia).
Ltac fw := forward; try solve [tcb].

Lemma ne_bool x y : 0 <= x < 256 -> 0 <= y < 256 ->
  bool2val (negb (Int.eq (Int.repr x) (Int.repr y))) = Vint (Int.repr (if x =? y then 0 else 1)).
Proof.
  intros. destruct (Z.eqb_spec x y).
  - subst. rewrite Int.eq_true. reflexivity.
  - rewrite Int.eq_false; [reflexivity|].
    intro E. apply repr_inj_unsigned in E; [contradiction|rep_lia|rep_lia].
Qed.

Lemma shiftr_byte8 x : 0 <= x < 256 -> Z.shiftr x 8 = 0.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. simpl. lia. Qed.

Lemma buf_ok_aligned bytes k : Forall (fun b => 0 <= b < 256) bytes -> 0 <= k <= Zlength bytes ->
  buf_ok bytes k 0 0.
Proof.
  intros Hb Hk. unfold buf_ok. split; [lia|]. split; [lia|]. split; [auto|].
  destruct (k =? 0) eqn:E; [reflexivity|]. apply Z.eqb_neq in E. simpl Z.sub.
  rewrite shiftr_byte8; [reflexivity|]. apply byte_range; auto; lia.
Qed.

Lemma stored_out_ok wr outlen out bs : out_ok wr outlen out -> Forall (fun b => 0 <= b < 256) bs ->
  fits wr outlen (out ++ bs) = true -> Zlength (out ++ bs) <= 2147483647 ->
  out_ok wr outlen (out ++ bs).
Proof.
  unfold out_ok, bytes_ok. intros (Ho & _ & _) Hb Hf Hl. split; [apply Forall_app; auto|]. auto.
Qed.

Lemma stored_room bytes out p k L :
  room false bytes out p -> p <= 8 * k -> 0 <= L -> 0 <= k -> k + 4 + L <= Zlength bytes ->
  (room false bytes (out ++ sublist (k + 4) (k + 4 + L) bytes) (8 * (k + 4 + L)) /\
   Zlength (out ++ sublist (k + 4) (k + 4 + L) bytes) <= 2147483647).
Proof.
  unfold room, VPuff.Inflate.nbits. intros [D|R] Hp HL Hk Hn; [discriminate|].
  rewrite Zlength_app, Zlength_sublist by lia. split; [right|]; lia.
Qed.

Lemma copy_upd (out bytes : list Z) k i outlen :
  0 <= k -> 0 <= i -> k + i < Zlength bytes -> Zlength out + i < outlen ->
  upd_Znth (Zlength out + i)
    (map Vint (map Int.repr (out ++ sublist k (k + i) bytes)) ++
     Zrepeat Vundef (outlen - Zlength (out ++ sublist k (k + i) bytes)))
    (Vint (Int.repr (Znth (k + i) bytes))) =
  map Vint (map Int.repr (out ++ sublist k (k + (i + 1)) bytes)) ++
  Zrepeat Vundef (outlen - Zlength (out ++ sublist k (k + (i + 1)) bytes)).
Proof.
  intros. rewrite (sublist_split k (k + i) (k + (i + 1))) by lia.
  replace (k + (i + 1)) with (k + i + 1) by lia.
  rewrite (sublist_len_1 (k + i)) by lia. rewrite app_assoc. list_solve.
Qed.

Lemma body_stored : semax_body Vprog Gprog f_stored stored_spec.
Proof.
  start_function.
  unfold bytes_ok in *.
  match goal with H : buf_ok _ _ _ _ |- _ => destruct H as (Hinc & Hbc & Hinc0 & Hbuf) end.
  match goal with H : Forall _ bytes |- _ => rename H into Hbytes end.
  assert (Hin : 0 <= Zlength bytes <= 1073741824) by (unfold sizes_ok in *; tauto).
  assert (Hol : Zlength out <= 2147483647) by (unfold out_ok in *; tauto).
  assert (Hpos : wr = true -> 0 < outlen /\ outlen <= 2147483647).
  { intros ->. match goal with H : sizes_ok _ _ _ _ |- _ => destruct H as [_ Hw]; exact Hw end. }
  assert_PROP (if wr then isptr outp else outp = nullval) as Hout.
  { destruct wr; unfold outbuf; entailer!. unfold sizes_ok in *; tauto. }
  assert (Hpn : is_pointer_or_null outp)
    by (destruct wr; [destruct outp; try contradiction; exact I | subst; hnf; auto]).
  unfold state_rep.
  forward. forward. (* bitbuf = 0; bitcnt = 0 *)
  forward. forward.
  forward_if.
  { (* no room for the header *)
    forward. Exists 2 out incnt 0 0 0. unfold state_rep. entailer!.
    rewrite stored_short by (try assumption; lia). discriminate. }
  assert (Ha := byte_range bytes Hbytes incnt ltac:(lia)).
  assert (Hb := byte_range bytes Hbytes (incnt + 1) ltac:(lia)).
  assert (Hc := byte_range bytes Hbytes (incnt + 2) ltac:(lia)).
  assert (Hd := byte_range bytes Hbytes (incnt + 3) ltac:(lia)).
  fw. fw. fw. fw.
  fw. fw. fw. fw.
  fw.
  rewrite len_repr by lia.
  fw. fw. fw. fw.
  forward_if (EX ic : Z,
    PROP (incnt + 3 <= ic <= incnt + 4; andb (Znth (incnt + 2) bytes =? 255 - Znth incnt bytes) (Znth (incnt + 3) bytes =? 255 - Znth (incnt + 1) bytes) = true -> (ic = incnt + 4)%Z)
    LOCAL (temp _t'4 (Vint (Int.repr (if andb (Znth (incnt + 2) bytes =? 255 - Znth incnt bytes) (Znth (incnt + 3) bytes =? 255 - Znth (incnt + 1) bytes) then 0 else 1)));
           temp _len (Vint (Int.repr (Znth incnt bytes + 256 * Znth (incnt + 1) bytes))); temp _s s)
    SEP (data_at sh (Tstruct _state noattr)
           (outp, (Vint (Int.repr outlen), (Vint (Int.repr (Zlength out)), (inp,
            (Vint (Int.repr (Zlength bytes)), (Vint (Int.repr (ic)), (Vint (Int.repr 0),
             (Vint (Int.repr 0), Vint (Int.repr 0))))))))) s;
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         outbuf wr sho outp outlen out))%assert.
  { (* the first complement byte is wrong *)
    match goal with Hx : context [Int.not _] |- _ => rewrite not_low in Hx by lia; rename Hx into Hcmp end.
    assert (Hne : Znth (incnt + 2) bytes <> 255 - Znth incnt bytes) by (intro E; apply Hcmp; rewrite E; reflexivity).
    fw. Exists (incnt + 1 + 1 + 1).
    rewrite (proj2 (Z.eqb_neq _ _) Hne). cbn [andb].
    entailer!. }
  { match goal with Hx : context [Int.not _] |- _ => rewrite not_low in Hx by lia; rename Hx into Hcmp end.
    apply repr_inj_unsigned in Hcmp; [|rep_lia|rep_lia].
    fw. fw. fw. fw. fw.
    rewrite not_high by lia.
    replace (incnt + (1 + (1 + 1))) with (incnt + 3) by lia.
    rewrite ne_bool by lia.
    Exists (incnt + 1 + 1 + 1 + 1).
    rewrite Hcmp, Z.eqb_refl. cbn [andb].
    entailer!. }
  Intros ic.
  destruct (andb (Znth (incnt + 2) bytes =? 255 - Znth incnt bytes) (Znth (incnt + 3) bytes =? 255 - Znth (incnt + 1) bytes)) eqn:Eok.
  2:{ (* complement mismatch *)
    forward_if.
    - forward. Exists (-2) out ic 0 0 0. unfold state_rep. entailer!.
      rewrite stored_header by (try assumption; lia). cbv zeta. rewrite Eok. cbn [andb]. discriminate.
    - exfalso. apply Int.one_not_zero. assumption. }
  match goal with H : true = true -> _ |- _ => specialize (H eq_refl); subst ic end.
  forward_if; [exfalso; lia|].
  fw. fw.
  forward_if.
  { (* not enough input for the block *)
    forward. Exists 2 out (incnt + 4) 0 0 0. unfold state_rep. entailer!.
    rewrite stored_header by (try assumption; lia). cbv zeta. rewrite Eok. cbn [andb].
    rewrite (proj2 (Z.leb_gt _ _)) by lia. discriminate. }
  assert (Hst : storedZ bytes (8 * incnt - bitcnt) =
                Some ((sublist (incnt + 4) (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) bytes), 8 * (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)))).
  { rewrite stored_header by (try assumption; lia). cbv zeta. rewrite Eok. cbn [andb].
    rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (HbsF : Forall (fun b => 0 <= b < 256) (sublist (incnt + 4) (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) bytes)) by (apply Forall_sublist; auto).
  assert (Hbs : Zlength (sublist (incnt + 4) (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) bytes) = (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) by (rewrite Zlength_sublist by lia; lia).
  fw.
  forward_if (PROP (fits wr outlen (out ++ (sublist (incnt + 4) (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) bytes)) = true)
    LOCAL (temp _s s)
    SEP (data_at sh (Tstruct _state noattr)
           (outp, (Vint (Int.repr outlen), (Vint (Int.repr (Zlength out + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes))), (inp,
            (Vint (Int.repr (Zlength bytes)), (Vint (Int.repr (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes))), (Vint (Int.repr 0),
             (Vint (Int.repr 0), Vint (Int.repr 0))))))))) s;
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         outbuf wr sho outp outlen (out ++ (sublist (incnt + 4) (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) bytes)))).
  { destruct wr; unfold outbuf.
    - assert (0 < outlen) by (apply Hpos; reflexivity). entailer!.
    - subst outp. entailer!. }
  { (* writing *)
    destruct wr; [|subst outp; contradiction].
    unfold outbuf.
    destruct (Hpos eq_refl) as [Hop Hol'].
    assert (Hfit : Zlength out <= outlen) by
      (destruct H1 as (_ & Hf & _); apply Z.leb_le in Hf; auto).
    fw. fw.
    forward_if.
    { forward. Exists 1 out (incnt + 4) 0 0 0. unfold state_rep, outbuf. entailer!.
      rewrite Hst. cbv beta iota. unfold fits. rewrite Zlength_app, Hbs.
      rewrite (proj2 (Z.leb_gt _ _)) by lia. discriminate. }
    forward_loop (EX i : Z,
      PROP (0 <= i <= (Znth incnt bytes + 256 * Znth (incnt + 1) bytes))
      LOCAL (temp _len (Vint (Int.repr ((Znth incnt bytes + 256 * Znth (incnt + 1) bytes) - i))); temp _s s)
      SEP (data_at sh (Tstruct _state noattr)
           (outp, (Vint (Int.repr outlen), (Vint (Int.repr (Zlength out + i)), (inp,
            (Vint (Int.repr (Zlength bytes)), (Vint (Int.repr (incnt + 4 + i)), (Vint (Int.repr 0),
             (Vint (Int.repr 0), Vint (Int.repr 0))))))))) s;
           data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
           data_at sho (tarray tuchar outlen) (map Vint (map Int.repr ((out ++ sublist (incnt + 4) (incnt + 4 + i) bytes))) ++ Zrepeat Vundef (outlen - Zlength ((out ++ sublist (incnt + 4) (incnt + 4 + i) bytes)))) outp))%assert
    break: (PROP ()
      LOCAL (temp _s s)
      SEP (data_at sh (Tstruct _state noattr)
           (outp, (Vint (Int.repr outlen), (Vint (Int.repr (Zlength out + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes))), (inp,
            (Vint (Int.repr (Zlength bytes)), (Vint (Int.repr (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes))), (Vint (Int.repr 0),
             (Vint (Int.repr 0), Vint (Int.repr 0))))))))) s;
           data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
           data_at sho (tarray tuchar outlen) (map Vint (map Int.repr (out ++ (sublist (incnt + 4) (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) bytes))) ++ Zrepeat Vundef (outlen - Zlength (out ++ (sublist (incnt + 4) (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) bytes)))) outp))%assert.
    { Exists 0. rewrite !Z.add_0_r, Z.sub_0_r, sublist_nil, app_nil_r. entailer!. }
    { Intros i. fw. fw.
      forward_if.
      { assert (Hi : i + 1 <= Znth incnt bytes + 256 * Znth (incnt + 1) bytes) by lia.
        assert (Hy := byte_range bytes Hbytes (incnt + 4 + i) ltac:(lia)).
        fw. fw. fw. fw. fw. fw. fw.
        fw.
        rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; lia).
        Exists (i + 1).
        rewrite copy_upd by lia.
        rewrite !add_repr, sub_repr.
        replace (Zlength out + i + 1) with (Zlength out + (i + 1)) by lia.
        replace (incnt + 4 + i + 1) with (incnt + 4 + (i + 1)) by lia.
        replace ((Znth incnt bytes + 256 * Znth (incnt + 1) bytes) - i - 1) with ((Znth incnt bytes + 256 * Znth (incnt + 1) bytes) - (i + 1)) by lia.
        entailer!. }
      { forward.
        match goal with Hx : Int.repr _ = Int.zero |- _ =>
          apply repr_inj_unsigned in Hx; [|rep_lia|rep_lia] end.
        assert (Hi : i = Znth incnt bytes + 256 * Znth (incnt + 1) bytes) by lia.
        subst i. entailer!. } }
    unfold outbuf. entailer!.
    unfold fits. rewrite Zlength_app, Hbs. apply Z.leb_le. lia. }
  { (* NIL: count only *)
    destruct wr; [subst outp; contradiction|].
    fw. fw. fw. fw. }
  Intros.
  match goal with Hx : fits _ _ _ = true |- _ => rename Hx into Hfits end.
  forward.
  assert (Hok : out_ok wr outlen (out ++ (sublist (incnt + 4) (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) bytes)) /\ room wr bytes (out ++ (sublist (incnt + 4) (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) bytes)) (8 * (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)))).
  { destruct wr.
    - split; [|left; reflexivity].
      apply stored_out_ok; auto.
      unfold fits in Hfits. apply Z.leb_le in Hfits. specialize (Hpos eq_refl). lia.
    - destruct (stored_room bytes out (8 * incnt - bitcnt) incnt (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) as [Hr Hl];
        [assumption | lia | lia | lia | lia |].
      split; [|exact Hr]. apply stored_out_ok; auto. }
  destruct Hok as [Hok Hroom].
  assert (Hbuf' : buf_ok bytes (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) 0 0) by (apply buf_ok_aligned; auto; lia).
  Exists 0 (out ++ (sublist (incnt + 4) (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) bytes)) (incnt + 4 + (Znth incnt bytes + 256 * Znth (incnt + 1) bytes)) 0 0 0.
  unfold state_rep. rewrite Zlength_app, Hbs.
  entailer!.
  rewrite Hst. cbv beta iota. rewrite Hfits.
  repeat match goal with |- _ /\ _ => split end; try assumption; auto; try lia.
Qed.
