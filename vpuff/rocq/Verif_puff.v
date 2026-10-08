(* puff() meets puff_spec (Spec_puff.v): it returns 0 exactly when the spec's
   inflateZ decodes the input with the zlib flag on and the output fits.
   The loop invariant is that the spec's blocks from the current bit position
   and output give the spec's result for the whole input (PuffLemmas.v). *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model VPuff.Spec_puff VPuff.PuffLemmas.
Require VPuff.Inflate.
Open Scope Z_scope.
Import ListNotations.

(* fold the struct back into state_rep after reading a field *)
Lemma PuffL_state_fold sh s o ol oc i il ic bb bc e :
  data_at sh (Tstruct _state noattr)
    (o, (Vint (Int.repr ol), (Vint (Int.repr oc), (i, (Vint (Int.repr il),
      (Vint (Int.repr ic), (Vint (Int.repr bb), (Vint (Int.repr bc), Vint (Int.repr e))))))))) s =
  state_rep sh s o ol oc i il ic bb bc e.
Proof. reflexivity. Qed.

Ltac PuffL_fold := rewrite !PuffL_state_fold.

(* stored()'s postcondition as a block result *)
Lemma PuffL_stored_post wr outlen bytes p q out r out' incnt' bitbuf' bitcnt' eof' :
  q = p + 3 ->
  match storedZ bytes q with
  | Some (bs, q) =>
      if fits wr outlen (out ++ bs)
      then r = 0 /\ out' = out ++ bs /\ (8 * incnt' - bitcnt' = q)%Z /\
           buf_ok bytes incnt' bitbuf' bitcnt' /\ eof' = 0 /\ room wr bytes out' q
      else r <> 0
  | None => r <> 0
  end ->
  block_ok wr outlen (PuffL_res bytes (p + 3) 0 out) r out' bytes incnt' bitbuf' bitcnt' eof'.
Proof.
  intros ->. rewrite PuffL_res_stored. unfold block_ok.
  destruct (storedZ bytes (p + 3)) as [[bs q]|]; auto.
Qed.

(* a zero return: the block succeeded and its output fits *)
Lemma PuffL_ok_r wr outlen res r out' bytes incnt' bitbuf' bitcnt' eof' :
  Int.min_signed <= r <= Int.max_signed ->
  block_ok wr outlen res r out' bytes incnt' bitbuf' bitcnt' eof' -> Int.repr r = Int.zero ->
  exists q, res = Some (out', q) /\ r = 0 /\ (8 * incnt' - bitcnt' = q)%Z /\
    buf_ok bytes incnt' bitbuf' bitcnt' /\ eof' = 0 /\ room wr bytes out' q.
Proof.
  intros Hr Hb Hz. assert (r = 0) by (apply repr_inj_signed; [rep_lia | rep_lia | exact Hz]).
  revert Hb. unfold block_ok. destruct res as [[o q]|]; [|contradiction].
  destruct (fits wr outlen o); [|contradiction].
  intros (-> & -> & Hq). exists q. auto.
Qed.

Lemma PuffL_getbits bytes p n :
  VPuff.Inflate.getbitsZ bytes p n =
    if p + n <=? nbits bytes then Some (lsbZ bytes p (Z.to_nat n)) else None.
Proof. reflexivity. Qed.

Ltac PuffL_absurd :=
  exfalso;
  match goal with
  | H1 : ?a <> ?b, H2 : ?a = ?b |- _ => exact (H1 H2)
  | H : ?x <> ?x |- _ => apply H; reflexivity
  | H : Int.repr _ <> Int.zero |- _ => apply H; reflexivity
  | H : Int.repr ?n = Int.zero |- _ =>
      match n with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate H
  end.

Lemma body_puff : semax_body Vprog Gprog f_puff puff_spec.
Proof.
  start_function.
  match goal with H : sizes_ok _ _ _ _ |- _ => rename H into Hsz end.
  match goal with H : bytes_ok _ |- _ => rename H into Hbytes end.
  assert (Hlen : Zlength bytes <= Int.max_signed) by (unfold sizes_ok in Hsz; rep_lia).
  forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
  forward.
  forward_loop
    (EX out : list Z, EX incnt : Z, EX bitbuf : Z, EX bitcnt : Z,
     PROP (buf_ok bytes incnt bitbuf bitcnt; out_ok wr outlen out;
           room wr bytes out (8 * incnt - bitcnt);
           VPuff.Inflate.blocksF bytes (8 * incnt - bitcnt) out true = inflateZ bytes)
     LOCAL (lvar _s (Tstruct _state noattr) v_s; gvars gv; temp _dest dest; temp _destlen destlen;
            temp _source source; temp _sourcelen sourcelen)
     SEP (state_rep Tsh v_s dest outlen (Zlength out) source (Zlength bytes) incnt bitbuf bitcnt 0;
          data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) source;
          outbuf wr sho dest outlen out;
          data_at shd tuint (Vint (Int.repr outlen)) destlen;
          data_at shs tuint (Vint (Int.repr (Zlength bytes))) sourcelen;
          all_tables gv))
  continue:
    (EX out : list Z, EX incnt : Z, EX bitbuf : Z, EX bitcnt : Z, EX l : Z,
     PROP (buf_ok bytes incnt bitbuf bitcnt; out_ok wr outlen out;
           room wr bytes out (8 * incnt - bitcnt); l = 0 \/ l = 1;
           if l =? 1 then inflateZ bytes = Some (out, 8 * incnt - bitcnt, true)
           else VPuff.Inflate.blocksF bytes (8 * incnt - bitcnt) out true = inflateZ bytes)
     LOCAL (temp _last (Vint (Int.repr l)); temp _err (Vint (Int.repr 0));
            lvar _s (Tstruct _state noattr) v_s; gvars gv; temp _dest dest; temp _destlen destlen;
            temp _source source; temp _sourcelen sourcelen)
     SEP (state_rep Tsh v_s dest outlen (Zlength out) source (Zlength bytes) incnt bitbuf bitcnt 0;
          data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) source;
          outbuf wr sho dest outlen out;
          data_at shd tuint (Vint (Int.repr outlen)) destlen;
          data_at shs tuint (Vint (Int.repr (Zlength bytes))) sourcelen;
          all_tables gv))
  break:
    (EX out : list Z, EX incnt : Z, EX bitbuf : Z, EX bitcnt : Z, EX eofv : Z, EX errz : Z,
     PROPx [Int.min_signed <= errz <= Int.max_signed; out_ok wr outlen out;
           if Int.eq (Int.repr eofv) Int.zero
           then (errz = 0 /\ inflateZ bytes = Some (out, 8 * incnt - bitcnt, true) /\
                 buf_ok bytes incnt bitbuf bitcnt) \/
                (Int.repr errz <> Int.zero /\ notok wr outlen bytes)
           else notok wr outlen bytes]
     (LOCALx ((if Int.eq (Int.repr eofv) Int.zero then [temp _err (Vint (Int.repr errz))] else []) ++
             [lvar _s (Tstruct _state noattr) v_s; gvars gv; temp _dest dest; temp _destlen destlen;
              temp _source source; temp _sourcelen sourcelen])
     (SEPx [state_rep Tsh v_s dest outlen (Zlength out) source (Zlength bytes) incnt bitbuf bitcnt eofv;
          data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) source;
          outbuf wr sho dest outlen out;
          data_at shd tuint (Vint (Int.repr outlen)) destlen;
          data_at shs tuint (Vint (Int.repr (Zlength bytes))) sourcelen;
          all_tables gv]))).
  - (* entry *)
    Exists (@nil Z) 0 0 0. unfold state_rep. entailer!.
    + split; [|split].
      * unfold buf_ok. pose proof (Zlength_nonneg bytes). repeat split; simpl; lia.
      * unfold out_ok, bytes_ok, fits. rewrite Zlength_nil. unfold sizes_ok in Hsz.
        destruct wr; repeat split; try constructor; try lia; apply Z.leb_le; lia.
      * replace (8 * 0) with 0 by lia. apply (PuffL_room0 wr dest bytes outlen Hsz).
    + unfold outbuf. destruct wr; [|cancel].
      rewrite Zlength_nil, Z.sub_0_r. simpl app.
      change (Zrepeat Vundef outlen) with (default_val (tarray tuchar outlen)).
      unfold data_at_, data_at, field_at_. apply derives_refl.
  - (* the body *)
    Intros out incnt bitbuf bitcnt.
    match goal with H : buf_ok _ _ _ _ |- _ => rename H into Hbuf end.
    match goal with H : out_ok _ _ _ |- _ => rename H into Hout end.
    match goal with H : room _ _ _ _ |- _ => rename H into Hroom end.
    match goal with H : VPuff.Inflate.blocksF _ _ _ _ = _ |- _ => rename H into Hinv end.
    pose proof (PuffL_buf_pos _ _ _ _ Hbuf) as Hp.
    (* last = bits(&s, 1) *)
    forward_call (Tsh, shi, v_s, dest, outlen, Zlength out, source, bytes, incnt, bitbuf, bitcnt, 1).
    Intros vret. destruct vret as [[[[r1 incnt1] bitbuf1] bitcnt1] eof1]. cbn [fst snd] in *.
    match goal with H : context [8 * incnt - bitcnt + 1 <=? _] |- _ => rename H into Hb1 end.
    change (Z.to_nat 1) with 1%nat in Hb1.
    destruct (8 * incnt - bitcnt + 1 <=? nbits bytes) eqn:E1.
    2: { destruct Hb1 as [-> ->]. unfold state_rep. forward. forward_if; [|PuffL_absurd]. forward.
         Exists out incnt1 bitbuf1 bitcnt1 1 0.
         change (Int.eq (Int.repr 1) Int.zero) with false. simpl app. unfold state_rep. entailer!.
         eapply PuffL_bad_header; [exact Hinv|]. left. rewrite PuffL_getbits, E1. reflexivity. }
    destruct Hb1 as (-> & Hpos1 & Hbuf1 & ->).
    pose proof (PuffL_lsb1 bytes (8 * incnt - bitcnt)) as Hl.
    assert (Hg1 : VPuff.Inflate.getbitsZ bytes (8 * incnt - bitcnt) 1 =
                  Some (lsbZ bytes (8 * incnt - bitcnt) 1)) by (rewrite PuffL_getbits, E1; reflexivity).
    remember (lsbZ bytes (8 * incnt - bitcnt) 1) as l eqn:El. clear El.
    unfold state_rep. forward. forward_if; [PuffL_absurd|]. PuffL_fold.
    (* type = bits(&s, 2) *)
    forward_call (Tsh, shi, v_s, dest, outlen, Zlength out, source, bytes, incnt1, bitbuf1, bitcnt1, 2).
    Intros vret. destruct vret as [[[[r2 incnt2] bitbuf2] bitcnt2] eof2]. cbn [fst snd] in *.
    match goal with H : context [8 * incnt1 - bitcnt1 + 2 <=? _] |- _ => rename H into Hb2 end.
    change (Z.to_nat 2) with 2%nat in Hb2.
    destruct (8 * incnt1 - bitcnt1 + 2 <=? nbits bytes) eqn:E2.
    2: { destruct Hb2 as [-> ->]. unfold state_rep. forward. forward_if; [|PuffL_absurd]. forward.
         Exists out incnt2 bitbuf2 bitcnt2 1 0.
         change (Int.eq (Int.repr 1) Int.zero) with false. simpl app. unfold state_rep. entailer!.
         eapply PuffL_bad_header; [exact Hinv|]. right. eexists; split; [exact Hg1|].
         rewrite PuffL_getbits. replace (8 * incnt - bitcnt + 1 + 2) with (8 * incnt1 - bitcnt1 + 2) by lia.
         rewrite E2. reflexivity. }
    destruct Hb2 as (-> & Hpos2 & Hbuf2 & ->).
    pose proof (PuffL_lsb2 bytes (8 * incnt1 - bitcnt1)) as Ht.
    assert (Hg2 : VPuff.Inflate.getbitsZ bytes (8 * incnt - bitcnt + 1) 2 =
                  Some (lsbZ bytes (8 * incnt1 - bitcnt1) 2)).
    { rewrite PuffL_getbits. replace (8 * incnt - bitcnt + 1 + 2) with (8 * incnt1 - bitcnt1 + 2) by lia.
      rewrite E2. rewrite Hpos1. reflexivity. }
    remember (lsbZ bytes (8 * incnt1 - bitcnt1) 2) as t eqn:Et. clear Et.
    assert (Hroom2 : room wr bytes out (8 * incnt2 - bitcnt2)) by (eapply PuffL_room_le; [|exact Hroom]; lia).
    unfold state_rep. forward. forward_if; [PuffL_absurd|]. PuffL_fold.
    (* err = stored/fixed/dynamic/-1 *)
    forward_if (EX r : Z, EX out' : list Z, EX incnt' : Z, EX bitbuf' : Z, EX bitcnt' : Z, EX eof' : Z,
      PROP (Int.min_signed <= r <= Int.max_signed; out_ok wr outlen out';
            block_ok wr outlen (PuffL_res bytes (8 * incnt - bitcnt + 3) t out) r out' bytes
              incnt' bitbuf' bitcnt' eof')
      LOCAL (temp _t'3 (Vint (Int.repr r)); temp _last (Vint (Int.repr l));
             lvar _s (Tstruct _state noattr) v_s; gvars gv; temp _dest dest; temp _destlen destlen;
             temp _source source; temp _sourcelen sourcelen)
      SEP (state_rep Tsh v_s dest outlen (Zlength out') source (Zlength bytes) incnt' bitbuf' bitcnt' eof';
           data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) source;
           outbuf wr sho dest outlen out';
           data_at shd tuint (Vint (Int.repr outlen)) destlen;
           data_at shs tuint (Vint (Int.repr (Zlength bytes))) sourcelen;
           all_tables gv)).
    + (* stored *)
      subst t.
      forward_call (Tsh, shi, sho, v_s, dest, outlen, out, wr, source, bytes, incnt2, bitbuf2, bitcnt2).
      Intros vret. destruct vret as [[[[[r out'] incnt'] bitbuf'] bitcnt'] eof']. cbn [fst snd] in *.
      forward.
      Exists r out' incnt' bitbuf' bitcnt' eof'. entailer!.
      eapply PuffL_stored_post; [|eassumption]. lia.
    + forward_if.
      * (* fixed *)
        subst t. unfold all_tables. Intros.
        forward_call (Tsh, shi, sho, v_s, dest, outlen, out, wr, source, bytes, incnt2, bitbuf2, bitcnt2, gv).
        Intros vret. destruct vret as [[[[[r out'] incnt'] bitbuf'] bitcnt'] eof']. cbn [fst snd] in *.
        forward.
        Exists r out' incnt' bitbuf' bitcnt' eof'. unfold all_tables. entailer!.
        rewrite PuffL_res_fixed. replace (8 * incnt - bitcnt + 3) with (8 * incnt2 - bitcnt2) by lia.
        assumption.
      * forward_if.
        -- (* dynamic *)
          subst t.
          forward_call (Tsh, shi, sho, v_s, dest, outlen, out, wr, source, bytes, incnt2, bitbuf2, bitcnt2, gv).
          Intros vret. destruct vret as [[[[[r out'] incnt'] bitbuf'] bitcnt'] eof']. cbn [fst snd] in *.
          forward. forward.
          Exists r out' incnt' bitbuf' bitcnt' eof'. entailer!.
          rewrite PuffL_res_dynamic. replace (8 * incnt - bitcnt + 3) with (8 * incnt2 - bitcnt2) by lia.
          assumption.
        -- (* type 3 *)
          forward. forward. forward.
          Exists (-1) out incnt2 bitbuf2 bitcnt2 0. entailer!.
          rewrite PuffL_res_bad by assumption. unfold block_ok.
          lia.
    + Intros r out' incnt' bitbuf' bitcnt' eof'.
      match goal with H : block_ok _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hblk end.
      match goal with H : out_ok _ _ out' |- _ => rename H into Hout' end.
      forward.
      forward_if.
      * (* err != 0: break *)
        forward.
        assert (Hrz : Int.repr r <> Int.zero).
        { first [assumption | intro Hz; apply repr_inj_signed in Hz; [|rep_lia|rep_lia]; subst; contradiction]. }
        assert (Hnot : notok wr outlen bytes).
        { eapply PuffL_fail; [ | exact Hinv | exact Hg1 | exact Hg2 | eapply PuffL_fail_r; eassumption]. lia. }
        Exists out' incnt' bitbuf' bitcnt' eof' r.
        destruct (Int.eq (Int.repr eof') Int.zero); simpl app; entailer!.
      * (* err == 0 *)
        assert (Hrz : Int.repr r = Int.zero).
        { first [assumption | match goal with H : r = 0 |- _ => rewrite H; reflexivity end]. }
        destruct (PuffL_ok_r _ _ _ r _ _ _ _ _ _ ltac:(assumption) Hblk Hrz)
          as (q & Hres & -> & Hq & Hbuf' & -> & Hroom').
        forward.
        pose proof (PuffL_buf_pos _ _ _ _ Hbuf') as Hq'.
        Exists out' incnt' bitbuf' bitcnt' l. entailer!.
        eapply PuffL_ok; [ | | exact Hinv | exact Hg1 | exact Hg2 | exact Hres]; lia.
  - (* while (!last) *)
    Intros out incnt bitbuf bitcnt l.
    match goal with H : l = 0 \/ l = 1 |- _ => destruct H as [-> | ->] end.
    + forward_if; [|PuffL_absurd]. forward. Exists out incnt bitbuf bitcnt. entailer!.
    + forward_if; [PuffL_absurd|]. forward.
      Exists out incnt bitbuf bitcnt 0 0.
      change (Int.eq (Int.repr 0) Int.zero) with true. simpl app. entailer!.
  - (* after the loop *)
    Intros out incnt bitbuf bitcnt eofv errz.
    match goal with H : out_ok _ _ _ |- _ => rename H into Hout end.
    match goal with H : if Int.eq _ _ then _ else _ |- _ => rename H into Hcase end.
    destruct (Int.eq (Int.repr eofv) Int.zero) eqn:Eeof; simpl app.
    + pose proof (Int.eq_spec (Int.repr eofv) Int.zero) as Heof. rewrite Eeof in Heof.
      unfold state_rep. rewrite Heof. forward.
      forward_if True; [PuffL_absurd | forward; entailer! |]. Intros.
      destruct Hcase as [(-> & Hinfl & Hbuf) | (Hne & Hnot)].
      * forward_if (PROP ()
          LOCAL (temp _err (Vint (Int.repr 0)); lvar _s (Tstruct _state noattr) v_s; gvars gv;
                 temp _dest dest; temp _destlen destlen; temp _source source; temp _sourcelen sourcelen)
          SEP (state_rep Tsh v_s dest outlen (Zlength out) source (Zlength bytes) incnt bitbuf bitcnt 0;
               data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) source;
               outbuf wr sho dest outlen out;
               data_at shd tuint (Vint (Int.repr (Zlength out))) destlen;
               data_at shs tuint (Vint (Int.repr incnt)) sourcelen;
               all_tables gv)).
        { forward. forward. forward. forward. unfold state_rep. entailer!. }
        { match goal with H : true = false |- _ => discriminate H end. }
        forward.
        Exists 0 (Zlength out) incnt (map Vint (map Int.repr out) ++ Zrepeat Vundef (outlen - Zlength out)).
        unfold outbuf. destruct wr; entailer!.
        all: try (unfold state_rep; apply data_at_data_at_).
        all: destruct Hout as (_ & Hf & _); destruct Hbuf as (_ & Hb & _);
             apply (PuffL_ok_post _ outlen bytes out incnt bitcnt); auto.
      * forward_if (EX dl : Z, EX sl : Z, PROP ()
          LOCAL (temp _err (Vint (Int.repr errz)); lvar _s (Tstruct _state noattr) v_s; gvars gv;
                 temp _dest dest; temp _destlen destlen; temp _source source; temp _sourcelen sourcelen)
          SEP (state_rep Tsh v_s dest outlen (Zlength out) source (Zlength bytes) incnt bitbuf bitcnt 0;
               data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) source;
               outbuf wr sho dest outlen out;
               data_at shd tuint (Vint (Int.repr dl)) destlen;
               data_at shs tuint (Vint (Int.repr sl)) sourcelen;
               all_tables gv)).
        { forward. forward. forward. forward. Exists (Zlength out) incnt. unfold state_rep. entailer!. }
        { forward. Exists outlen (Zlength bytes). unfold state_rep. entailer!. }
        Intros dl sl. forward.
        Exists errz dl sl (map Vint (map Int.repr out) ++ Zrepeat Vundef (outlen - Zlength out)).
        assert (errz <> 0) by (intro; subst; apply Hne; reflexivity).
        unfold outbuf. destruct wr; entailer!.
        all: try (unfold state_rep; apply data_at_data_at_).
        all: apply PuffL_notok_post; auto.
    + assert (Heof : Int.repr eofv <> Int.zero).
      { pose proof (Int.eq_spec (Int.repr eofv) Int.zero) as Heof. rewrite Eeof in Heof. exact Heof. }
      unfold state_rep. forward.
      forward_if (PROP ()
          LOCAL (temp _err (Vint (Int.repr 2)); lvar _s (Tstruct _state noattr) v_s; gvars gv;
                 temp _dest dest; temp _destlen destlen; temp _source source; temp _sourcelen sourcelen)
          SEP (state_rep Tsh v_s dest outlen (Zlength out) source (Zlength bytes) incnt bitbuf bitcnt eofv;
               data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) source;
               outbuf wr sho dest outlen out;
               data_at shd tuint (Vint (Int.repr outlen)) destlen;
               data_at shs tuint (Vint (Int.repr (Zlength bytes))) sourcelen;
               all_tables gv)).
      { forward. unfold state_rep. entailer!. }
      { PuffL_absurd. }
      forward_if True.
      { match goal with H : false = true |- _ => discriminate H end. }
      { forward. entailer!. }
      Intros. forward.
      Exists 2 outlen (Zlength bytes) (map Vint (map Int.repr out) ++ Zrepeat Vundef (outlen - Zlength out)).
      unfold outbuf. destruct wr; entailer!.
      all: try (unfold state_rep; apply data_at_data_at_).
      all: apply PuffL_notok_post; auto; lia.
Qed.
