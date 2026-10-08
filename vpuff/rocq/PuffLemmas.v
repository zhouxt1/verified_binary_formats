(* Facts about the mirror of the spec's blocks (Inflate.v) that the proof of
   puff() (Verif_puff.v) uses: positions advance, blocksF unfolds one block, a
   block outside zlib keeps the stream outside zlib, and outputs only grow. *)
Require Import VST.floyd.proofauto.
Require Import VPuff.Model VPuff.Spec_puff.
Require VPuff.Inflate VPuff.InflateFacts.
Close Scope Nat_scope.
Open Scope Z_scope.
Import ListNotations.

Section Puff.
Import VPuff.Inflate.

(** * Bits *)

Lemma PuffL_lsb_nonneg bytes p n : 0 <= lsbZ bytes p n.
Proof.
  revert p; induction n; intros p; cbn [lsbZ]; [lia|].
  specialize (IHn (p + 1)). destruct (bitZ bytes p); lia.
Qed.

Lemma PuffL_getbits_nonneg bytes p n v : getbitsZ bytes p n = Some v -> 0 <= v.
Proof.
  unfold getbitsZ. destruct (_ <=? _); intros H; inversion H; apply PuffL_lsb_nonneg.
Qed.

Lemma PuffL_decode_pos lens bytes p s p1 :
  0 <= p -> lean_decode lens bytes p = Some (s, p1) -> p < p1 <= nbits bytes.
Proof.
  intros Hp H. destruct (VPuff.InflateFacts.lean_decode_bounds lens bytes p s p1 Hp H). lia.
Qed.

(** * Positions advance *)

Lemma PuffL_stored_pos bytes p bs q : 0 <= p -> storedZ bytes p = Some (bs, q) -> p < q.
Proof.
  intros Hp. unfold storedZ.
  assert (Hq0 : p <= (p + 7) / 8 * 8).
  { pose proof (Z.div_mod (p + 7) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(lia)). lia. }
  remember ((p + 7) / 8 * 8) as q0 eqn:Eq0. clear Eq0.
  destruct (getbitsZ bytes q0 16) as [len|] eqn:E1; [|discriminate].
  destruct (getbitsZ bytes (q0 + 16) 16) as [nlen|]; [|discriminate].
  destruct (andb _ _); [|discriminate].
  apply PuffL_getbits_nonneg in E1.
  intros H; injection H; intros; lia.
Qed.

Lemma PuffL_syms_pos lit dist bytes : forall f p out o q,
  0 <= p -> symsZ lit dist bytes f p out = Some (o, q) -> p < q.
Proof.
  induction f as [|f IH]; intros p out o q Hp H; cbn [symsZ] in H; [discriminate|].
  destruct (lean_decode lit bytes p) as [[s p1]|] eqn:Ed; [|discriminate].
  apply PuffL_decode_pos in Ed; [|lia].
  destruct (s <? 256).
  - destruct (andb (p <? p1) (p1 <=? nbits bytes)); [|discriminate].
    apply IH in H; lia.
  - destruct (s =? 256).
    + inversion H; subst; lia.
    + destruct (s - 257 <? 29); [|discriminate].
      destruct (getbitsZ bytes p1 (lenExtraZ (s - 257))) as [e|]; [|discriminate].
      destruct (lean_decode dist bytes (p1 + lenExtraZ (s - 257))) as [[ds p3]|]; [|discriminate].
      destruct (ds <? 30); [|discriminate].
      destruct (getbitsZ bytes p3 (distExtraZ ds)) as [e2|]; [|discriminate].
      destruct (distBaseZ ds + e2 <=? Zlength out); [|discriminate].
      destruct (andb (p <? p3 + distExtraZ ds) (p3 + distExtraZ ds <=? nbits bytes)) eqn:Eg;
        [|discriminate].
      apply andb_prop in Eg as [Eg _]. apply Z.ltb_lt in Eg.
      apply IH in H; lia.
Qed.

Lemma PuffL_symsF_pos lit dist bytes p out o q :
  0 <= p -> symsF lit dist bytes p out = Some (o, q) -> p < q.
Proof. apply PuffL_syms_pos. Qed.

Lemma PuffL_readCL_pos bytes p hclen : forall f i acc l r,
  readCLgo bytes p hclen f i acc = Some (l, r) -> r = p + 3 * hclen.
Proof.
  induction f as [|f IH]; intros i acc l r H; cbn [readCLgo] in H; [discriminate|].
  destruct (i <? hclen).
  - destruct (getbitsZ bytes (p + 3 * i) 3); [|discriminate]. eapply IH; eauto.
  - inversion H; auto.
Qed.

Lemma PuffL_readLens_pos cl bytes total : forall f p acc l r,
  0 <= p -> readLensZ cl bytes f p total acc = Some (l, r) -> p <= r.
Proof.
  induction f as [|f IH]; intros p acc l r Hp H; cbn [readLensZ] in H; [discriminate|].
  destruct (total <=? Zlength acc).
  { inversion H; lia. }
  destruct (lean_decode cl bytes p) as [[s p1]|] eqn:Ed; [|discriminate].
  apply PuffL_decode_pos in Ed; [|lia].
  destruct (s <? 16).
  - apply IH in H; lia.
  - destruct (getbitsZ bytes p1 _); [|discriminate].
    destruct (if s =? 16 then lastZ acc else Some 0); [|discriminate].
    destruct (_ <=? total); [|discriminate].
    apply IH in H; [|destruct (s =? 16); [|destruct (s =? 17)]; lia].
    destruct (s =? 16); [|destruct (s =? 17)]; lia.
Qed.

Lemma PuffL_dyn_pos bytes p lit dist q z :
  0 <= p -> dynHeaderZ bytes p = Some (lit, dist, q, z) -> p < q.
Proof.
  intros Hp. unfold dynHeaderZ.
  destruct (getbitsZ bytes p 5) as [hlit|]; [|discriminate].
  destruct (getbitsZ bytes (p + 5) 5) as [hdist|]; [|discriminate].
  destruct (getbitsZ bytes (p + 10) 4) as [hclen|] eqn:Ec; [|discriminate].
  apply PuffL_getbits_nonneg in Ec.
  destruct (hlit + 257 <=? 286); [|discriminate].
  destruct (readCLZ bytes (p + 14) (hclen + 4)) as [[cl q0]|] eqn:Ecl; [|discriminate].
  unfold readCLZ in Ecl. apply PuffL_readCL_pos in Ecl.
  destruct (notOversubZ cl); [|discriminate].
  destruct (readLensZ cl bytes _ q0 _ []) as [[lens r]|] eqn:El; [|discriminate].
  apply PuffL_readLens_pos in El; [|lia].
  destruct (andb _ _); [|discriminate].
  intros H; inversion H; subst. lia.
Qed.

Lemma PuffL_block_pos bytes p t out o q z :
  0 <= p -> blockZ bytes p t out = Some (o, q, z) -> p < q.
Proof.
  intros Hp. unfold blockZ.
  destruct (t =? 0).
  { destruct (storedZ bytes p) as [[bs q0]|] eqn:E; [|discriminate].
    intros H; inversion H; subst. eapply PuffL_stored_pos; eauto. }
  destruct (t =? 1).
  { destruct (symsF fixedLitZ fixedDistZ bytes p out) as [[o0 q0]|] eqn:E; [|discriminate].
    intros H; inversion H; subst. eapply PuffL_symsF_pos; eauto. }
  destruct (t =? 2); [|discriminate].
  destruct (dynHeaderZ bytes p) as [[[[lit dist] qh] zh]|] eqn:Eh; [|discriminate].
  destruct (symsF lit dist bytes qh out) as [[o0 r]|] eqn:Es; [|discriminate].
  intros H; inversion H; subst.
  apply PuffL_dyn_pos in Eh; auto.
  apply PuffL_symsF_pos in Es; lia.
Qed.

(** * Outputs only grow *)

Lemma PuffL_lzCopy_len out d n : Zlength (lzCopyZ out d n) = Zlength out + Z.of_nat n.
Proof.
  revert out; induction n; intros out; cbn [lzCopyZ]; [lia|].
  rewrite IHn, Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma PuffL_syms_len lit dist bytes : forall f p out o q,
  symsZ lit dist bytes f p out = Some (o, q) -> Zlength out <= Zlength o.
Proof.
  induction f as [|f IH]; intros p out o q H; cbn [symsZ] in H; [discriminate|].
  destruct (lean_decode lit bytes p) as [[s p1]|]; [|discriminate].
  destruct (s <? 256).
  - destruct (andb _ _); [|discriminate].
    apply IH in H. rewrite Zlength_app in H. list_solve.
  - destruct (s =? 256).
    + inversion H; subst; lia.
    + destruct (s - 257 <? 29); [|discriminate].
      destruct (getbitsZ _ _ _); [|discriminate].
      destruct (lean_decode dist _ _) as [[ds p3]|]; [|discriminate].
      destruct (ds <? 30); [|discriminate].
      destruct (getbitsZ _ _ _); [|discriminate].
      destruct (_ <=? Zlength out); [|discriminate].
      destruct (andb _ _); [|discriminate].
      apply IH in H. rewrite PuffL_lzCopy_len in H. lia.
Qed.

Lemma PuffL_block_len bytes p t out o q z :
  blockZ bytes p t out = Some (o, q, z) -> Zlength out <= Zlength o.
Proof.
  unfold blockZ.
  destruct (t =? 0).
  { destruct (storedZ bytes p) as [[bs q0]|]; [|discriminate].
    intros H; inversion H; subst. rewrite Zlength_app. list_solve. }
  destruct (t =? 1).
  { destruct (symsF _ _ bytes p out) as [[o0 q0]|] eqn:E; [|discriminate].
    intros H; inversion H; subst. eapply PuffL_syms_len; eauto. }
  destruct (t =? 2); [|discriminate].
  destruct (dynHeaderZ bytes p) as [[[[lit dist] qh] zh]|]; [|discriminate].
  destruct (symsF lit dist bytes qh out) as [[o0 r]|] eqn:Es; [|discriminate].
  intros H; inversion H; subst. eapply PuffL_syms_len; eauto.
Qed.

Lemma PuffL_blocks_len bytes : forall f p out zl o q z,
  blocksZ bytes f p out zl = Some (o, q, z) -> Zlength out <= Zlength o.
Proof.
  induction f as [|f IH]; intros p out zl o q z H; cbn [blocksZ] in H; [discriminate|].
  destruct (getbitsZ bytes p 1) as [bf|]; [|discriminate].
  destruct (getbitsZ bytes (p + 1) 2) as [bt|]; [|discriminate].
  destruct (blockZ bytes (p + 3) bt out) as [[[o1 q1] z1]|] eqn:Eb; [|discriminate].
  apply PuffL_block_len in Eb.
  destruct (bf =? 1).
  - inversion H; subst; lia.
  - destruct (andb _ _); [|discriminate]. apply IH in H; lia.
Qed.

(** * The zlib flag stays off *)

Lemma PuffL_blocks_false bytes : forall f p out o q z,
  blocksZ bytes f p out false = Some (o, q, z) -> z = false.
Proof.
  induction f as [|f IH]; intros p out o q z H; cbn [blocksZ] in H; [discriminate|].
  destruct (getbitsZ bytes p 1) as [bf|]; [|discriminate].
  destruct (getbitsZ bytes (p + 1) 2) as [bt|]; [|discriminate].
  destruct (blockZ bytes (p + 3) bt out) as [[[o1 q1] z1]|]; [|discriminate].
  destruct (bf =? 1).
  - inversion H; auto.
  - destruct (andb _ _); [|discriminate]. eapply IH; eauto.
Qed.

(** * Fuel *)

Lemma PuffL_blocks_fuel bytes : forall f1 f2 p out zl,
  (Z.to_nat (nbits bytes - p) < f1)%nat -> (Z.to_nat (nbits bytes - p) < f2)%nat ->
  blocksZ bytes f1 p out zl = blocksZ bytes f2 p out zl.
Proof.
  induction f1 as [|f1 IH]; intros f2 p out zl H1 H2; [lia|].
  destruct f2 as [|f2]; [lia|].
  cbn [blocksZ].
  destruct (getbitsZ bytes p 1); [|reflexivity].
  destruct (getbitsZ bytes (p + 1) 2); [|reflexivity].
  destruct (blockZ bytes (p + 3) _ out) as [[[o1 q1] z1]|]; [|reflexivity].
  destruct (_ =? 1); [reflexivity|].
  destruct (andb (p <? q1) (q1 <=? nbits bytes)) eqn:Eg; [|reflexivity].
  apply andb_prop in Eg as [Eg1 Eg2]. apply Z.ltb_lt in Eg1. apply Z.leb_le in Eg2.
  apply IH; lia.
Qed.

Lemma PuffL_blocksF_step bytes p out zl :
  blocksF bytes p out zl =
    match getbitsZ bytes p 1 with
    | None => None
    | Some bfinal =>
      match getbitsZ bytes (p + 1) 2 with
      | None => None
      | Some btype =>
        match blockZ bytes (p + 3) btype out with
        | None => None
        | Some (o, q, z) =>
          if bfinal =? 1 then Some (o, q, andb zl z)
          else if andb (p <? q) (q <=? nbits bytes) then blocksF bytes q o (andb zl z)
          else None
        end
      end
    end.
Proof.
  unfold blocksF. rewrite Nat.add_1_r. cbn [blocksZ].
  destruct (getbitsZ bytes p 1); [|reflexivity].
  destruct (getbitsZ bytes (p + 1) 2); [|reflexivity].
  destruct (blockZ bytes (p + 3) _ out) as [[[o1 q1] z1]|]; [|reflexivity].
  destruct (_ =? 1); [reflexivity|].
  destruct (andb (p <? q1) (q1 <=? nbits bytes)) eqn:Eg; [|reflexivity].
  apply andb_prop in Eg as [Eg1 Eg2]. apply Z.ltb_lt in Eg1. apply Z.leb_le in Eg2.
  apply PuffL_blocks_fuel; lia.
Qed.

End Puff.

(** * What one block does to the stream's result *)

(* the stream's result is not a success that fits *)
Definition notok (wr : bool) (outlen : Z) (bytes : list Z) : Prop :=
  match inflateZ bytes with
  | Some (o, _, true) => fits wr outlen o = false
  | _ => True
  end.

Lemma PuffL_fits_mono wr outlen o o' :
  fits wr outlen o = false -> Zlength o <= Zlength o' -> fits wr outlen o' = false.
Proof.
  unfold fits. destruct wr; [|discriminate].
  intros H1 H2. apply Z.leb_gt in H1. apply Z.leb_gt. lia.
Qed.

(* the block at p + 3 failed: its result is not a zlib-accepted output that fits *)
Lemma PuffL_bad wr outlen bytes p out l t :
  0 <= p ->
  VPuff.Inflate.blocksF bytes p out true = inflateZ bytes ->
  VPuff.Inflate.getbitsZ bytes p 1 = Some l ->
  VPuff.Inflate.getbitsZ bytes (p + 1) 2 = Some t ->
  (forall o q z, VPuff.Inflate.blockZ bytes (p + 3) t out = Some (o, q, z) ->
     z = true -> fits wr outlen o = false) ->
  notok wr outlen bytes.
Proof.
  intros Hp Hinv Hl Ht Hbad. unfold notok. rewrite <- Hinv, PuffL_blocksF_step, Hl, Ht.
  destruct (VPuff.Inflate.blockZ bytes (p + 3) t out) as [[[o q] z]|] eqn:Eb; [|exact I].
  destruct z.
  - specialize (Hbad o q true eq_refl eq_refl).
    destruct (l =? 1); [exact Hbad|].
    destruct (andb _ _); [|exact I].
    unfold VPuff.Inflate.blocksF.
    destruct (VPuff.Inflate.blocksZ _ _ _ _ _) as [[[o' q'] z']|] eqn:E; [|exact I].
    destruct z'; [|exact I].
    apply PuffL_blocks_len in E. eapply PuffL_fits_mono; eauto.
  - destruct (l =? 1); [exact I|].
    destruct (andb _ _); [|exact I].
    unfold VPuff.Inflate.blocksF.
    destruct (VPuff.Inflate.blocksZ _ _ _ _ _) as [[[o' q'] z']|] eqn:E; [|exact I].
    apply PuffL_blocks_false in E. subst. exact I.
Qed.

(* the header ran out of input *)
Lemma PuffL_bad_header wr outlen bytes p out :
  VPuff.Inflate.blocksF bytes p out true = inflateZ bytes ->
  (VPuff.Inflate.getbitsZ bytes p 1 = None \/
   exists l, VPuff.Inflate.getbitsZ bytes p 1 = Some l /\ VPuff.Inflate.getbitsZ bytes (p + 1) 2 = None) ->
  notok wr outlen bytes.
Proof.
  intros Hinv [H | [l [H1 H2]]]; unfold notok; rewrite <- Hinv, PuffL_blocksF_step.
  - rewrite H. exact I.
  - rewrite H1, H2. exact I.
Qed.

(* the block at p + 3 succeeded *)
Lemma PuffL_good bytes p out l t o q :
  0 <= p -> q <= VPuff.Inflate.nbits bytes ->
  VPuff.Inflate.blocksF bytes p out true = inflateZ bytes ->
  VPuff.Inflate.getbitsZ bytes p 1 = Some l ->
  VPuff.Inflate.getbitsZ bytes (p + 1) 2 = Some t ->
  VPuff.Inflate.blockZ bytes (p + 3) t out = Some (o, q, true) ->
  (l = 1 -> inflateZ bytes = Some (o, q, true)) /\
  (l <> 1 -> VPuff.Inflate.blocksF bytes q o true = inflateZ bytes).
Proof.
  intros Hp Hq Hinv Hl Ht Hb.
  assert (Hpq : p + 3 < q) by (eapply PuffL_block_pos; [|exact Hb]; lia).
  rewrite <- Hinv, PuffL_blocksF_step, Hl, Ht, Hb.
  split; intros E.
  - subst. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) E).
    replace (andb (p <? q) (q <=? VPuff.Inflate.nbits bytes)) with true
      by (symmetry; apply andb_true_intro; split; [apply Z.ltb_lt | apply Z.leb_le]; lia).
    reflexivity.
Qed.

(** * What one block call gives puff() *)

(* the block's result when the spec stays in zlib: the C returns 0 exactly then *)
Definition PuffL_res (bytes : list Z) (p t : Z) (out : list Z) : option (list Z * Z) :=
  match VPuff.Inflate.blockZ bytes p t out with
  | Some (o, q, true) => Some (o, q)
  | _ => None
  end.

Lemma PuffL_res_stored bytes p out :
  PuffL_res bytes p 0 out =
    match storedZ bytes p with Some (bs, q) => Some (out ++ bs, q) | None => None end.
Proof.
  unfold PuffL_res, VPuff.Inflate.blockZ. simpl.
  destruct (storedZ bytes p) as [[bs q]|]; reflexivity.
Qed.

Lemma PuffL_res_fixed bytes p out :
  PuffL_res bytes p 1 out = symsF VPuff.Inflate.fixedLitZ VPuff.Inflate.fixedDistZ bytes p out.
Proof.
  unfold PuffL_res, VPuff.Inflate.blockZ. simpl.
  destruct (symsF _ _ _ _ _) as [[o q]|]; reflexivity.
Qed.

Lemma PuffL_res_dynamic bytes p out :
  PuffL_res bytes p 2 out =
    match dynHeaderZ bytes p with
    | Some (lit, dist, q, true) => symsF lit dist bytes q out
    | _ => None
    end.
Proof.
  unfold PuffL_res, VPuff.Inflate.blockZ. simpl.
  destruct (dynHeaderZ bytes p) as [[[[lit dist] q] z]|]; [|reflexivity].
  destruct (symsF _ _ _ _ _) as [[o r]|]; destruct z; reflexivity.
Qed.

Lemma PuffL_res_bad bytes p t out : t <> 0 -> t <> 1 -> t <> 2 -> PuffL_res bytes p t out = None.
Proof.
  intros H0 H1 H2. unfold PuffL_res, VPuff.Inflate.blockZ.
  rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2).
  reflexivity.
Qed.

Lemma PuffL_lsb1 bytes p : lsbZ bytes p 1 = 0 \/ lsbZ bytes p 1 = 1.
Proof. cbn [VPuff.Inflate.lsbZ]. destruct (VPuff.Model.bitZ bytes p); lia. Qed.

Lemma PuffL_lsb2 bytes p : 0 <= lsbZ bytes p 2 < 4.
Proof.
  cbn [VPuff.Inflate.lsbZ].
  destruct (VPuff.Model.bitZ bytes p), (VPuff.Model.bitZ bytes (p + 1)); lia.
Qed.

(* a failed block: the spec fails too, or its output does not fit *)
Lemma PuffL_fail wr outlen bytes p out l t :
  0 <= p ->
  VPuff.Inflate.blocksF bytes p out true = inflateZ bytes ->
  VPuff.Inflate.getbitsZ bytes p 1 = Some l ->
  VPuff.Inflate.getbitsZ bytes (p + 1) 2 = Some t ->
  match PuffL_res bytes (p + 3) t out with
  | Some (o, _) => fits wr outlen o = false
  | None => True
  end ->
  notok wr outlen bytes.
Proof.
  intros Hp Hinv Hl Ht Hr. eapply PuffL_bad; eauto.
  intros o q z Hb Hz. subst z. unfold PuffL_res in Hr. rewrite Hb in Hr. exact Hr.
Qed.

(* a block that succeeded *)
Lemma PuffL_ok bytes p out l t o q :
  0 <= p -> q <= nbits bytes ->
  VPuff.Inflate.blocksF bytes p out true = inflateZ bytes ->
  VPuff.Inflate.getbitsZ bytes p 1 = Some l ->
  VPuff.Inflate.getbitsZ bytes (p + 1) 2 = Some t ->
  PuffL_res bytes (p + 3) t out = Some (o, q) ->
  (if l =? 1 then inflateZ bytes = Some (o, q, true)
   else VPuff.Inflate.blocksF bytes q o true = inflateZ bytes).
Proof.
  intros Hp Hq Hinv Hl Ht Hr.
  assert (Hb : VPuff.Inflate.blockZ bytes (p + 3) t out = Some (o, q, true)).
  { unfold PuffL_res in Hr.
    destruct (VPuff.Inflate.blockZ bytes (p + 3) t out) as [[[o' q'] [|]]|]; inversion Hr; reflexivity. }
  destruct (PuffL_good bytes p out l t o q Hp Hq Hinv Hl Ht Hb) as [H1 H2].
  destruct (Z.eqb_spec l 1); auto.
Qed.

Lemma PuffL_room_le wr bytes out p p' : p <= p' -> room wr bytes out p -> room wr bytes out p'.
Proof. unfold room. intros H [H1|H1]; [left|right]; auto; lia. Qed.

Lemma PuffL_room0 wr dest bytes outlen :
  sizes_ok wr dest (Zlength bytes) outlen -> room wr bytes [] 0.
Proof.
  unfold sizes_ok, room, nbits. destruct wr; [auto|]. intros [H1 [_ H2]]. right.
  rewrite Zlength_nil. lia.
Qed.

Lemma PuffL_incnt incnt bitcnt : 0 <= bitcnt <= 7 -> (8 * incnt - bitcnt + 7) / 8 = incnt.
Proof.
  intros H. symmetry. apply Z.div_unique with (r := 7 - bitcnt); lia.
Qed.

Lemma PuffL_buf_pos bytes incnt bitbuf bitcnt :
  buf_ok bytes incnt bitbuf bitcnt -> 0 <= 8 * incnt - bitcnt <= nbits bytes.
Proof.
  unfold buf_ok, nbits. intros (H1 & H2 & H3 & _).
  destruct (Z.eq_dec incnt 0) as [E|E]; [rewrite (H3 E), E; lia | lia].
Qed.

(* a nonzero return: the block's output does not fit, or the spec fails *)
Lemma PuffL_fail_r wr outlen res r out' bytes incnt' bitbuf' bitcnt' eof' :
  block_ok wr outlen res r out' bytes incnt' bitbuf' bitcnt' eof' -> Int.repr r <> Int.zero ->
  match res with Some (o, _) => fits wr outlen o = false | None => True end.
Proof.
  unfold block_ok. destruct res as [[o q]|]; [|auto].
  destruct (fits wr outlen o); [|auto]. intros [Hr _] Hne. subst r. contradiction Hne. reflexivity.
Qed.

(* puff()'s postcondition when it fails *)
Lemma PuffL_notok_post wr outlen bytes r dl sl (outv : list val) :
  notok wr outlen bytes -> r <> 0 ->
  match inflateZ bytes with
  | Some (o, nb, true) =>
      if fits wr outlen o
      then r = 0 /\ dl = Zlength o /\ (sl = (nb + 7) / 8)%Z /\
           (wr = true -> outv = map Vint (map Int.repr o) ++ Zrepeat Vundef (outlen - Zlength o))
      else r <> 0
  | _ => r <> 0
  end.
Proof.
  unfold notok. destruct (inflateZ bytes) as [[[o nb] [|]]|]; auto. intros H; rewrite H; auto.
Qed.

(* and when it succeeds *)
Lemma PuffL_ok_post wr outlen bytes out incnt bitcnt (outv : list val) :
  inflateZ bytes = Some (out, 8 * incnt - bitcnt, true) -> fits wr outlen out = true ->
  0 <= bitcnt <= 7 ->
  (wr = true -> outv = map Vint (map Int.repr out) ++ Zrepeat Vundef (outlen - Zlength out)) ->
  match inflateZ bytes with
  | Some (o, nb, true) =>
      if fits wr outlen o
      then 0 = 0 /\ Zlength out = Zlength o /\ (incnt = (nb + 7) / 8)%Z /\
           (wr = true -> outv = map Vint (map Int.repr o) ++ Zrepeat Vundef (outlen - Zlength o))
      else 0 <> 0
  | _ => 0 <> 0
  end.
Proof.
  intros H Hf Hb Hw. rewrite H, Hf. rewrite PuffL_incnt by auto. auto.
Qed.
