(* puff's bits() reads the spec's getbits (Inflate.getbitsZ): VST proof of
   Spec_puff.bits_spec. *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model VPuff.Spec_puff VPuff.P2_Bits.
Open Scope Z_scope.

Lemma or_repr' x y : 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
  Int.or (Int.repr x) (Int.repr y) = Int.repr (Z.lor x y).
Proof. intros; unfold Int.or; rewrite !Int.unsigned_repr by lia; reflexivity. Qed.

Lemma shl_repr' x c : 0 <= x <= Int.max_unsigned -> 0 <= c < 32 ->
  Int.shl (Int.repr x) (Int.repr c) = Int.repr (Z.shiftl x c).
Proof. intros; unfold Int.shl; rewrite !Int.unsigned_repr by rep_lia; reflexivity. Qed.

Lemma shr_repr' x c : 0 <= x <= Int.max_signed -> 0 <= c < 32 ->
  Int.shr (Int.repr x) (Int.repr c) = Int.repr (Z.shiftr x c).
Proof.
  intros; unfold Int.shr; rewrite Int.signed_repr by rep_lia.
  rewrite Int.unsigned_repr by rep_lia; reflexivity.
Qed.

Lemma mask_repr x n : 0 <= x <= Int.max_unsigned -> 0 <= n <= 20 ->
  Int.and (Int.repr x) (Int.sub (Int.shl (Int.repr 1) (Int.repr n)) (Int.repr 1)) =
    Int.repr (Z.land x (Z.ones n)).
Proof.
  intros Hx Hn.
  rewrite shl_repr' by rep_lia. rewrite Z.shiftl_1_l.
  assert (0 < 2 ^ n <= 2 ^ 20) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  rewrite sub_repr. unfold Int.and.
  rewrite !Int.unsigned_repr by rep_lia. rewrite Z.ones_equiv. reflexivity.
Qed.

Ltac tcb := entailer!; try (simpl; rewrite ?Int.unsigned_repr by rep_lia; rep_lia).
Ltac fw := forward; try solve [tcb].
Ltac fws := forward; try (entailer!; change (Int.unsigned Int.iwordsize) with 32; lia).

Lemma body_bits : semax_body Vprog Gprog f_bits bits_spec.
Proof.
  start_function.
  unfold bytes_ok in *.
  match goal with H : buf_ok _ _ _ _ |- _ => destruct H as (Hinc & Hbc & Hinc0 & Hbuf) end.
  set (p := 8 * incnt - bitcnt).
  assert (Hp0 : 0 <= p) by (unfold p; destruct (Z.eq_dec incnt 0); [rewrite Hinc0 by auto|]; lia).
  assert (Hv0 : bitbuf = lsbZ bytes p (Z.to_nat bitcnt)).
  { rewrite Hbuf. destruct (incnt =? 0) eqn:E.
    - apply Z.eqb_eq in E. rewrite (Hinc0 E). reflexivity.
    - apply Z.eqb_neq in E. unfold p. apply shiftr_byte_lsbZ; auto; lia. }
  clear Hbuf.
  unfold state_rep.
  forward. (* val = s->bitbuf *)
  forward_loop (EX k : Z,
    PROP (incnt <= k <= Zlength bytes; 0 <= bitcnt + 8 * (k - incnt) < need + 8)
    LOCAL (temp _val (Vint (Int.repr (lsbZ bytes p (Z.to_nat (bitcnt + 8 * (k - incnt))))));
           temp _s s; temp _need (Vint (Int.repr need)))
    SEP (data_at sh (Tstruct _state noattr)
           (outp, (Vint (Int.repr outlen), (Vint (Int.repr outcnt), (inp, (Vint (Int.repr (Zlength bytes)),
            (Vint (Int.repr k), (Vint (Int.repr bitbuf), (Vint (Int.repr (bitcnt + 8 * (k - incnt))),
             Vint (Int.repr 0))))))))) s;
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp))%assert
  break: (EX k : Z,
    PROP (incnt <= k <= Zlength bytes; 0 <= bitcnt + 8 * (k - incnt) < need + 8;
          need <= bitcnt + 8 * (k - incnt))
    LOCAL (temp _val (Vint (Int.repr (lsbZ bytes p (Z.to_nat (bitcnt + 8 * (k - incnt))))));
           temp _s s; temp _need (Vint (Int.repr need)))
    SEP (data_at sh (Tstruct _state noattr)
           (outp, (Vint (Int.repr outlen), (Vint (Int.repr outcnt), (inp, (Vint (Int.repr (Zlength bytes)),
            (Vint (Int.repr k), (Vint (Int.repr bitbuf), (Vint (Int.repr (bitcnt + 8 * (k - incnt))),
             Vint (Int.repr 0))))))))) s;
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp))%assert.
  { Exists incnt. rewrite Z.sub_diag, Z.mul_0_r, Z.add_0_r, <- Hv0. clear Hv0. entailer!. }
  { clear Hv0. Intros k.
    set (c := bitcnt + 8 * (k - incnt)) in *.
    forward. (* t9 = s->bitcnt *)
    forward_if.
    2:{ forward. Exists k. entailer!. }
    forward. forward. (* t7 = s->incnt; t8 = s->inlen *)
    forward_if.
    { (* out of input *)
      forward. forward.
      Exists 0 (Zlength bytes) bitbuf c 1.
      unfold state_rep. entailer!.
      rewrite (proj2 (Z.leb_gt _ _)); [split; reflexivity|].
      unfold VPuff.Inflate.nbits, p, c in *. lia. }
    assert (Hb : 0 <= Znth k bytes < 256) 
      by (match goal with H : Forall _ bytes |- _ => rewrite Forall_Znth in H; apply H; lia end).
    assert (Hlb := lsbZ_bound bytes (Z.to_nat c) p).
    rewrite Z2Nat.id in Hlb by lia.
    assert (Hc2 : 2 ^ c <= 2 ^ 20) by (apply Z.pow_le_mono_r; lia).
    fw. fw. fw. fw. (* incnt++; t5 = in[t1] *)
    fw. (* t6 = s->bitcnt *)
    forward. (* val |= t5 << t6 *)
    { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
    fw. fw. (* bitcnt += 8 *)
    Exists (k + 1).
    assert (Hsh : 0 <= Z.shiftl (Znth k bytes) c <= 267386880).
    { rewrite Z.shiftl_mul_pow2 by lia. change 267386880 with (255 * 2 ^ 20). nia. }
    assert (Hlb' : 0 <= lsbZ bytes p (Z.to_nat c) <= 1048576).
    { change 1048576 with (2 ^ 20). lia. }
    rewrite shl_repr' by rep_lia.
    rewrite or_repr' by rep_lia.
    rewrite lsbZ_or_byte by (auto; unfold p, c in *; lia).
    rewrite !add_repr.
    replace (c + 8) with (bitcnt + 8 * (k + 1 - incnt)) by (unfold c; lia).
    entailer!. }
  (* the bits are there: return the low need of them *)
  clear Hv0. Intros k.
  set (c := bitcnt + 8 * (k - incnt)) in *.
  assert (Hlb := lsbZ_bound bytes (Z.to_nat c) p).
  rewrite Z2Nat.id in Hlb by lia.
  assert (Hc2 : 2 ^ c <= 2 ^ 20) by (apply Z.pow_le_mono_r; lia).
  assert (Hlb' : 0 <= lsbZ bytes p (Z.to_nat c) <= 1048576).
  { change 1048576 with (2 ^ 20). lia. }
  fws. (* s->bitbuf = val >> need *)
  fws. fws. (* s->bitcnt -= need *)
  assert (H2n : 0 < 2 ^ need <= 8192).
  { split; [apply Z.pow_pos_nonneg; lia|]. change 8192 with (2 ^ 13). apply Z.pow_le_mono_r; lia. }
  forward. (* return *)
  { entailer!. rewrite shl_repr' by rep_lia. rewrite Z.shiftl_1_l, Int.signed_repr by rep_lia.
    change (Int.unsigned Int.iwordsize) with 32. rep_lia. }
  rewrite mask_repr by rep_lia. rewrite lsbZ_land by lia.
  rewrite shr_repr' by rep_lia. rewrite lsbZ_shiftr by lia.
  rewrite ?sub_repr.
  Exists (lsbZ bytes p (Z.to_nat need)) k (lsbZ bytes (p + need) (Z.to_nat (c - need))) (c - need) 0.
  unfold state_rep. entailer!.
  assert (Hk : 8 * k = p + c) by (unfold p, c; lia).
  rewrite (proj2 (Z.leb_le _ _)) by (unfold VPuff.Inflate.nbits; lia).
  split; [reflexivity|]. split; [lia|]. split; [|reflexivity].
  unfold buf_ok. split; [lia|]. split; [lia|]. split.
  - intros Hk0. assert (Hi0 : incnt = 0) by lia. specialize (Hinc0 Hi0). lia.
  - destruct (k =? 0) eqn:E.
    + apply Z.eqb_eq in E. assert (Hi0 : incnt = 0) by lia. specialize (Hinc0 Hi0).
      replace (c - need) with 0 by lia. reflexivity.
    + apply Z.eqb_neq in E.
      rewrite shiftr_byte_lsbZ by (auto; lia). f_equal. lia.
Qed.
