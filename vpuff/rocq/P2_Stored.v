(* The mirror's storedZ (Inflate.v) at a byte boundary, in the terms puff's
   stored() computes: four header bytes, then a run of whole bytes. *)
Require Import VST.floyd.proofauto.
Require Import VPuff.Model VPuff.P2_Bits.
Require VPuff.Inflate.
Open Scope Z_scope.

Notation storedZ := VPuff.Inflate.storedZ.
Notation bytesAtZ := VPuff.Inflate.bytesAtZ.

Section Stored.
Variable bytes : list Z.
Hypothesis Hbytes : Forall (fun x => 0 <= x < 256) bytes.

Lemma byte_range k : 0 <= k < Zlength bytes -> 0 <= Znth k bytes < 256.
Proof. intros. rewrite Forall_Znth in Hbytes. apply Hbytes; lia. Qed.

Lemma lsbZ_byte k : 0 <= k < Zlength bytes -> lsbZ bytes (8 * k) 8 = Znth k bytes.
Proof.
  intros Hk. replace (8 * k) with (8 * (k + 1) - 8) by lia.
  change 8%nat with (Z.to_nat 8).
  rewrite <- shiftr_byte_lsbZ by (auto; lia).
  replace (k + 1 - 1) with k by lia. apply Z.shiftr_0_r.
Qed.

Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b -> Z.lor a (Z.shiftl b 8) = a + 256 * b.
Proof.
  intros Ha Hb.
  assert (H0 : Z.land a (Z.shiftl b 8) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8).
    - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite (testbit_small a 8 i) by (simpl; lia). reflexivity. }
  rewrite <- Z.lxor_lor by exact H0. rewrite <- Z.add_nocarry_lxor by exact H0.
  rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma lsbZ_two k : 0 <= k -> k + 2 <= Zlength bytes ->
  lsbZ bytes (8 * k) 16 = Znth k bytes + 256 * Znth (k + 1) bytes.
Proof.
  intros Hk Hk2.
  change 16%nat with (Z.to_nat (8 + 8)).
  rewrite <- (lsbZ_or_byte bytes (8 * k) 8 (k + 1)) by (auto; lia).
  change (Z.to_nat 8) with 8%nat. rewrite lsbZ_byte by lia.
  apply lor_byte; [apply byte_range; lia | apply byte_range; lia].
Qed.

Lemma bytesAtZ_sublist n : forall k, 0 <= k -> k + Z.of_nat n <= Zlength bytes ->
  bytesAtZ bytes (8 * k) n = sublist k (k + Z.of_nat n) bytes.
Proof.
  induction n as [|n IH]; intros k Hk Hn.
  - simpl. rewrite Z.add_0_r, sublist_nil. reflexivity.
  - cbn [VPuff.Inflate.bytesAtZ].
    rewrite lsbZ_byte by lia.
    replace (8 * k + 8) with (8 * (k + 1)) by lia.
    rewrite IH by lia.
    rewrite (sublist_split k (k + 1) (k + Z.of_nat (S n))) by lia.
    rewrite sublist_len_1 by lia.
    replace (k + 1 + Z.of_nat n) with (k + Z.of_nat (S n)) by lia. reflexivity.
Qed.

(* the bit position of a buf_ok state, rounded up to a byte *)
Lemma round_up incnt bitcnt : 0 <= bitcnt <= 7 -> (incnt = 0 -> bitcnt = 0) -> 0 <= incnt ->
  (8 * incnt - bitcnt + 7) / 8 * 8 = 8 * incnt.
Proof.
  intros Hb H0 Hi.
  destruct (Z.eq_dec bitcnt 0) as [->|Hne].
  - rewrite Z.sub_0_r. rewrite <- (Z.div_unique_pos _ 8 incnt 7) by lia. lia.
  - rewrite <- (Z.div_unique_pos _ 8 incnt (7 - bitcnt)) by lia. lia.
Qed.

Section At.
Variables incnt bitcnt : Z.
Hypothesis Hb : 0 <= bitcnt <= 7.
Hypothesis H0 : incnt = 0 -> bitcnt = 0.
Hypothesis Hi : 0 <= incnt.

Let a := Znth incnt bytes.
Let b := Znth (incnt + 1) bytes.
Let c := Znth (incnt + 2) bytes.
Let d := Znth (incnt + 3) bytes.

Lemma stored_short : Zlength bytes < incnt + 4 -> storedZ bytes (8 * incnt - bitcnt) = None.
Proof.
  intros Hs. unfold storedZ, VPuff.Inflate.getbitsZ, VPuff.Inflate.nbits.
  rewrite round_up by auto.
  destruct (8 * incnt + 16 <=? 8 * Zlength bytes) eqn:E1; [|reflexivity].
  rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
Qed.

Lemma stored_header : incnt + 4 <= Zlength bytes ->
  storedZ bytes (8 * incnt - bitcnt) =
    if andb (andb (c =? 255 - a) (d =? 255 - b)) (incnt + 4 + (a + 256 * b) <=? Zlength bytes)
    then Some (sublist (incnt + 4) (incnt + 4 + (a + 256 * b)) bytes, 8 * (incnt + 4 + (a + 256 * b)))
    else None.
Proof.
  intros Hs. unfold storedZ, VPuff.Inflate.getbitsZ, VPuff.Inflate.nbits.
  rewrite round_up by auto.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  rewrite (proj2 (Z.leb_le (8 * incnt + 16 + 16) _)) by lia.
  replace (8 * incnt + 32) with (8 * (incnt + 4)) by lia.
  rewrite lsbZ_two by lia.
  replace (8 * incnt + 16) with (8 * (incnt + 2)) by lia.
  rewrite lsbZ_two by lia.
  replace (incnt + 2 + 1) with (incnt + 3) by lia.
  fold a b c d.
  assert (0 <= a < 256) by (apply byte_range; lia).
  assert (0 <= b < 256) by (apply byte_range; lia).
  assert (0 <= c < 256) by (apply byte_range; lia).
  assert (0 <= d < 256) by (apply byte_range; lia).
  assert (Hc : (a + 256 * b + (c + 256 * d) =? 65535) = andb (c =? 255 - a) (d =? 255 - b)).
  { destruct (c =? 255 - a) eqn:E1, (d =? 255 - b) eqn:E2; cbn [andb];
      rewrite ?Z.eqb_eq, ?Z.eqb_neq in *; try (apply Z.eqb_eq; lia); apply Z.eqb_neq; lia. }
  rewrite Hc.
  destruct (andb (c =? 255 - a) (d =? 255 - b)); [|reflexivity]. cbn [andb].
  destruct (incnt + 4 + (a + 256 * b) <=? Zlength bytes) eqn:E;
    [rewrite (proj2 (Z.leb_le _ _)) by (apply Z.leb_le in E; lia)
    |rewrite (proj2 (Z.leb_gt _ _)) by (apply Z.leb_gt in E; lia)]; cbn [andb]; [|reflexivity].
  apply Z.leb_le in E.
  rewrite bytesAtZ_sublist by (rewrite ?Z2Nat.id; lia).
  rewrite Z2Nat.id by lia. f_equal; f_equal; try lia.
Qed.

End At.
End Stored.

(* the complement checks of stored(), on puff's unsigned ints *)
Lemma not_unsigned L : 0 <= L <= Int.max_unsigned ->
  Int.unsigned (Int.not (Int.repr L)) = Int.max_unsigned - L.
Proof.
  intros HL. rewrite Int.not_neg. unfold Int.add, Int.neg.
  rewrite (Int.unsigned_repr L) by lia.
  change (Int.unsigned Int.mone) with (Int.modulus - 1).
  rewrite !Int.unsigned_repr_eq. rewrite Zplus_mod_idemp_l.
  change Int.max_unsigned with 4294967295 in *. change Int.modulus with 4294967296.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma and255 x : Int.and x (Int.repr 255) = Int.repr (Int.unsigned x mod 256).
Proof.
  change (Int.repr 255) with (Int.repr (two_p 8 - 1)).
  rewrite <- Int.zero_ext_and by lia.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 x)).
  rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia). reflexivity.
Qed.

Lemma not_low a b : 0 <= a < 256 -> 0 <= b < 256 ->
  Int.and (Int.not (Int.repr (a + 256 * b))) (Int.repr 255) = Int.repr (255 - a).
Proof.
  intros Ha Hb. rewrite and255, not_unsigned by rep_lia. f_equal.
  change Int.max_unsigned with 4294967295.
  symmetry. apply Z.mod_unique_pos with (16777215 - b); lia.
Qed.

Lemma not_high a b : 0 <= a < 256 -> 0 <= b < 256 ->
  Int.and (Int.shru (Int.not (Int.repr (a + 256 * b))) (Int.repr 8)) (Int.repr 255) =
    Int.repr (255 - b).
Proof.
  intros Ha Hb. rewrite and255. unfold Int.shru.
  rewrite not_unsigned by rep_lia. rewrite (Int.unsigned_repr 8) by rep_lia.
  change Int.max_unsigned with 4294967295.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- (Z.div_unique_pos _ 256 (16777215 - b) (255 - a)) by lia.
  rewrite Int.unsigned_repr by rep_lia. f_equal.
  symmetry. apply Z.mod_unique_pos with (65535); lia.
Qed.

Lemma len_repr a b : 0 <= a < 256 -> 0 <= b < 256 ->
  Int.or (Int.repr a) (Int.shl (Int.repr b) (Int.repr 8)) = Int.repr (a + 256 * b).
Proof.
  intros Ha Hb. unfold Int.shl, Int.or.
  rewrite !(Int.unsigned_repr b), (Int.unsigned_repr 8) by rep_lia.
  rewrite (Int.unsigned_repr a) by rep_lia.
  rewrite (Int.unsigned_repr (Z.shiftl b 8))
    by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; rep_lia).
  rewrite lor_byte by lia. reflexivity.
Qed.
