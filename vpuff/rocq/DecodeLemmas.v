(* Arithmetic facts for the VST proof of decode (Verif_decode.v). *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model VPuff.Spec_puff.
Open Scope Z_scope.

(* the byte buffer: bits q .. 8*incnt - 1 of the stream are the low r bits of
   bitbuf, r = 8 * incnt - q *)
Definition bufval (bytes : list Z) (incnt r : Z) : Z :=
  if incnt =? 0 then 0 else Z.shiftr (Znth (incnt - 1) bytes) (8 - r).

Lemma bufval_nonneg bytes incnt r :
  Forall (fun b => 0 <= b < 256) bytes -> 0 <= incnt <= Zlength bytes -> 0 <= r <= 8 ->
  0 <= bufval bytes incnt r < 256.
Proof.
  intros Hb Hi Hr. unfold bufval. destruct (incnt =? 0) eqn:E; [lia|].
  apply Z.eqb_neq in E.
  assert (Hx : 0 <= Znth (incnt - 1) bytes < 256) by (apply Forall_Znth; auto; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with (Znth (incnt - 1) bytes); [|lia].
  apply Z.div_le_upper_bound; [lia|].
  assert (0 < 2 ^ (8 - r)) by (apply Z.pow_pos_nonneg; lia).
  nia.
Qed.

(* the next bit of the buffer is the stream's bit q *)
Lemma bufval_bit bytes incnt q :
  0 <= q -> 1 <= 8 * incnt - q <= 8 ->
  Z.land (bufval bytes incnt (8 * incnt - q)) 1 = if bitZ bytes q then 1 else 0.
Proof.
  intros Hq Hr. unfold bufval, bitZ.
  destruct (incnt =? 0) eqn:E; [apply Z.eqb_eq in E; lia|].
  assert (Hdiv : q / 8 = incnt - 1).
  { symmetry. apply Z.div_unique_pos with (q - 8 * (incnt - 1)); lia. }
  assert (Hmod : q mod 8 = 8 - (8 * incnt - q)).
  { rewrite Zmod_eq_full by lia; rewrite Hdiv; lia. }
  rewrite Hdiv, Hmod.
  rewrite Z.land_ones with (n := 1) by lia. change (2 ^ 1) with 2.
  rewrite <- Z.bit0_mod, Z.shiftr_spec by lia. rewrite Z.add_0_l.
  destruct (Z.testbit _ _); reflexivity.
Qed.

Lemma bufval_shift bytes incnt r :
  1 <= r <= 8 -> Z.shiftr (bufval bytes incnt r) 1 = bufval bytes incnt (r - 1).
Proof.
  intros Hr. unfold bufval. destruct (incnt =? 0); [reflexivity|].
  rewrite Z.shiftr_shiftr by lia. f_equal; lia.
Qed.

(* C's code |= bit, for even code *)
Lemma lor_even_bit c b : Z.even c = true -> (b = 0 \/ b = 1) -> Z.lor c b = c + b.
Proof.
  intros He [-> | ->]; [rewrite Z.lor_0_r; lia|].
  assert (H0 : Z.land c 1 = 0).
  { rewrite Z.land_ones with (n := 1) by lia. change (2 ^ 1) with 2.
    apply Z.even_spec in He. destruct He as [k ->].
    rewrite Z.mul_comm, Z.mod_mul; lia. }
  rewrite <- (Z.lxor_lor _ _ H0), <- (Z.add_nocarry_lxor _ _ H0). reflexivity.
Qed.

Lemma land7 x : Z.land x 7 = x mod 8.
Proof. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* offs over the 16 counts is monotone and bounded by ncodes *)
Lemma offsZ_mono counts a b :
  Forall (fun c => 0 <= c) counts -> (1 <= a <= b)%nat ->
  offsZ (countF counts) a <= offsZ (countF counts) b.
Proof.
  intros Hc [Ha Hab]. induction Hab as [|b Hab IH]; [lia|].
  rewrite offsZ_succ by lia.
  assert (0 <= countF counts (Z.of_nat b)).
  { unfold countF. destruct (zlt (Z.of_nat b) (Zlength counts)).
    - apply Forall_Znth; auto; lia.
    - rewrite Znth_overflow by lia; unfold default, Inhabitant_Z; lia. }
  lia.
Qed.

Lemma goZ_S count symbol bit nbits p k len cd first index :
  goZ count symbol bit nbits p (S k) len cd first index =
    if nbits <? p + len then None
    else if cd + (if bit (p + len - 1) then 1 else 0) <? first + count len then
      Some (symbol (index + (cd + (if bit (p + len - 1) then 1 else 0) - first)), p + len)
    else goZ count symbol bit nbits p k (len + 1)
           (2 * (cd + (if bit (p + len - 1) then 1 else 0))) (2 * (first + count len))
           (index + count len).
Proof. reflexivity. Qed.

(** * C's int operations on small non-negative values *)

Lemma and_repr x y : 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
  Int.and (Int.repr x) (Int.repr y) = Int.repr (Z.land x y).
Proof. intros; unfold Int.and; rewrite !Int.unsigned_repr by lia; reflexivity. Qed.

Lemma or_repr x y : 0 <= x <= Int.max_unsigned -> 0 <= y <= Int.max_unsigned ->
  Int.or (Int.repr x) (Int.repr y) = Int.repr (Z.lor x y).
Proof. intros; unfold Int.or; rewrite !Int.unsigned_repr by lia; reflexivity. Qed.

Lemma shr1_repr x : 0 <= x <= Int.max_signed ->
  Int.shr (Int.repr x) (Int.repr 1) = Int.repr (Z.shiftr x 1).
Proof.
  intros; unfold Int.shr; rewrite Int.signed_repr by rep_lia.
  rewrite Int.unsigned_repr by rep_lia; reflexivity.
Qed.

Lemma shl1_repr x : 0 <= x <= Int.max_unsigned ->
  Int.shl (Int.repr x) (Int.repr 1) = Int.repr (2 * x).
Proof.
  intros; unfold Int.shl; rewrite !Int.unsigned_repr by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. f_equal; lia.
Qed.

Lemma and7_repr x : Int.and (Int.repr x) (Int.repr 7) = Int.repr (x mod 8).
Proof.
  unfold Int.and. rewrite (Int.unsigned_repr 7) by rep_lia.
  rewrite Int.unsigned_repr_eq, land7.
  rewrite Z.mod_mod_divide; [reflexivity|].
  exists (Int.modulus / 8). reflexivity.
Qed.

Lemma offsZ_nonneg_counts counts l :
  Forall (fun c => 0 <= c <= 320) counts -> 0 <= offsZ (countF counts) l.
Proof.
  intros Hc. induction l as [|[|l] IH]; [cbn; lia|cbn; lia|].
  rewrite offsZ_succ by lia.
  assert (0 <= countF counts (Z.of_nat (S l))).
  { unfold countF. destruct (zlt (Z.of_nat (S l)) (Zlength counts)).
    - assert (H : 0 <= Znth (Z.of_nat (S l)) counts <= 320)
        by (rewrite Forall_Znth in Hc; apply Hc; lia). lia.
    - rewrite Znth_overflow by lia; unfold default, Inhabitant_Z; lia. }
  lia.
Qed.

Lemma offsZ_le_counts counts l :
  Forall (fun c => 0 <= c <= 320) counts -> offsZ (countF counts) l <= 320 * Z.of_nat l.
Proof.
  intros Hc. induction l as [|[|l] IH]; [cbn; lia|cbn; lia|].
  rewrite offsZ_succ by lia.
  assert (countF counts (Z.of_nat (S l)) <= 320).
  { unfold countF. destruct (zlt (Z.of_nat (S l)) (Zlength counts)).
    - assert (H : 0 <= Znth (Z.of_nat (S l)) counts <= 320)
        by (rewrite Forall_Znth in Hc; apply Hc; lia). lia.
    - rewrite Znth_overflow by lia; unfold default, Inhabitant_Z; lia. }
  lia.
Qed.
