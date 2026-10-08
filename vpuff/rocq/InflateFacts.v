(* Facts about the imported spec that several proofs share. *)
From LeanImport Require Import Lean.
Require Import VPuff.LeanSpec VPuff.LeanNat VPuff.Bridge.
Close Scope Nat_scope. Close Scope lean_scope.
From Stdlib Require Import ZArith List Lia.
From VST.zlist Require Import sublist.
Require VPuff.Inflate.
Open Scope Z_scope.

(* A decoded symbol is one of the alphabet's, and its code takes at least one
   bit, all within the input (Lean: InflateExport.decodeSym_bounds). *)
Lemma lean_decode_bounds (lens bytes : list Z) (p s p1 : Z) :
  0 <= p ->
  lean_decode lens bytes p = Some (s, p1) ->
  p < p1 <= VPuff.Inflate.nbits bytes /\ 0 <= s < Zlength lens.
Proof.
  intros Hp H. unfold lean_decode, Vopt in H.
  destruct (Deflate_decodeSym (Deflate_code (arrN lens)) (Deflate_bitsOf (arrU8 bytes)) (LN p))
    as [|x] eqn:E; [discriminate|].
  inversion H as [[Hs Hp1]]; clear H.
  pose proof (of_leq (Deflate_InflateExport_decodeSym_bounds (arrN lens)
    (Deflate_bitsOf (arrU8 bytes)) (LN p) (fst1 _ _ x) (snd1 _ _ x) (to_leq E))) as B.
  destruct (Nat_blt (LN p) (snd1 _ _ x)) eqn:E1, (Nat_ble (snd1 _ _ x) (Array_size_inst1 Bool (Deflate_bitsOf (arrU8 bytes)))) eqn:E2,
    (Nat_blt (fst1 _ _ x) (Array_size_inst1 Nat (arrN lens))) eqn:E3; try discriminate.
  apply (f_equal B2b) in E1, E2, E3.
  rewrite B2b_blt in E1, E3. rewrite B2b_ble in E2. cbn [B2b] in E1, E2, E3.
  apply Z.ltb_lt in E1, E3. apply Z.leb_le in E2.
  rewrite V_LN in E1 by exact Hp.
  rewrite (of_leq (Deflate_InflateExport_bitsOf_size (arrU8 bytes))), V_mul in E2.
  unfold arrU8 in E2. rewrite V_size_mk in E2. vlits.
  unfold arrN in E3. rewrite V_size_mk in E3.
  unfold VPuff.Inflate.nbits. pose proof (V_nonneg (fst1 _ _ x)). lia.
Qed.
