(* puff builds the fixed distance code from 30 lengths of 5, the spec from 32
   (Inflate.fixedDistZ): decoding agrees on symbols below 30, and puff fails to
   decode 30 and 31 (Lean: InflateExport.decodeSym_dist30). *)
From LeanImport Require Import Lean.
Require Import VPuff.LeanSpec VPuff.LeanNat VPuff.Bridge.
Close Scope Nat_scope. Close Scope lean_scope.
From Stdlib Require Import ZArith List Lia.
From VST.zlist Require Import sublist.
Require VPuff.Inflate.
Open Scope Z_scope.

Lemma arrN_rep30 : arrN (Zrepeat 5 30) = Array_replicate_inst1 Nat (L# 30) (L# 5).
Proof.
  rewrite (of_leq (Deflate_InflateExport_replicate_mk Nat (L# 30) (L# 5))).
  reflexivity.
Qed.

Lemma arrN_rep32 : arrN VPuff.Inflate.fixedDistZ = Deflate_fixedDist.
Proof.
  unfold Deflate_fixedDist.
  rewrite (of_leq (Deflate_InflateExport_replicate_mk Nat (L# 32) (L# 5))).
  reflexivity.
Qed.

Lemma lean_decode_dist30 (bytes : list Z) (p : Z) :
  lean_decode (Zrepeat 5 30) bytes p =
    match lean_decode VPuff.Inflate.fixedDistZ bytes p with
    | Some (ds, q) => if ds <? 30 then Some (ds, q) else None
    | None => None
    end.
Proof.
  unfold lean_decode. rewrite arrN_rep30, arrN_rep32.
  rewrite (of_leq (Deflate_InflateExport_decodeSym_dist30 _ _)).
  destruct (Deflate_decodeSym (Deflate_code Deflate_fixedDist) (Deflate_bitsOf (arrU8 bytes)) (LN p))
    as [|x]; [reflexivity|].
  destruct x as [ds q]. cbn [Vopt fst1 snd1].
  change (Deflate_InflateExport_inflateSyms_eq_match_3 _ (Option_some_inst1 _ (Prod_mk_inst3 Nat Nat ds q)) _ _)
    with (cond (Option_inst1 (Prod_inst3 Nat Nat)) (Nat_blt ds (L# 30))
            (Option_some_inst1 _ (Prod_mk_inst3 Nat Nat ds q)) (Option_none_inst1 _)).
  destruct (Nat_blt ds (L# 30)) eqn:E; pose proof (f_equal B2b E) as E'; rewrite B2b_blt in E';
    cbn [B2b] in E'; vlits; rewrite E'.
  - rewrite cond_false. reflexivity.
  - rewrite cond_true. reflexivity.
Qed.
