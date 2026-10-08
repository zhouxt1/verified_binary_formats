(* The result: puff's inflate (../c/puff.c, altered from zlib's contrib/puff)
   meets a contract stated against the Lean spec of DEFLATE, imported from Lean
   (LeanSpec.v).

   puff_lean says: puff() returns 0 exactly when Deflate.inflateBytes decodes
   the input with the zlib flag on and the output fits in the buffer, and it
   then writes the spec's output, sets *destlen to its length and *sourcelen
   to the bytes the stream took ((bits + 7) / 8). Otherwise it returns nonzero.

   puff_lean is the C contract puff_spec (Spec_puff.v, proved in Verif_puff.v)
   with the Rocq mirror inflateZ replaced by the imported Lean function, by
   InflateEq.inflateZ_eq. puff_bodies collects the proofs of every function
   puff() calls, against the same Gprog, which is what makes the result hold
   for the whole program. See ../README.md for what it rests on. *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Spec_puff.
Require VPuff.InflateEq.
Require VPuff.Verif_bits VPuff.Verif_stored VPuff.Verif_decode VPuff.Verif_construct
  VPuff.Verif_codes VPuff.Verif_fixed VPuff.Verif_dynamic VPuff.Verif_puff.
Open Scope Z_scope.

Notation lean_inflate := VPuff.InflateEq.lean_inflate.

Definition puff_lean_spec :=
 DECLARE _puff
  WITH sho : share, shd : share, shi : share, shs : share, dest : val, destlen : val,
       source : val, sourcelen : val, outlen : Z, wr : bool, bytes : list Z, gv : globals
  PRE [ tptr tuchar, tptr tuint, tptr tuchar, tptr tuint ]
    PROP (writable_share sho; writable_share shd; readable_share shi; writable_share shs;
          bytes_ok bytes; sizes_ok wr dest (Zlength bytes) outlen)
    PARAMS (dest; destlen; source; sourcelen) GLOBALS (gv)
    SEP ((if wr then data_at_ sho (tarray tuchar outlen) dest else emp);
         data_at shd tuint (Vint (Int.repr outlen)) destlen;
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) source;
         data_at shs tuint (Vint (Int.repr (Zlength bytes))) sourcelen;
         all_tables gv)
  POST [ tint ]
    EX r : Z, EX dl : Z, EX sl : Z, EX outv : list val,
    PROP (Int.min_signed <= r <= Int.max_signed;
          match lean_inflate bytes with
          | Some (o, nb, true) =>
              if fits wr outlen o
              then r = 0 /\ dl = Zlength o /\ (sl = (nb + 7) / 8)%Z /\
                   (wr = true -> outv = map Vint (map Int.repr o) ++ Zrepeat Vundef (outlen - Zlength o))
              else r <> 0
          | _ => r <> 0
          end)
    RETURN (Vint (Int.repr r))
    SEP ((if wr then data_at sho (tarray tuchar outlen) outv dest else emp);
         data_at shd tuint (Vint (Int.repr dl)) destlen;
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) source;
         data_at shs tuint (Vint (Int.repr sl)) sourcelen;
         all_tables gv).

Local Opaque VPuff.Inflate.inflateZ lean_inflate.

Lemma puff_lean_sub : funspec_sub (snd puff_spec) (snd puff_lean_spec).
Proof.
  do_funspec_sub.
  destruct w as [[[[[[[[[[[sho shd] shi] shs] dest] destlen] source] sourcelen] outlen] wr] bytes] gv].
  clear H. normalize.
  assert (Heq : VPuff.Inflate.inflateZ bytes = lean_inflate bytes)
    by (apply VPuff.InflateEq.inflateZ_eq; assumption).
  Exists (sho, shd, shi, shs, dest, destlen, source, sourcelen, outlen, wr, bytes, gv) emp.
  entailer!.
  intros tau ? ?.
  Exists x0 x1 x2 x3. entailer!.
  match goal with H : match VPuff.Inflate.inflateZ bytes with _ => _ end |- _ =>
    rewrite Heq in H; exact H end.
Qed.

Theorem puff_lean : semax_body Vprog Gprog f_puff puff_lean_spec.
Proof.
  eapply semax_body_funspec_sub; [exact VPuff.Verif_puff.body_puff | exact puff_lean_sub |].
  compute; repeat (constructor; [intros H; repeat (destruct H as [H|H]; [discriminate|]); exact H|]); constructor.
Qed.

(* every function in puff.c meets its contract, assuming only the contracts in
   Gprog of the functions it calls *)
Theorem puff_bodies :
  semax_body Vprog Gprog f_bits bits_spec /\
  semax_body Vprog Gprog f_stored stored_spec /\
  semax_body Vprog Gprog f_decode decode_spec /\
  semax_body Vprog Gprog f_construct construct_spec /\
  semax_body Vprog Gprog f_codes codes_spec /\
  semax_body Vprog Gprog f_fixed fixed_spec /\
  semax_body Vprog Gprog f_dynamic dynamic_spec /\
  semax_body Vprog Gprog f_puff puff_lean_spec.
Proof.
  exact (conj VPuff.Verif_bits.body_bits (conj VPuff.Verif_stored.body_stored
        (conj VPuff.Verif_decode.body_decode (conj VPuff.Verif_construct.body_construct
        (conj VPuff.Verif_codes.body_codes (conj VPuff.Verif_fixed.body_fixed
        (conj VPuff.Verif_dynamic.body_dynamic puff_lean))))))).
Qed.

Print Assumptions puff_bodies.
