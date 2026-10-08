(* Facts about the mirror's inflateSyms (Inflate.symsF) for the VST proofs of
   codes() and fixed(). *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model VPuff.Spec_puff.
Require Import VPuff.Inflate.
Require VPuff.InflateFacts VPuff.Codes_Dist30.
Open Scope Z_scope.

(** * Bits *)

Lemma lsbZ_range bytes p n : 0 <= lsbZ bytes p n < 2 ^ Z.of_nat n.
Proof.
  revert p; induction n as [|n IH]; intros p; cbn [lsbZ].
  - cbn. lia.
  - specialize (IH (p + 1)). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    destruct (bitZ bytes p); lia.
Qed.

(** * The tables *)

Ltac zcases i n :=
  let H := fresh in
  assert (H : In (Z.to_nat i) (seq 0 n)) by (apply in_seq; lia);
  cbn [seq In] in H;
  repeat (destruct H as [H|H]; [replace i with (Z.of_nat (Z.to_nat i)) by lia; rewrite <- H; clear H|]);
  [..|contradiction].

Lemma lensTab_ok i : 0 <= i < 29 ->
  Znth i lensTab = lenBaseZ i /\ Znth i lextTab = lenExtraZ i /\
  0 <= lenExtraZ i <= 5 /\ 3 <= lenBaseZ i <= 258 /\ lenBaseZ i + 2 ^ lenExtraZ i <= 259.
Proof. intros Hi. zcases i 29%nat; vm_compute; repeat split; congruence. Qed.

Lemma distsTab_ok i : 0 <= i < 30 ->
  Znth i distsTab = distBaseZ i /\ Znth i dextTab = distExtraZ i /\
  0 <= distExtraZ i <= 13 /\ 1 <= distBaseZ i <= 24577 /\ distBaseZ i + 2 ^ distExtraZ i <= 32769.
Proof. intros Hi. zcases i 30%nat; vm_compute; repeat split; congruence. Qed.

(** * lzCopy *)

Lemma lzCopyZ_length out d n : Zlength (lzCopyZ out d n) = Zlength out + Z.of_nat n.
Proof.
  revert out; induction n as [|n IH]; intros out; cbn [lzCopyZ]; [lia|].
  rewrite IH, Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

(* lzCopy appends one byte at a time at the end *)
Lemma lzCopyZ_S_end out d n :
  lzCopyZ out d (S n) =
    lzCopyZ out d n ++ [Znth (Z.max 0 (Zlength (lzCopyZ out d n) - d)) (lzCopyZ out d n)].
Proof.
  revert out; induction n as [|n IH]; intros out.
  - reflexivity.
  - change (lzCopyZ out d (S (S n))) with (lzCopyZ (out ++ [Znth (Z.max 0 (Zlength out - d)) out]) d (S n)).
    rewrite IH. reflexivity.
Qed.

Lemma lzCopyZ_bytes out d n : bytes_ok out -> bytes_ok (lzCopyZ out d n).
Proof.
  revert out; induction n as [|n IH]; intros out H; cbn [lzCopyZ]; auto.
  apply IH. unfold bytes_ok in *. rewrite Forall_app. split; auto. constructor; auto.
  destruct (zlt (Z.max 0 (Zlength out - d)) (Zlength out)).
  - apply Forall_Znth; auto. lia.
  - rewrite Znth_overflow by lia. unfold default, Inhabitant_Z. lia.
Qed.

(** * inflateSyms: fuel, one step, growth *)

Section Syms.
Variables (lit dist bytes : list Z).

Lemma decode_none_past p : nbits bytes < p -> 0 <= p -> forall l, lean_decode l bytes p = None.
Proof.
  intros H Hp l. destruct (lean_decode l bytes p) as [[s p1]|] eqn:E; auto.
  apply InflateFacts.lean_decode_bounds in E; auto. lia.
Qed.

Ltac split_all :=
  repeat match goal with
  | |- context [match ?x with _ => _ end] => destruct x eqn:?
  | |- context [if ?x then _ else _] => destruct x eqn:?
  end.

Lemma symsZ_fuel f1 : forall f2 p out, 0 <= p ->
  nbits bytes - p < Z.of_nat f1 -> nbits bytes - p < Z.of_nat f2 ->
  symsZ lit dist bytes f1 p out = symsZ lit dist bytes f2 p out.
Proof.
  induction f1 as [|f1 IH]; intros f2 p out Hp H1 H2.
  - destruct f2 as [|f2]; [reflexivity|]. cbn [symsZ].
    rewrite decode_none_past by lia. reflexivity.
  - destruct f2 as [|f2]; [cbn [symsZ]; rewrite decode_none_past by lia; reflexivity|].
    cbn [symsZ]. split_all; auto;
    match goal with
    | |- symsZ _ _ _ _ ?q _ = symsZ _ _ _ _ ?q _ =>
        repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
        repeat match goal with H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end;
        repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H end;
        apply IH; lia
    | _ => idtac
    end.
Qed.

Lemma symsF_eq p out : 0 <= p ->
  symsF lit dist bytes p out =
    match lean_decode lit bytes p with
    | None => None
    | Some (s, p1) =>
      if s <? 256 then
        (if andb (p <? p1) (p1 <=? nbits bytes) then symsF lit dist bytes p1 (out ++ [s]) else None)
      else if s =? 256 then Some (out, p1)
      else if s - 257 <? 29 then
        match getbitsZ bytes p1 (lenExtraZ (s - 257)) with
        | None => None
        | Some e =>
          match lean_decode dist bytes (p1 + lenExtraZ (s - 257)) with
          | None => None
          | Some (ds, p3) =>
            if ds <? 30 then
              match getbitsZ bytes p3 (distExtraZ ds) with
              | None => None
              | Some e2 =>
                if distBaseZ ds + e2 <=? Zlength out then
                  (if andb (p <? p3 + distExtraZ ds) (p3 + distExtraZ ds <=? nbits bytes) then
                     symsF lit dist bytes (p3 + distExtraZ ds)
                       (lzCopyZ out (distBaseZ ds + e2) (Z.to_nat (lenBaseZ (s - 257) + e)))
                   else None)
                else None
              end
            else None
          end
        end
      else None
    end.
Proof.
  intros Hp. unfold symsF at 1.
  replace (Z.to_nat (nbits bytes - p) + 1)%nat with (S (Z.to_nat (nbits bytes - p))) by lia.
  cbn [symsZ].
  destruct (zlt (nbits bytes) p).
  { rewrite decode_none_past by lia. reflexivity. }
  split_all; auto;
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
  repeat match goal with H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end;
  repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H end;
  unfold symsF; apply symsZ_fuel; lia.
Qed.

Lemma symsZ_grow f : forall p out o q,
  symsZ lit dist bytes f p out = Some (o, q) -> Zlength out <= Zlength o.
Proof.
  induction f as [|f IH]; intros p out o q H; cbn [symsZ] in H; [discriminate|].
  revert H. split_all; intros H; try discriminate.
  - apply IH in H. rewrite Zlength_app in H. list_solve.
  - inversion H; subst; lia.
  - apply IH in H. rewrite lzCopyZ_length in H. lia.
Qed.

Lemma symsF_grow p out o q :
  symsF lit dist bytes p out = Some (o, q) -> Zlength out <= Zlength o.
Proof. apply symsZ_grow. Qed.

End Syms.

(** * fixed(): 30 or 32 distance codes *)

Lemma symsZ_dist30 lit bytes f : forall p out,
  symsZ lit (Zrepeat 5 30) bytes f p out = symsZ lit fixedDistZ bytes f p out.
Proof.
  induction f as [|f IH]; intros p out; [reflexivity|]. cbn [symsZ].
  destruct (lean_decode lit bytes p) as [[s p1]|]; [|reflexivity].
  destruct (s <? 256); [rewrite IH; reflexivity|].
  destruct (s =? 256); [reflexivity|].
  destruct (s - 257 <? 29); [|reflexivity].
  destruct (getbitsZ bytes p1 (lenExtraZ (s - 257))) as [e|]; [|reflexivity].
  rewrite Codes_Dist30.lean_decode_dist30.
  destruct (lean_decode fixedDistZ bytes (p1 + lenExtraZ (s - 257))) as [[ds p3]|]; [|reflexivity].
  cbv beta iota.
  destruct (ds <? 30) eqn:E; rewrite ?E; [|reflexivity].
  destruct (getbitsZ bytes p3 (distExtraZ ds)); [|reflexivity].
  rewrite IH. reflexivity.
Qed.

Lemma symsF_dist30 lit bytes p out :
  symsF lit (Zrepeat 5 30) bytes p out = symsF lit fixedDistZ bytes p out.
Proof. apply symsZ_dist30. Qed.

(** * One step of inflateSyms, case by case, as codes() takes it *)

Ltac bsimpl := repeat first
  [ rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia
  | rewrite (proj2 (Z.leb_le _ _)) by lia | rewrite (proj2 (Z.leb_gt _ _)) by lia
  | rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia ];
  cbn [andb].

Section Step.
Variables (lit dist bytes out : list Z) (p : Z).
Hypothesis Hp : 0 <= p.

Lemma step_none : lean_decode lit bytes p = None -> symsF lit dist bytes p out = None.
Proof. intros E. rewrite symsF_eq, E by lia. reflexivity. Qed.

Variables (s p1 : Z).
Hypothesis Ed : lean_decode lit bytes p = Some (s, p1).

Let B := InflateFacts.lean_decode_bounds _ _ _ _ _ Hp Ed.

Lemma step_lit : s < 256 -> symsF lit dist bytes p out = symsF lit dist bytes p1 (out ++ [s]).
Proof. intros. pose proof B. rewrite symsF_eq, Ed by lia. bsimpl. reflexivity. Qed.

Lemma step_end : s = 256 -> symsF lit dist bytes p out = Some (out, p1).
Proof. intros. pose proof B. rewrite symsF_eq, Ed by lia. bsimpl. reflexivity. Qed.

Lemma step_badlen : 256 < s -> 29 <= s - 257 -> symsF lit dist bytes p out = None.
Proof. intros. pose proof B. rewrite symsF_eq, Ed by lia. bsimpl. reflexivity. Qed.

Variable (i : Z).
Hypotheses (Hs : 256 < s) (Hi : i = s - 257) (Hi29 : i < 29).

Lemma step_len_eof : nbits bytes < p1 + lenExtraZ i -> symsF lit dist bytes p out = None.
Proof. intros. pose proof B. subst i. rewrite symsF_eq, Ed by lia. bsimpl. unfold getbitsZ. bsimpl. reflexivity. Qed.

Hypothesis Hl : p1 + lenExtraZ i <= nbits bytes.

Lemma step_dist_none : lean_decode dist bytes (p1 + lenExtraZ i) = None -> symsF lit dist bytes p out = None.
Proof. intros E. pose proof B. subst i. rewrite symsF_eq, Ed by lia. bsimpl. unfold getbitsZ at 1. bsimpl. rewrite E. reflexivity. Qed.

Variables (ds p3 : Z).
Hypotheses (Edd : lean_decode dist bytes (p1 + lenExtraZ i) = Some (ds, p3)) (Hds : ds < 30).

Lemma step_dist_eof : nbits bytes < p3 + distExtraZ ds -> symsF lit dist bytes p out = None.
Proof. intros. pose proof B. subst i. rewrite symsF_eq, Ed by lia. bsimpl. unfold getbitsZ. bsimpl. rewrite Edd. bsimpl. reflexivity. Qed.

Hypothesis Hd : p3 + distExtraZ ds <= nbits bytes.

Lemma step_far : Zlength out < distBaseZ ds + lsbZ bytes p3 (Z.to_nat (distExtraZ ds)) ->
  symsF lit dist bytes p out = None.
Proof. intros. pose proof B. subst i. rewrite symsF_eq, Ed by lia. bsimpl. unfold getbitsZ. bsimpl. rewrite Edd. bsimpl. reflexivity. Qed.

Lemma step_copy : distBaseZ ds + lsbZ bytes p3 (Z.to_nat (distExtraZ ds)) <= Zlength out ->
  0 <= distExtraZ ds -> 0 <= lenExtraZ i ->
  symsF lit dist bytes p out =
    symsF lit dist bytes (p3 + distExtraZ ds)
      (lzCopyZ out (distBaseZ ds + lsbZ bytes p3 (Z.to_nat (distExtraZ ds)))
         (Z.to_nat (lenBaseZ i + lsbZ bytes p1 (Z.to_nat (lenExtraZ i))))).
Proof.
  intros. pose proof B. pose proof (InflateFacts.lean_decode_bounds dist bytes (p1 + lenExtraZ i) ds p3 ltac:(lia) Edd).
  subst i. rewrite symsF_eq, Ed by lia. bsimpl. unfold getbitsZ. bsimpl. rewrite Edd. bsimpl. reflexivity.
Qed.

End Step.

(** * Failures, output room *)

Lemma block_fail wr outlen res r out' bytes ic bb bc eof : r <> 0 ->
  (forall o q, res = Some (o, q) -> fits wr outlen o = false) ->
  block_ok wr outlen res r out' bytes ic bb bc eof.
Proof.
  intros Hr H. unfold block_ok. destruct res as [[o q]|]; auto.
  rewrite (H o q eq_refl). auto.
Qed.

Lemma block_none wr outlen r out' bytes ic bb bc eof : r <> 0 ->
  block_ok wr outlen None r out' bytes ic bb bc eof.
Proof. intros; apply block_fail; congruence. Qed.

(* the C finds no space for what the spec would still write *)
Lemma nospace lit dist bytes p cur outlen :
  outlen < Zlength cur ->
  forall o q, symsF lit dist bytes p cur = Some (o, q) -> fits true outlen o = false.
Proof.
  intros H o q E. apply symsF_grow in E. unfold fits. apply Z.leb_gt. lia.
Qed.

Lemma room_out wr bytes out p : room wr bytes out p -> p <= nbits bytes ->
  Zlength out <= 2147483647 \/ wr = true.
Proof. unfold room. intros [H|H] Hp; [right|left]; auto; pose proof (Zlength_nonneg out); lia. Qed.

Lemma room_lit wr bytes out p p1 s :
  room wr bytes out p -> p < p1 -> room wr bytes (out ++ [s]) p1.
Proof. unfold room. rewrite Zlength_app, Zlength_cons, Zlength_nil. intros [H|H] Hp; [left|right]; auto; lia. Qed.

Lemma room_copy wr bytes out p p4 d n :
  room wr bytes out p -> p + 2 <= p4 -> 0 <= n <= 258 ->
  room wr bytes (lzCopyZ out d (Z.to_nat n)) p4.
Proof. unfold room. rewrite lzCopyZ_length. intros [H|H] Hp Hn; [left|right]; auto; lia. Qed.

(** * The output buffer *)

Lemma out_upd (cur : list Z) x n : Zlength cur < n ->
  upd_Znth (Zlength cur) (map Vint (map Int.repr cur) ++ Zrepeat Vundef (n - Zlength cur))
    (Vint (Int.repr x)) =
  map Vint (map Int.repr (cur ++ [x])) ++ Zrepeat Vundef (n - Zlength (cur ++ [x])).
Proof. intros. list_solve. Qed.

Lemma out_read (cur : list Z) j n : 0 <= j < Zlength cur -> Zlength cur <= n ->
  Znth j (map Vint (map Int.repr cur) ++ Zrepeat Vundef (n - Zlength cur)) =
  Vint (Int.repr (Znth j cur)).
Proof. intros. list_solve. Qed.

Lemma out_ok_nil outlen bytes o p :
  bytes_ok o -> room false bytes o p -> p <= nbits bytes -> out_ok false outlen o.
Proof.
  intros Hb Hr Hp. split; auto. split; [reflexivity|].
  destruct (room_out _ _ _ _ Hr Hp); [auto|discriminate].
Qed.

Lemma out_ok_wr outlen o :
  bytes_ok o -> Zlength o <= outlen <= 2147483647 -> out_ok true outlen o.
Proof. intros. split; auto. unfold fits. split; [apply Z.leb_le|]; lia. Qed.

Lemma bytes_ok_app1 o x : bytes_ok o -> 0 <= x < 256 -> bytes_ok (o ++ [x]).
Proof. intros. unfold bytes_ok in *. rewrite Forall_app. auto. Qed.

Lemma room_mono wr bytes o p p' : room wr bytes o p -> p <= p' -> room wr bytes o p'.
Proof. unfold room. intros [H|H] Hp; [left|right]; auto; lia. Qed.

(* one byte of the C copy loop: out[outcnt] = out[outcnt - dist] *)
Lemma copy_read out_c D k n : 0 <= k -> 1 <= D <= Zlength out_c -> Zlength out_c + k <= n ->
  Znth (Zlength out_c + k - D)
    (map Vint (map Int.repr (lzCopyZ out_c D (Z.to_nat k))) ++
     Zrepeat Vundef (n - Zlength (lzCopyZ out_c D (Z.to_nat k)))) =
  Vint (Int.repr (Znth (Zlength out_c + k - D) (lzCopyZ out_c D (Z.to_nat k)))).
Proof.
  intros. pose proof (lzCopyZ_length out_c D (Z.to_nat k)). rewrite Z2Nat.id in H2 by lia.
  apply out_read; lia.
Qed.

Lemma copy_write out_c D k n : 0 <= k -> 1 <= D <= Zlength out_c -> Zlength out_c + k < n ->
  upd_Znth (Zlength out_c + k)
    (map Vint (map Int.repr (lzCopyZ out_c D (Z.to_nat k))) ++
     Zrepeat Vundef (n - Zlength (lzCopyZ out_c D (Z.to_nat k))))
    (Vint (Int.repr (Znth (Zlength out_c + k - D) (lzCopyZ out_c D (Z.to_nat k))))) =
  map Vint (map Int.repr (lzCopyZ out_c D (Z.to_nat (k + 1)))) ++
    Zrepeat Vundef (n - Zlength (lzCopyZ out_c D (Z.to_nat (k + 1)))).
Proof.
  intros. pose proof (lzCopyZ_length out_c D (Z.to_nat k)) as HL. rewrite Z2Nat.id in HL by lia.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  rewrite lzCopyZ_S_end, HL, Z.max_r by lia.
  rewrite <- HL. apply out_upd. lia.
Qed.
