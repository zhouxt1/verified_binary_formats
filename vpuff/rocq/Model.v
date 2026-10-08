(* puff's Huffman decoding in Rocq over Z: the functions the VST proofs show the
   C code computes. They follow Deflate.Puff (lspec/Lspec/Deflate/Puff.lean) step
   for step; Bridge.v proves them equal to the imported Lean ones. *)
From Stdlib Require Import ZArith List Lia.
From VST.zlist Require Import sublist.
Open Scope Z_scope.

(* how many of the symbols 0 .. n-1 have length l *)
Fixpoint cntZ (len : Z -> Z) (n : nat) (l : Z) : Z :=
  match n with
  | O => 0
  | S n' => cntZ len n' l + (if len (Z.of_nat n') =? l then 1 else 0)
  end.

(* where the symbols of length l start in the symbol table *)
Fixpoint offsZ (count : Z -> Z) (l : nat) : Z :=
  match l with
  | O => 0
  | S O => 0
  | S (S _ as m) => offsZ count m + count (Z.of_nat m)
  end.

(* the codes of lengths 1..L as L-bit strings *)
Fixpoint krZ (count : Z -> Z) (L : nat) : Z :=
  match L with
  | O => 0
  | S L' => 2 * krZ count L' + count (Z.of_nat (S L'))
  end.

(* decode, a bit at a time; k lengths left to try *)
Fixpoint goZ (count symbol : Z -> Z) (bit : Z -> bool) (nbits p : Z) (k : nat)
    (len cd first index : Z) : option (Z * Z) :=
  match k with
  | O => None
  | S k' =>
    if nbits <? p + len then None
    else
      let c := cd + (if bit (p + len - 1) then 1 else 0) in
      if c <? first + count len then Some (symbol (index + (c - first)), p + len)
      else goZ count symbol bit nbits p k' (len + 1) (2 * c) (2 * (first + count len))
        (index + count len)
  end.

Definition decodeZ (count symbol : Z -> Z) (bit : Z -> bool) (nbits p : Z) : option (Z * Z) :=
  goZ count symbol bit nbits p 15 1 0 0 0.

(* bit q of a byte sequence *)
Definition bitZ (bytes : list Z) (q : Z) : bool := Z.testbit (Znth (q / 8) bytes) (q mod 8).

(** * Facts *)

Lemma cntZ_nonneg len n l : 0 <= cntZ len n l.
Proof. induction n; cbn; [lia|]. destruct (_ =? _); lia. Qed.

Lemma cntZ_le len n l : cntZ len n l <= Z.of_nat n.
Proof. induction n; cbn; [lia|]. destruct (_ =? _); lia. Qed.

Lemma cntZ_ext len len' n l :
  (forall i, 0 <= i < Z.of_nat n -> len i = len' i) -> cntZ len n l = cntZ len' n l.
Proof.
  induction n; intros H; cbn; auto.
  rewrite IHn by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma offsZ_succ count l : (1 <= l)%nat -> offsZ count (S l) = offsZ count l + count (Z.of_nat l).
Proof. intros; destruct l as [|[|l]]; [lia| |]; reflexivity. Qed.

Lemma krZ_succ count L : krZ count (S L) = 2 * krZ count L + count (Z.of_nat (S L)).
Proof. reflexivity. Qed.
