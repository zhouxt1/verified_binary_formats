(* The rest of the Lean spec in Rocq over Z and lists: the functions the VST
   proofs of puff's inflate are stated against. Each follows its Lean
   definition step for step (lspec/Lspec/Deflate/Spec.lean, unfolded as in
   InflateExport.lean); InflateEq.v proves them equal to the imported ones.
   Recursions take a fuel argument; *F versions supply enough. Decoding a
   symbol is the imported Lean decodeSym itself (Bridge.lean_decode). *)
From Stdlib Require Import ZArith List Lia Bool.
From VST.zlist Require Import sublist.
Require Import VPuff.Model.
Require VPuff.Bridge.
Import ListNotations.
Open Scope Z_scope.

Notation lean_decode := VPuff.Bridge.lean_decode.

(** * Bits *)

Definition nbits (bytes : list Z) : Z := 8 * Zlength bytes.

(* lsbVal: n bits from p, the first the least significant *)
Fixpoint lsbZ (bytes : list Z) (p : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n => (if bitZ bytes p then 1 else 0) + 2 * lsbZ bytes (p + 1) n
  end.

(* getbits *)
Definition getbitsZ (bytes : list Z) (p n : Z) : option Z :=
  if p + n <=? nbits bytes then Some (lsbZ bytes p (Z.to_nat n)) else None.

(** * The length and distance tables (InflateExport.lenBase etc.) *)

Definition lenBaseZ (i : Z) : Z :=
  if i <? 8 then i + 3 else if i =? 28 then 258 else 2 ^ (i / 4 - 1) * (4 + i mod 4) + 3.
Definition lenExtraZ (i : Z) : Z := if i <? 8 then 0 else if i =? 28 then 0 else i / 4 - 1.
Definition distBaseZ (i : Z) : Z := if i <? 4 then i + 1 else 2 ^ (i / 2 - 1) * (2 + i mod 2) + 1.
Definition distExtraZ (i : Z) : Z := if i <? 4 then 0 else i / 2 - 1.

(** * Compressed blocks: inflateSyms *)

(* lzCopy: copy n bytes from d back, one at a time *)
Fixpoint lzCopyZ (out : list Z) (d : Z) (n : nat) : list Z :=
  match n with
  | O => out
  | S n => lzCopyZ (out ++ [Znth (Z.max 0 (Zlength out - d)) out]) d n
  end.

Fixpoint symsZ (lit dist bytes : list Z) (fuel : nat) (p : Z) (out : list Z) : option (list Z * Z) :=
  match fuel with
  | O => None
  | S f =>
    match lean_decode lit bytes p with
    | None => None
    | Some (s, p1) =>
      if s <? 256 then
        (if (p <? p1) && (p1 <=? nbits bytes) then symsZ lit dist bytes f p1 (out ++ [s]) else None)
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
                  (if (p <? p3 + distExtraZ ds) && (p3 + distExtraZ ds <=? nbits bytes) then
                     symsZ lit dist bytes f (p3 + distExtraZ ds)
                       (lzCopyZ out (distBaseZ ds + e2) (Z.to_nat (lenBaseZ (s - 257) + e)))
                   else None)
                else None
              end
            else None
          end
        end
      else None
    end
  end.

(* inflateSyms (code lit) (code dist) (bitsOf bytes) p out *)
Definition symsF (lit dist bytes : list Z) (p : Z) (out : list Z) : option (list Z * Z) :=
  symsZ lit dist bytes (Z.to_nat (nbits bytes - p) + 1) p out.

(** * Stored blocks *)

Fixpoint bytesAtZ (bytes : list Z) (q : Z) (n : nat) : list Z :=
  match n with
  | O => []
  | S n => lsbZ bytes q 8 :: bytesAtZ bytes (q + 8) n
  end.

Definition storedZ (bytes : list Z) (p : Z) : option (list Z * Z) :=
  let q := (p + 7) / 8 * 8 in
  match getbitsZ bytes q 16 with
  | None => None
  | Some len =>
    match getbitsZ bytes (q + 16) 16 with
    | None => None
    | Some nlen =>
      if (len + nlen =? 65535) && (q + 32 + 8 * len <=? nbits bytes) then
        Some (bytesAtZ bytes (q + 32) (Z.to_nat len), q + 32 + 8 * len)
      else None
    end
  end.

(** * Dynamic block headers *)

Definition clOrderZ : list Z := [16; 17; 18; 0; 8; 7; 9; 6; 10; 5; 11; 4; 12; 3; 13; 2; 14; 1; 15].

Fixpoint readCLgo (bytes : list Z) (p hclen : Z) (fuel : nat) (i : Z) (acc : list Z) :
    option (list Z * Z) :=
  match fuel with
  | O => None
  | S f =>
    if i <? hclen then
      match getbitsZ bytes (p + 3 * i) 3 with
      | None => None
      | Some v => readCLgo bytes p hclen f (i + 1) (upd_Znth (Znth i clOrderZ) acc v)
      end
    else Some (acc, p + 3 * hclen)
  end.

Definition readCLZ (bytes : list Z) (p hclen : Z) : option (list Z * Z) :=
  readCLgo bytes p hclen 20 0 (Zrepeat 0 19).

Definition lastZ (l : list Z) : option Z :=
  match rev l with [] => None | x :: _ => Some x end.

Fixpoint readLensZ (cl bytes : list Z) (fuel : nat) (p total : Z) (acc : list Z) :
    option (list Z * Z) :=
  match fuel with
  | O => None
  | S f =>
    if total <=? Zlength acc then Some (acc, p)
    else
      match lean_decode cl bytes p with
      | None => None
      | Some (s, p1) =>
        if s <? 16 then readLensZ cl bytes f p1 total (acc ++ [s])
        else
          let nb := if s =? 16 then 2 else if s =? 17 then 3 else 7 in
          let base := if s =? 18 then 11 else 3 in
          match getbitsZ bytes p1 nb with
          | None => None
          | Some e =>
            match (if s =? 16 then lastZ acc else Some 0) with
            | None => None
            | Some v =>
              if Zlength acc + (base + e) <=? total then
                readLensZ cl bytes f (p1 + nb) total (acc ++ Zrepeat v (base + e))
              else None
            end
          end
      end
  end.

(* the count of each length and the Kraft sum, as construct() computes them *)
Definition cntOf (lens : list Z) (l : Z) : Z := cntZ (fun i => Znth i lens) (Z.to_nat (Zlength lens)) l.
Definition krOf (lens : list Z) : Z := krZ (cntOf lens) 15.

Definition notOversubZ (lens : list Z) : bool := krOf lens <=? 32768.

Definition zlibOkZ (lens : list Z) (clCode : bool) : bool :=
  (cntOf lens 0 =? Zlength lens) || (krOf lens =? 32768) ||
    (negb clCode && (cntOf lens 1 =? 1) && (krOf lens =? 16384)).

Definition dynHeaderZ (bytes : list Z) (p : Z) : option (list Z * list Z * Z * bool) :=
  match getbitsZ bytes p 5 with
  | None => None
  | Some hlit =>
    match getbitsZ bytes (p + 5) 5 with
    | None => None
    | Some hdist =>
      match getbitsZ bytes (p + 10) 4 with
      | None => None
      | Some hclen =>
        if hlit + 257 <=? 286 then
          match readCLZ bytes (p + 14) (hclen + 4) with
          | None => None
          | Some (cl, q) =>
            if notOversubZ cl then
              match readLensZ cl bytes (Z.to_nat (hlit + 257 + (hdist + 1)) + 1) q
                      (hlit + 257 + (hdist + 1)) [] with
              | None => None
              | Some (lens, r) =>
                let lit := sublist 0 (hlit + 257) lens in
                let dist := sublist (hlit + 257) (hlit + 257 + (hdist + 1)) lens in
                if negb (Znth 256 lit =? 0) && (notOversubZ lit && notOversubZ dist) then
                  Some (lit, dist, r,
                    zlibOkZ cl true && zlibOkZ lit false && zlibOkZ dist false && (hdist + 1 <=? 30))
                else None
              end
            else None
          end
        else None
      end
    end
  end.

(** * Blocks and the stream *)

Definition fixedLitZ : list Z := Zrepeat 8 144 ++ Zrepeat 9 112 ++ Zrepeat 7 24 ++ Zrepeat 8 8.
Definition fixedDistZ : list Z := Zrepeat 5 32.

Definition blockZ (bytes : list Z) (p btype : Z) (out : list Z) : option (list Z * Z * bool) :=
  if btype =? 0 then
    match storedZ bytes p with
    | None => None
    | Some (bs, q) => Some (out ++ bs, q, true)
    end
  else if btype =? 1 then
    match symsF fixedLitZ fixedDistZ bytes p out with
    | None => None
    | Some (o, q) => Some (o, q, true)
    end
  else if btype =? 2 then
    match dynHeaderZ bytes p with
    | None => None
    | Some (lit, dist, q, z) =>
      match symsF lit dist bytes q out with
      | None => None
      | Some (o, r) => Some (o, r, z)
      end
    end
  else None.

Fixpoint blocksZ (bytes : list Z) (fuel : nat) (p : Z) (out : list Z) (zl : bool) :
    option (list Z * Z * bool) :=
  match fuel with
  | O => None
  | S f =>
    match getbitsZ bytes p 1 with
    | None => None
    | Some bfinal =>
      match getbitsZ bytes (p + 1) 2 with
      | None => None
      | Some btype =>
        match blockZ bytes (p + 3) btype out with
        | None => None
        | Some (o, q, z) =>
          if bfinal =? 1 then Some (o, q, zl && z)
          else if (p <? q) && (q <=? nbits bytes) then blocksZ bytes f q o (zl && z)
          else None
        end
      end
    end
  end.

Definition blocksF (bytes : list Z) (p : Z) (out : list Z) (zl : bool) : option (list Z * Z * bool) :=
  blocksZ bytes (Z.to_nat (nbits bytes - p) + 1) p out zl.

(* Deflate.inflateBytes: the output, the bits the stream took, and whether zlib
   accepts it *)
Definition inflateZ (bytes : list Z) : option (list Z * Z * bool) := blocksF bytes 0 [] true.
