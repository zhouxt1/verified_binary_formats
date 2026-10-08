(* VST contracts for puff.c (../c, zlib's contrib/puff altered as listed there),
   stated against the Rocq mirror of the Lean spec (Inflate.v) and, for
   decoding one symbol, the imported Lean decodeSym (Bridge.lean_decode).

   puff_spec is the result: puff() returns 0 exactly when the spec decodes the
   input (inflateZ, which InflateEq.v proves is Deflate.inflateBytes) with the
   zlib flag on and the output fits, and then gives the spec's output and the
   number of input bytes the stream took. *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model.
Require VPuff.Bridge VPuff.Inflate.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Open Scope Z_scope.

Notation lean_decode := VPuff.Bridge.lean_decode.
Notation symsF := VPuff.Inflate.symsF.
Notation storedZ := VPuff.Inflate.storedZ.
Notation dynHeaderZ := VPuff.Inflate.dynHeaderZ.
Notation inflateZ := VPuff.Inflate.inflateZ.
Notation lsbZ := VPuff.Inflate.lsbZ.
Notation nbits := VPuff.Inflate.nbits.

(** * The state and the buffers *)

(* struct state: output, then input; bit position 8 * incnt - bitcnt *)
Definition state_rep (sh : share) (s outp : val) (outlen outcnt : Z) (inp : val)
    (inlen incnt bitbuf bitcnt eof : Z) : mpred :=
  data_at sh (Tstruct _state noattr)
    (outp, (Vint (Int.repr outlen), (Vint (Int.repr outcnt), (inp, (Vint (Int.repr inlen),
      (Vint (Int.repr incnt), (Vint (Int.repr bitbuf), (Vint (Int.repr bitcnt), Vint (Int.repr eof))))))))) s.

(* the input position: bitbuf holds the bitcnt unused bits of the last byte read *)
Definition buf_ok (bytes : list Z) (incnt bitbuf bitcnt : Z) : Prop :=
  0 <= incnt <= Zlength bytes /\ 0 <= bitcnt <= 7 /\ (incnt = 0 -> bitcnt = 0) /\
  bitbuf = (if incnt =? 0 then 0 else Z.shiftr (Znth (incnt - 1) bytes) (8 - bitcnt)).

Definition bytes_ok (bytes : list Z) : Prop := Forall (fun b => 0 <= b < 256) bytes.

(* the output: written to a buffer of outlen bytes (wr), or only counted
   (puff's NIL mode); out is the output so far *)
Definition outbuf (wr : bool) (sh : share) (outp : val) (outlen : Z) (out : list Z) : mpred :=
  if wr then data_at sh (tarray tuchar outlen)
               (map Vint (map Int.repr out) ++ Zrepeat Vundef (outlen - Zlength out)) outp
  else emp.

Definition fits (wr : bool) (outlen : Z) (o : list Z) : bool :=
  if wr then Zlength o <=? outlen else true.

(* sizes that keep puff's unsigned counters from wrapping: in NIL mode the
   output is at most 1032 times the input. A real output buffer has at least
   one byte (puff compares its pointer with NIL, which in C needs a valid
   pointer). *)
Definition sizes_ok (wr : bool) (outp : val) (inlen outlen : Z) : Prop :=
  0 <= inlen <= 1073741824 /\
  (if wr then 0 < outlen <= 2147483647 else outp = nullval /\ inlen <= 2000000).

(* in NIL mode, room for the rest of the input: each bit read adds at most
   129 bytes of output (a copy of up to 258 bytes costs at least 2 bits) *)
Definition room (wr : bool) (bytes out : list Z) (p : Z) : Prop :=
  wr = true \/ Zlength out + 129 * (nbits bytes - p) <= 2147483647.

Definition out_ok (wr : bool) (outlen : Z) (out : list Z) : Prop :=
  bytes_ok out /\ fits wr outlen out = true /\ Zlength out <= 2147483647.

(** * The read-only tables (static const in puff.c) *)

Definition lensTab : list Z :=
  [3; 4; 5; 6; 7; 8; 9; 10; 11; 13; 15; 17; 19; 23; 27; 31; 35; 43; 51; 59; 67; 83; 99; 115;
   131; 163; 195; 227; 258].
Definition lextTab : list Z :=
  [0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 2; 2; 2; 2; 3; 3; 3; 3; 4; 4; 4; 4; 5; 5; 5; 5; 0].
Definition distsTab : list Z :=
  [1; 2; 3; 4; 5; 7; 9; 13; 17; 25; 33; 49; 65; 97; 129; 193; 257; 385; 513; 769; 1025; 1537;
   2049; 3073; 4097; 6145; 8193; 12289; 16385; 24577].
Definition dextTab : list Z :=
  [0; 0; 0; 0; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5; 6; 6; 7; 7; 8; 8; 9; 9; 10; 10; 11; 11; 12; 12; 13; 13].
Definition orderTab : list Z := [16; 17; 18; 0; 8; 7; 9; 6; 10; 5; 11; 4; 12; 3; 13; 2; 14; 1; 15].

Definition shortarr (sh : share) (n : Z) (l : list Z) (p : val) : mpred :=
  data_at sh (tarray tshort n) (map Vint (map Int.repr l)) p.

Definition codes_tables (gv : globals) : mpred :=
  (shortarr Ers 29 lensTab (gv _lens) * shortarr Ers 29 lextTab (gv _lext) *
   shortarr Ers 30 distsTab (gv _dists) * shortarr Ers 30 dextTab (gv _dext))%logic.

Definition all_tables (gv : globals) : mpred :=
  (codes_tables gv * shortarr Ers 19 orderTab (gv _order))%logic.

(** * construct() and decode() *)

Definition lenF (lens : list Z) (i : Z) : Z := Znth i lens.
Definition countsOf (lens : list Z) : list Z :=
  map (fun l => cntZ (lenF lens) (Z.to_nat (Zlength lens)) l) (map Z.of_nat (seq 0 16)).
Definition countF (counts : list Z) (l : Z) : Z := Znth l counts.
Definition ncodes (counts : list Z) : Z := offsZ (countF counts) 16.

Definition table (lens : list Z) (syms : list val) : Prop :=
  forall s, 0 <= s < Zlength lens -> 1 <= Znth s lens ->
    Znth (offsZ (countF (countsOf lens)) (Z.to_nat (Znth s lens)) +
          cntZ (lenF lens) (Z.to_nat s) (Znth s lens)) syms = Vint (Int.repr s).

Definition construct_spec :=
 DECLARE _construct
  WITH sh : share, shl : share, h : val, cnt : val, sym : val, length : val, lens : list Z
  PRE [ tptr (Tstruct _huffman noattr), tptr tshort, tint ]
    PROP (writable_share sh; readable_share shl;
          Zlength lens <= 320; Forall (fun x => 0 <= x <= 15) lens)
    PARAMS (h; length; Vint (Int.repr (Zlength lens)))
    SEP (data_at sh (Tstruct _huffman noattr) (cnt, sym) h;
         data_at_ sh (tarray tshort 16) cnt;
         data_at_ sh (tarray tshort (Zlength lens)) sym;
         data_at shl (tarray tshort (Zlength lens)) (map Vint (map Int.repr lens)) length)
  POST [ tint ]
    EX r : Z, EX syms : list val,
    PROP (Int.min_signed <= r <= Int.max_signed;
          r < 0 <-> 32768 < krZ (countF (countsOf lens)) 15;
          0 <= r -> (r = 0 <-> (Znth 0 (countsOf lens) = Zlength lens \/
                                krZ (countF (countsOf lens)) 15 = 32768));
          0 <= r -> table lens syms)
    RETURN (Vint (Int.repr r))
    SEP (data_at sh (Tstruct _huffman noattr) (cnt, sym) h;
         data_at sh (tarray tshort 16) (map Vint (map Int.repr (countsOf lens))) cnt;
         data_at sh (tarray tshort (Zlength lens)) syms sym;
         data_at shl (tarray tshort (Zlength lens)) (map Vint (map Int.repr lens)) length).

(* decode, on tables construct built from lens: the Lean spec's decodeSym
   (code lens) (bitsOf bytes) at the input's bit position *)
Definition decode_spec :=
 DECLARE _decode
  WITH sh : share, shi : share, shh : share, s : val, outp : val, outlen : Z, outcnt : Z,
       inp : val, bytes : list Z, incnt : Z, bitbuf : Z, bitcnt : Z,
       h : val, cnt : val, sym : val, lens : list Z, syms : list val
  PRE [ tptr (Tstruct _state noattr), tptr (Tstruct _huffman noattr) ]
    PROP (writable_share sh; readable_share shi; readable_share shh;
          bytes_ok bytes; Zlength bytes <= Int.max_signed;
          buf_ok bytes incnt bitbuf bitcnt;
          Zlength lens <= 320; Forall (fun x => 0 <= x <= 15) lens;
          Zlength syms = Zlength lens; table lens syms)
    PARAMS (s; h)
    SEP (state_rep sh s outp outlen outcnt inp (Zlength bytes) incnt bitbuf bitcnt 0;
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         data_at shh (Tstruct _huffman noattr) (cnt, sym) h;
         data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf lens))) cnt;
         data_at shh (tarray tshort (Zlength syms)) syms sym)
  POST [ tint ]
    EX r : Z, EX incnt' : Z, EX bitbuf' : Z, EX bitcnt' : Z, EX eof' : Z,
    PROP (Int.min_signed <= r <= Int.max_signed;
          match lean_decode lens bytes (8 * incnt - bitcnt) with
          | Some (v, p') => r = v /\ (8 * incnt' - bitcnt' = p')%Z /\ buf_ok bytes incnt' bitbuf' bitcnt' /\
                            eof' = 0
          | None => r < 0
          end)
    RETURN (Vint (Int.repr r))
    SEP (state_rep sh s outp outlen outcnt inp (Zlength bytes) incnt' bitbuf' bitcnt' eof';
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         data_at shh (Tstruct _huffman noattr) (cnt, sym) h;
         data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf lens))) cnt;
         data_at shh (tarray tshort (Zlength syms)) syms sym).

(* a Huffman table construct() built from lens, as decode() reads it *)
Definition htable (shh : share) (h cnt sym : val) (lens : list Z) : mpred :=
  EX syms : list val,
    !! (Zlength lens <= 320 /\ Forall (fun x => 0 <= x <= 15) lens /\
        Zlength syms = Zlength lens /\ table lens syms) &&
    (data_at shh (Tstruct _huffman noattr) (cnt, sym) h *
     data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf lens))) cnt *
     data_at shh (tarray tshort (Zlength syms)) syms sym)%logic.

(** * bits() and stored() *)

Definition bits_spec :=
 DECLARE _bits
  WITH sh : share, shi : share, s : val, outp : val, outlen : Z, outcnt : Z,
       inp : val, bytes : list Z, incnt : Z, bitbuf : Z, bitcnt : Z, need : Z
  PRE [ tptr (Tstruct _state noattr), tint ]
    PROP (writable_share sh; readable_share shi; bytes_ok bytes; Zlength bytes <= Int.max_signed;
          buf_ok bytes incnt bitbuf bitcnt; 0 <= need <= 13)
    PARAMS (s; Vint (Int.repr need))
    SEP (state_rep sh s outp outlen outcnt inp (Zlength bytes) incnt bitbuf bitcnt 0;
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp)
  POST [ tint ]
    EX r : Z, EX incnt' : Z, EX bitbuf' : Z, EX bitcnt' : Z, EX eof' : Z,
    PROP (if 8 * incnt - bitcnt + need <=? nbits bytes
          then r = lsbZ bytes (8 * incnt - bitcnt) (Z.to_nat need) /\
               (8 * incnt' - bitcnt' = 8 * incnt - bitcnt + need)%Z /\
               buf_ok bytes incnt' bitbuf' bitcnt' /\ eof' = 0
          else eof' = 1 /\ r = 0)
    RETURN (Vint (Int.repr r))
    SEP (state_rep sh s outp outlen outcnt inp (Zlength bytes) incnt' bitbuf' bitcnt' eof';
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp).

Definition stored_spec :=
 DECLARE _stored
  WITH sh : share, shi : share, sho : share, s : val, outp : val, outlen : Z, out : list Z,
       wr : bool, inp : val, bytes : list Z, incnt : Z, bitbuf : Z, bitcnt : Z
  PRE [ tptr (Tstruct _state noattr) ]
    PROP (writable_share sh; readable_share shi; writable_share sho; bytes_ok bytes;
          sizes_ok wr outp (Zlength bytes) outlen; out_ok wr outlen out;
          buf_ok bytes incnt bitbuf bitcnt; room wr bytes out (8 * incnt - bitcnt))
    PARAMS (s)
    SEP (state_rep sh s outp outlen (Zlength out) inp (Zlength bytes) incnt bitbuf bitcnt 0;
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         outbuf wr sho outp outlen out)
  POST [ tint ]
    EX r : Z, EX out' : list Z, EX incnt' : Z, EX bitbuf' : Z, EX bitcnt' : Z, EX eof' : Z,
    PROP (Int.min_signed <= r <= Int.max_signed; out_ok wr outlen out';
          match storedZ bytes (8 * incnt - bitcnt) with
          | Some (bs, q) =>
              if fits wr outlen (out ++ bs)
              then r = 0 /\ out' = out ++ bs /\ (8 * incnt' - bitcnt' = q)%Z /\
                   buf_ok bytes incnt' bitbuf' bitcnt' /\ eof' = 0 /\ room wr bytes out' q
              else r <> 0
          | None => r <> 0
          end)
    RETURN (Vint (Int.repr r))
    SEP (state_rep sh s outp outlen (Zlength out') inp (Zlength bytes) incnt' bitbuf' bitcnt' eof';
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         outbuf wr sho outp outlen out').

(** * codes(), fixed() and dynamic(): one compressed block *)

(* the result of a block's data: Some when the C must return 0 *)
Definition block_ok (wr : bool) (outlen : Z) (res : option (list Z * Z)) (r : Z) (out' : list Z)
    (bytes : list Z) (incnt' bitbuf' bitcnt' eof' : Z) : Prop :=
  match res with
  | Some (o, q) =>
      if fits wr outlen o
      then r = 0 /\ out' = o /\ (8 * incnt' - bitcnt' = q)%Z /\ buf_ok bytes incnt' bitbuf' bitcnt' /\
           eof' = 0 /\ room wr bytes out' q
      else r <> 0
  | None => r <> 0
  end.

Definition codes_spec :=
 DECLARE _codes
  WITH sh : share, shi : share, sho : share, shh : share, s : val, outp : val, outlen : Z,
       out : list Z, wr : bool, inp : val, bytes : list Z, incnt : Z, bitbuf : Z, bitcnt : Z,
       hl : val, lt : val * val, lit : list Z, hd : val, dt : val * val, dist : list Z,
       gv : globals
  PRE [ tptr (Tstruct _state noattr), tptr (Tstruct _huffman noattr), tptr (Tstruct _huffman noattr) ]
    PROP (writable_share sh; readable_share shi; writable_share sho; readable_share shh;
          bytes_ok bytes; sizes_ok wr outp (Zlength bytes) outlen; out_ok wr outlen out;
          buf_ok bytes incnt bitbuf bitcnt; room wr bytes out (8 * incnt - bitcnt); Zlength dist <= 30)
    PARAMS (s; hl; hd) GLOBALS (gv)
    SEP (state_rep sh s outp outlen (Zlength out) inp (Zlength bytes) incnt bitbuf bitcnt 0;
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         outbuf wr sho outp outlen out; htable shh hl (fst lt) (snd lt) lit; htable shh hd (fst dt) (snd dt) dist; codes_tables gv)
  POST [ tint ]
    EX r : Z, EX out' : list Z, EX incnt' : Z, EX bitbuf' : Z, EX bitcnt' : Z, EX eof' : Z,
    PROP (Int.min_signed <= r <= Int.max_signed; out_ok wr outlen out';
          block_ok wr outlen (symsF lit dist bytes (8 * incnt - bitcnt) out) r out' bytes
            incnt' bitbuf' bitcnt' eof')
    RETURN (Vint (Int.repr r))
    SEP (state_rep sh s outp outlen (Zlength out') inp (Zlength bytes) incnt' bitbuf' bitcnt' eof';
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         outbuf wr sho outp outlen out'; htable shh hl (fst lt) (snd lt) lit; htable shh hd (fst dt) (snd dt) dist; codes_tables gv).

(* a block with fixed codes: the spec's inflateSyms (code fixedLit) (code fixedDist) *)
Definition fixed_spec :=
 DECLARE _fixed
  WITH sh : share, shi : share, sho : share, s : val, outp : val, outlen : Z, out : list Z,
       wr : bool, inp : val, bytes : list Z, incnt : Z, bitbuf : Z, bitcnt : Z, gv : globals
  PRE [ tptr (Tstruct _state noattr) ]
    PROP (writable_share sh; readable_share shi; writable_share sho; bytes_ok bytes;
          sizes_ok wr outp (Zlength bytes) outlen; out_ok wr outlen out;
          buf_ok bytes incnt bitbuf bitcnt; room wr bytes out (8 * incnt - bitcnt))
    PARAMS (s) GLOBALS (gv)
    SEP (state_rep sh s outp outlen (Zlength out) inp (Zlength bytes) incnt bitbuf bitcnt 0;
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         outbuf wr sho outp outlen out; codes_tables gv)
  POST [ tint ]
    EX r : Z, EX out' : list Z, EX incnt' : Z, EX bitbuf' : Z, EX bitcnt' : Z, EX eof' : Z,
    PROP (Int.min_signed <= r <= Int.max_signed; out_ok wr outlen out';
          block_ok wr outlen
            (symsF VPuff.Inflate.fixedLitZ VPuff.Inflate.fixedDistZ bytes (8 * incnt - bitcnt) out)
            r out' bytes incnt' bitbuf' bitcnt' eof')
    RETURN (Vint (Int.repr r))
    SEP (state_rep sh s outp outlen (Zlength out') inp (Zlength bytes) incnt' bitbuf' bitcnt' eof';
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         outbuf wr sho outp outlen out'; codes_tables gv).

(* a block with dynamic codes: the spec's dynHeader, and puff fails where it
   sets the zlib flag off; then inflateSyms with the codes it read *)
Definition dynamic_spec :=
 DECLARE _dynamic
  WITH sh : share, shi : share, sho : share, s : val, outp : val, outlen : Z, out : list Z,
       wr : bool, inp : val, bytes : list Z, incnt : Z, bitbuf : Z, bitcnt : Z, gv : globals
  PRE [ tptr (Tstruct _state noattr) ]
    PROP (writable_share sh; readable_share shi; writable_share sho; bytes_ok bytes;
          sizes_ok wr outp (Zlength bytes) outlen; out_ok wr outlen out;
          buf_ok bytes incnt bitbuf bitcnt; room wr bytes out (8 * incnt - bitcnt))
    PARAMS (s) GLOBALS (gv)
    SEP (state_rep sh s outp outlen (Zlength out) inp (Zlength bytes) incnt bitbuf bitcnt 0;
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         outbuf wr sho outp outlen out; all_tables gv)
  POST [ tint ]
    EX r : Z, EX out' : list Z, EX incnt' : Z, EX bitbuf' : Z, EX bitcnt' : Z, EX eof' : Z,
    PROP (Int.min_signed <= r <= Int.max_signed; out_ok wr outlen out';
          block_ok wr outlen
            (match dynHeaderZ bytes (8 * incnt - bitcnt) with
             | Some (lit, dist, q, true) => symsF lit dist bytes q out
             | _ => None
             end)
            r out' bytes incnt' bitbuf' bitcnt' eof')
    RETURN (Vint (Int.repr r))
    SEP (state_rep sh s outp outlen (Zlength out') inp (Zlength bytes) incnt' bitbuf' bitcnt' eof';
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         outbuf wr sho outp outlen out'; all_tables gv).

(** * puff() *)

Definition puff_spec :=
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
          match inflateZ bytes with
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

Definition Gprog : funspecs :=
  [bits_spec; stored_spec; decode_spec; construct_spec; codes_spec; fixed_spec; dynamic_spec;
   puff_spec].
