(* puff's fixed(): build the fixed literal/length and distance tables, then
   codes(). VST proof of Spec_puff.fixed_spec. *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model VPuff.Spec_puff VPuff.Inflate VPuff.CodesLemmas.
Open Scope Z_scope.

(* lengths[] while the literal/length code lengths are written *)
Definition fillv (F : list Z) (i : Z) : list val :=
  map Vint (map Int.repr (sublist 0 i F)) ++ Zrepeat Vundef (288 - i).

(* lengths[] while the first 30 are overwritten with 5 *)
Definition fill2 (i : Z) : list val :=
  map Vint (map Int.repr (Zrepeat 5 i ++ sublist i 288 fixedLitZ)).

Lemma fixedLit_len : Zlength fixedLitZ = 288.
Proof. reflexivity. Qed.

Lemma fixedLit_8_0 i : 0 <= i < 144 -> Znth i fixedLitZ = 8.
Proof. intros. unfold fixedLitZ. list_solve. Qed.
Lemma fixedLit_9_144 i : 144 <= i < 256 -> Znth i fixedLitZ = 9.
Proof. intros. unfold fixedLitZ. list_solve. Qed.
Lemma fixedLit_7_256 i : 256 <= i < 280 -> Znth i fixedLitZ = 7.
Proof. intros. unfold fixedLitZ. list_solve. Qed.
Lemma fixedLit_8_280 i : 280 <= i < 288 -> Znth i fixedLitZ = 8.
Proof. intros. unfold fixedLitZ. list_solve. Qed.

Lemma fill_step F i c : Zlength F = 288 -> 0 <= i < 288 -> Znth i F = c ->
  upd_Znth i (fillv F i) (Vint (Int.repr c)) = fillv F (i + 1).
Proof. intros. subst c. unfold fillv. list_solve. Qed.

Lemma fill2_step i : 0 <= i < 30 -> upd_Znth i (fill2 i) (Vint (Int.repr 5)) = fill2 (i + 1).
Proof. intros. unfold fill2. pose proof fixedLit_len. list_solve. Qed.

Lemma lens_ok (l : list Z) : forallb (fun x => andb (0 <=? x) (x <=? 15)) l = true ->
  Forall (fun x => 0 <= x <= 15) l.
Proof.
  intros H. apply Forall_forall. intros x Hx. rewrite forallb_forall in H.
  specialize (H x Hx). apply andb_prop in H. lia.
Qed.

Lemma fixedLit_ok : Forall (fun x => 0 <= x <= 15) fixedLitZ.
Proof. apply lens_ok. reflexivity. Qed.

(* puff's distance code lengths (30 of them; the spec's fixedDistZ has 32) *)
Definition dist30 : list Z := Zrepeat 5 30.

Lemma dist30_len : Zlength dist30 = 30.
Proof. reflexivity. Qed.

Lemma fixedDist_ok : Forall (fun x => 0 <= x <= 15) dist30.
Proof. apply lens_ok. reflexivity. Qed.

Lemma fixedLit_kraft : krZ (countF (countsOf fixedLitZ)) 15 = 32768.
Proof. vm_compute. reflexivity. Qed.

Lemma fixedDist_kraft : krZ (countF (countsOf dist30)) 15 = 30720.
Proof. vm_compute. reflexivity. Qed.

Lemma fill2_0 : fill2 0 = map Vint (map Int.repr fixedLitZ).
Proof. unfold fill2. rewrite sublist_same by reflexivity. reflexivity. Qed.

Lemma fill2_30 : fill2 30 =
  map Vint (map Int.repr (Zrepeat 5 30)) ++ map Vint (map Int.repr (sublist 30 288 fixedLitZ)).
Proof. unfold fill2. rewrite !map_app. reflexivity. Qed.

Lemma htable_fold shh h lens cnt sym syms n :
  Zlength lens <= 320 -> Forall (fun x => 0 <= x <= 15) lens ->
  Zlength syms = Zlength lens -> n = Zlength lens -> table lens syms ->
  (data_at shh (Tstruct _huffman noattr) (cnt, sym) h *
   data_at shh (tarray tshort 16) (map Vint (map Int.repr (countsOf lens))) cnt *
   data_at shh (tarray tshort n) syms sym)%logic |-- htable shh h cnt sym lens.
Proof. intros. subst n. unfold htable. Exists syms. rewrite H1. entailer!. Qed.

Lemma body_fixed : semax_body Vprog Gprog f_fixed fixed_spec.
Proof.
  start_function.
  forward. forward. forward. forward.
  freeze [1;2;3;4;5;6;7;8;9;10] FR.
  forward_for_simple_bound 144
    (EX i : Z,
     PROP ()
     LOCAL (temp _s s; gvars gv; lvar _lengths (tarray tshort 288) v_lengths; lvar _lencode (Tstruct _huffman noattr) v_lencode; lvar _distcode (Tstruct _huffman noattr) v_distcode; lvar _distsym (tarray tshort 30) v_distsym; lvar _distcnt (tarray tshort 16) v_distcnt; lvar _lensym (tarray tshort 288) v_lensym; lvar _lencnt (tarray tshort 16) v_lencnt)
     SEP (data_at Tsh (tarray tshort 288) (fillv fixedLitZ i) v_lengths; FRZL FR))%assert.
  { entailer!. }
  { forward. rewrite fill_step with (c := 8) by first [apply fixedLit_len | lia | (apply fixedLit_8_0; lia)]. entailer!. }
  forward_loop (EX i : Z,
     PROP (144 <= i <= 256)
     LOCAL (temp _symbol (Vint (Int.repr i)); temp _s s; gvars gv; lvar _lengths (tarray tshort 288) v_lengths; lvar _lencode (Tstruct _huffman noattr) v_lencode; lvar _distcode (Tstruct _huffman noattr) v_distcode; lvar _distsym (tarray tshort 30) v_distsym; lvar _distcnt (tarray tshort 16) v_distcnt; lvar _lensym (tarray tshort 288) v_lensym; lvar _lencnt (tarray tshort 16) v_lencnt)
     SEP (data_at Tsh (tarray tshort 288) (fillv fixedLitZ i) v_lengths; FRZL FR))%assert
  continue: (EX i : Z,
     PROP (144 <= i < 256)
     LOCAL (temp _symbol (Vint (Int.repr i)); temp _s s; gvars gv; lvar _lengths (tarray tshort 288) v_lengths; lvar _lencode (Tstruct _huffman noattr) v_lencode; lvar _distcode (Tstruct _huffman noattr) v_distcode; lvar _distsym (tarray tshort 30) v_distsym; lvar _distcnt (tarray tshort 16) v_distcnt; lvar _lensym (tarray tshort 288) v_lensym; lvar _lencnt (tarray tshort 16) v_lencnt)
     SEP (data_at Tsh (tarray tshort 288) (fillv fixedLitZ (i + 1)) v_lengths; FRZL FR))%assert
  break: (PROP ()
     LOCAL (temp _symbol (Vint (Int.repr 256)); temp _s s; gvars gv; lvar _lengths (tarray tshort 288) v_lengths; lvar _lencode (Tstruct _huffman noattr) v_lencode; lvar _distcode (Tstruct _huffman noattr) v_distcode; lvar _distsym (tarray tshort 30) v_distsym; lvar _distcnt (tarray tshort 16) v_distcnt; lvar _lensym (tarray tshort 288) v_lensym; lvar _lencnt (tarray tshort 16) v_lencnt)
     SEP (data_at Tsh (tarray tshort 288) (fillv fixedLitZ 256) v_lengths; FRZL FR)).
  { Exists 144. entailer!. }
  { Intros i. forward_if.
    - forward. rewrite fill_step with (c := 9) by first [apply fixedLit_len | lia | (apply fixedLit_9_144; lia)].
      Exists i. entailer!.
    - forward. assert (i = 256) by lia. subst i. entailer!. }
  { Intros i. forward. Exists (i + 1). entailer!. }
  forward_loop (EX i : Z,
     PROP (256 <= i <= 280)
     LOCAL (temp _symbol (Vint (Int.repr i)); temp _s s; gvars gv; lvar _lengths (tarray tshort 288) v_lengths; lvar _lencode (Tstruct _huffman noattr) v_lencode; lvar _distcode (Tstruct _huffman noattr) v_distcode; lvar _distsym (tarray tshort 30) v_distsym; lvar _distcnt (tarray tshort 16) v_distcnt; lvar _lensym (tarray tshort 288) v_lensym; lvar _lencnt (tarray tshort 16) v_lencnt)
     SEP (data_at Tsh (tarray tshort 288) (fillv fixedLitZ i) v_lengths; FRZL FR))%assert
  continue: (EX i : Z,
     PROP (256 <= i < 280)
     LOCAL (temp _symbol (Vint (Int.repr i)); temp _s s; gvars gv; lvar _lengths (tarray tshort 288) v_lengths; lvar _lencode (Tstruct _huffman noattr) v_lencode; lvar _distcode (Tstruct _huffman noattr) v_distcode; lvar _distsym (tarray tshort 30) v_distsym; lvar _distcnt (tarray tshort 16) v_distcnt; lvar _lensym (tarray tshort 288) v_lensym; lvar _lencnt (tarray tshort 16) v_lencnt)
     SEP (data_at Tsh (tarray tshort 288) (fillv fixedLitZ (i + 1)) v_lengths; FRZL FR))%assert
  break: (PROP ()
     LOCAL (temp _symbol (Vint (Int.repr 280)); temp _s s; gvars gv; lvar _lengths (tarray tshort 288) v_lengths; lvar _lencode (Tstruct _huffman noattr) v_lencode; lvar _distcode (Tstruct _huffman noattr) v_distcode; lvar _distsym (tarray tshort 30) v_distsym; lvar _distcnt (tarray tshort 16) v_distcnt; lvar _lensym (tarray tshort 288) v_lensym; lvar _lencnt (tarray tshort 16) v_lencnt)
     SEP (data_at Tsh (tarray tshort 288) (fillv fixedLitZ 280) v_lengths; FRZL FR)).
  { Exists 256. entailer!. }
  { Intros i. forward_if.
    - forward. rewrite fill_step with (c := 7) by first [apply fixedLit_len | lia | (apply fixedLit_7_256; lia)].
      Exists i. entailer!.
    - forward. assert (i = 280) by lia. subst i. entailer!. }
  { Intros i. forward. Exists (i + 1). entailer!. }
  forward_loop (EX i : Z,
     PROP (280 <= i <= 288)
     LOCAL (temp _symbol (Vint (Int.repr i)); temp _s s; gvars gv; lvar _lengths (tarray tshort 288) v_lengths; lvar _lencode (Tstruct _huffman noattr) v_lencode; lvar _distcode (Tstruct _huffman noattr) v_distcode; lvar _distsym (tarray tshort 30) v_distsym; lvar _distcnt (tarray tshort 16) v_distcnt; lvar _lensym (tarray tshort 288) v_lensym; lvar _lencnt (tarray tshort 16) v_lencnt)
     SEP (data_at Tsh (tarray tshort 288) (fillv fixedLitZ i) v_lengths; FRZL FR))%assert
  continue: (EX i : Z,
     PROP (280 <= i < 288)
     LOCAL (temp _symbol (Vint (Int.repr i)); temp _s s; gvars gv; lvar _lengths (tarray tshort 288) v_lengths; lvar _lencode (Tstruct _huffman noattr) v_lencode; lvar _distcode (Tstruct _huffman noattr) v_distcode; lvar _distsym (tarray tshort 30) v_distsym; lvar _distcnt (tarray tshort 16) v_distcnt; lvar _lensym (tarray tshort 288) v_lensym; lvar _lencnt (tarray tshort 16) v_lencnt)
     SEP (data_at Tsh (tarray tshort 288) (fillv fixedLitZ (i + 1)) v_lengths; FRZL FR))%assert
  break: (PROP ()
     LOCAL (temp _symbol (Vint (Int.repr 288)); temp _s s; gvars gv; lvar _lengths (tarray tshort 288) v_lengths; lvar _lencode (Tstruct _huffman noattr) v_lencode; lvar _distcode (Tstruct _huffman noattr) v_distcode; lvar _distsym (tarray tshort 30) v_distsym; lvar _distcnt (tarray tshort 16) v_distcnt; lvar _lensym (tarray tshort 288) v_lensym; lvar _lencnt (tarray tshort 16) v_lencnt)
     SEP (data_at Tsh (tarray tshort 288) (fillv fixedLitZ 288) v_lengths; FRZL FR)).
  { Exists 280. entailer!. }
  { Intros i. forward_if.
    - forward. rewrite fill_step with (c := 8) by first [apply fixedLit_len | lia | (apply fixedLit_8_280; lia)].
      Exists i. entailer!.
    - forward. assert (i = 288) by lia. subst i. entailer!. }
  { Intros i. forward. Exists (i + 1). entailer!. }
  thaw FR.
  replace (fillv fixedLitZ 288) with (map Vint (map Int.repr fixedLitZ))
    by (unfold fillv; rewrite sublist_same by reflexivity; list_solve).
  pose proof fixedLit_ok. pose proof fixedLit_kraft.
  forward_call (Tsh, Tsh, v_lencode, v_lencnt, v_lensym, v_lengths, fixedLitZ).
  { rewrite fixedLit_len. lia. }
  Intros vret. destruct vret as [r1 syms1]. cbn [fst snd] in *.
  match goal with H : r1 < 0 <-> _ |- _ => rewrite fixedLit_kraft in H;
    assert (Hr1 : 0 <= r1) by (destruct (Z_lt_le_dec r1 0) as [Hn|]; [apply H in Hn; lia | auto]) end.
  match goal with H : 0 <= r1 -> table _ _ |- _ => pose proof (H Hr1) as Htab1 end.
  assert_PROP (Zlength syms1 = 288) as Hs1 by (rewrite fixedLit_len in *; entailer!).
  rewrite fixedLit_len.
  freeze [0;1;2;4;5;6;7;8;9;10] FR.
  rewrite <- fill2_0.
  forward_for_simple_bound 30
    (EX i : Z,
     PROP ()
     LOCAL (temp _s s; gvars gv; lvar _lengths (tarray tshort 288) v_lengths; lvar _lencode (Tstruct _huffman noattr) v_lencode; lvar _distcode (Tstruct _huffman noattr) v_distcode; lvar _distsym (tarray tshort 30) v_distsym; lvar _distcnt (tarray tshort 16) v_distcnt; lvar _lensym (tarray tshort 288) v_lensym; lvar _lencnt (tarray tshort 16) v_lencnt)
     SEP (data_at Tsh (tarray tshort 288) (fill2 i) v_lengths; FRZL FR))%assert.
  { entailer!. }
  { forward. rewrite fill2_step by lia. entailer!. }
  thaw FR.
  rewrite fill2_30.
  change (Zrepeat 5 30) with dist30.
  assert (Hz1 : Zlength (map Vint (map Int.repr dist30)) = 30) by reflexivity.
  assert (Hz2 : Zlength (map Vint (map Int.repr (sublist 30 288 fixedLitZ))) = 288 - 30) by reflexivity.
  rewrite (split2_data_at_Tarray_app 30 288 Tsh tshort _ _ v_lengths Hz1 Hz2).
  Intros.
  freeze [1;2;3;4;8;9;10;11] FR2.
  pose proof fixedDist_ok. pose proof fixedDist_kraft.
  forward_call (Tsh, Tsh, v_distcode, v_distcnt, v_distsym, v_lengths, dist30).
  { rewrite dist30_len. lia. }
  Intros vret. destruct vret as [r2 syms2]. cbn [fst snd] in *.
  match goal with H : r2 < 0 <-> _ |- _ => rewrite fixedDist_kraft in H;
    assert (Hr2 : 0 <= r2) by (destruct (Z_lt_le_dec r2 0) as [Hn|]; [apply H in Hn; lia | auto]) end.
  match goal with H : 0 <= r2 -> table _ _ |- _ => pose proof (H Hr2) as Htab2 end.
  assert_PROP (Zlength syms2 = 30) as Hs2 by (rewrite dist30_len in *; entailer!).
  rewrite dist30_len.
  thaw FR2.
  sep_apply (htable_fold Tsh v_lencode fixedLitZ v_lencnt v_lensym syms1 288
    ltac:(rewrite fixedLit_len; lia) fixedLit_ok ltac:(rewrite fixedLit_len; lia)
    ltac:(rewrite fixedLit_len; lia) Htab1).
  sep_apply (htable_fold Tsh v_distcode dist30 v_distcnt v_distsym syms2 30
    ltac:(rewrite dist30_len; lia) fixedDist_ok ltac:(rewrite dist30_len; lia)
    ltac:(rewrite dist30_len; lia) Htab2).
  freeze [2;3] FR3.
  forward_call (sh, shi, sho, Tsh, s, outp, outlen, out, wr, inp, bytes, incnt, bitbuf, bitcnt,
                v_lencode, (v_lencnt, v_lensym), fixedLitZ, v_distcode, (v_distcnt, v_distsym), dist30, gv).
  all: try (rewrite ?dist30_len; lia).
  { cbn [fst snd]. cancel. }
  Intros vret. destruct vret as [[[[[r out'] ic] bb] bc] ef]. cbn [fst snd] in *.
  thaw FR3.
  unfold htable. Intros ss1 ss2.
  rewrite fixedLit_len, dist30_len in *.
  match goal with H : Zlength ss1 = 288 |- _ => rewrite H end.
  match goal with H : Zlength ss2 = 30 |- _ => rewrite H end.
  gather_SEP 10 11.
  rewrite <- (split2_data_at_Tarray_app 30 288 Tsh tshort _ _ v_lengths Hz1 Hz2).
  forward.
  Exists r out' ic bb bc ef. entailer!.
  match goal with H : block_ok _ _ _ _ _ _ _ _ _ _ |- _ =>
    unfold dist30 in H; rewrite symsF_dist30 in H; exact H end.
Qed.
