(* puff's decode() computes decodeZ (Model.v), and so (Main.v) the Lean spec's
   decodeSym: VST proof of Spec_puff.decode_spec. *)
Require Import VST.floyd.proofauto.
Require Import VPuff.puff VPuff.Model VPuff.Spec_puff VPuff.DecodeLemmas VPuff.Main.
Require VPuff.Bridge.
Open Scope Z_scope.

(* decode() on any tables: the model decodeZ (Model.v) *)
Definition decode_model_spec :=
 DECLARE _decode
  WITH sh : share, shi : share, shh : share, s : val, outp : val, outlen : Z, outcnt : Z,
       inp : val, bytes : list Z, incnt : Z, bitbuf : Z, bitcnt : Z, h : val, cnt : val, sym : val,
       counts : list Z, syms : list val
  PRE [ tptr (Tstruct _state noattr), tptr (Tstruct _huffman noattr) ]
    PROP (writable_share sh; readable_share shi; readable_share shh;
          Forall (fun b => 0 <= b < 256) bytes; Zlength bytes <= Int.max_signed;
          buf_ok bytes incnt bitbuf bitcnt;
          Zlength counts = 16; Forall (fun c => 0 <= c <= 320) counts;
          ncodes counts <= Zlength syms;
          forall j, 0 <= j < ncodes counts ->
            exists v, Znth j syms = Vint (Int.repr v) /\ 0 <= v <= Int.max_signed)
    PARAMS (s; h)
    SEP (state_rep sh s outp outlen outcnt inp (Zlength bytes) incnt bitbuf bitcnt 0;
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         data_at shh (Tstruct _huffman noattr) (cnt, sym) h;
         data_at shh (tarray tshort 16) (map Vint (map Int.repr counts)) cnt;
         data_at shh (tarray tshort (Zlength syms)) syms sym)
  POST [ tint ]
    EX r : Z, EX incnt' : Z, EX bitbuf' : Z, EX bitcnt' : Z, EX eof' : Z,
    PROP (Int.min_signed <= r <= Int.max_signed;
          match decodeZ (countF counts) (symF syms (ncodes counts)) (bitZ bytes)
                  (8 * Zlength bytes) (8 * incnt - bitcnt) with
          | Some (v, p') => r = v /\ (8 * incnt' - bitcnt' = p')%Z /\ buf_ok bytes incnt' bitbuf' bitcnt' /\
                            eof' = 0
          | None => r < 0
          end)
    RETURN (Vint (Int.repr r))
    SEP (state_rep sh s outp outlen outcnt inp (Zlength bytes) incnt' bitbuf' bitcnt' eof';
         data_at shi (tarray tuchar (Zlength bytes)) (map Vint (map Int.repr bytes)) inp;
         data_at shh (Tstruct _huffman noattr) (cnt, sym) h;
         data_at shh (tarray tshort 16) (map Vint (map Int.repr counts)) cnt;
         data_at shh (tarray tshort (Zlength syms)) syms sym).

Lemma body_decode_model : semax_body Vprog Gprog f_decode decode_model_spec.
Proof.
  start_function.
  match goal with H : buf_ok _ _ _ _ |- _ => destruct H as (Hinc & Hbc & Hinc0 & Hbuf) end.
  set (inlen := Zlength bytes) in *.
  set (p0 := 8 * incnt - bitcnt).
  set (cF := countF counts).
  set (sF := symF syms (ncodes counts)).
  set (target := decodeZ cF sF (bitZ bytes) (8 * inlen) p0).
  unfold state_rep.
  forward. (* bitbuf = s->bitbuf *)
  forward. (* left = s->bitcnt *)
  forward. forward. forward. forward. forward. (* code = first = index = 0 *)
  forward. (* len = 1 *)
  forward. (* t12 = h->count *)
  forward. (* next = t12 + 1 *)
  assert_PROP (field_compatible (tarray tshort 16) [] cnt) as Hfc by entailer!.
  forward_loop
    (EX len : Z, EX code : Z, EX first : Z, EX index : Z, EX inc : Z,
     PROP (1 <= len <= 16; 0 <= first <= code; code < 2 ^ len; Z.even code = true;
           index = offsZ cF (Z.to_nat len);
           incnt <= inc <= inlen;
           0 <= 8 * inc - (p0 + len - 1) <= 8;
           goZ cF sF (bitZ bytes) (8 * inlen) p0 (Z.to_nat (16 - len)) len code first index = target)
     LOCAL (temp _len (Vint (Int.repr len)); temp _code (Vint (Int.repr code));
            temp _first (Vint (Int.repr first)); temp _index (Vint (Int.repr index));
            temp _bitbuf (Vint (Int.repr (bufval bytes inc (8 * inc - (p0 + len - 1)))));
            temp _left (Vint (Int.repr (Z.min (8 * inc - (p0 + len - 1)) (16 - len))));
            temp _next (offset_val (2 * len) cnt); temp _s s; temp _h h)
     SEP (data_at sh (Tstruct _state noattr)
            (outp, (Vint (Int.repr outlen), (Vint (Int.repr outcnt), (inp, (Vint (Int.repr inlen), (Vint (Int.repr inc), (Vint (Int.repr bitbuf), (Vint (Int.repr bitcnt), Vint (Int.repr 0))))))))) s;
          data_at shi (tarray tuchar inlen) (map Vint (map Int.repr bytes)) inp;
          data_at shh (Tstruct _huffman noattr) (cnt, sym) h;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr counts)) cnt;
          data_at shh (tarray tshort (Zlength syms)) syms sym))%assert
  break:
    (EX inc : Z,
     PROP (target = None; incnt <= inc <= inlen)
     LOCAL (temp _s s; temp _h h)
     SEP (data_at sh (Tstruct _state noattr)
            (outp, (Vint (Int.repr outlen), (Vint (Int.repr outcnt), (inp, (Vint (Int.repr inlen), (Vint (Int.repr inc), (Vint (Int.repr bitbuf), (Vint (Int.repr bitcnt), Vint (Int.repr 0))))))))) s;
          data_at shi (tarray tuchar inlen) (map Vint (map Int.repr bytes)) inp;
          data_at shh (Tstruct _huffman noattr) (cnt, sym) h;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr counts)) cnt;
          data_at shh (tarray tshort (Zlength syms)) syms sym))%assert.
  - (* the invariant holds at the start *)
    Exists 1 0 0 0 incnt. entailer!.
    replace (8 * incnt - (p0 + 1 - 1)) with bitcnt by (unfold p0; lia).
    split; [unfold bufval; reflexivity | f_equal; f_equal; lia].
  - (* the loop body *)
    clear Hbuf. Intros len code first index inc.
    forward_loop
    (EX len : Z, EX code : Z, EX first : Z, EX index : Z, EX inc : Z,
     PROP (1 <= len <= 16; 0 <= first <= code; code < 2 ^ len; Z.even code = true;
           index = offsZ cF (Z.to_nat len);
           incnt <= inc <= inlen;
           0 <= 8 * inc - (p0 + len - 1) <= 8;
           goZ cF sF (bitZ bytes) (8 * inlen) p0 (Z.to_nat (16 - len)) len code first index = target)
     LOCAL (temp _len (Vint (Int.repr len)); temp _code (Vint (Int.repr code));
            temp _first (Vint (Int.repr first)); temp _index (Vint (Int.repr index));
            temp _bitbuf (Vint (Int.repr (bufval bytes inc (8 * inc - (p0 + len - 1)))));
            temp _left (Vint (Int.repr (Z.min (8 * inc - (p0 + len - 1)) (16 - len))));
            temp _next (offset_val (2 * len) cnt); temp _s s; temp _h h)
     SEP (data_at sh (Tstruct _state noattr)
            (outp, (Vint (Int.repr outlen), (Vint (Int.repr outcnt), (inp, (Vint (Int.repr inlen), (Vint (Int.repr inc), (Vint (Int.repr bitbuf), (Vint (Int.repr bitcnt), Vint (Int.repr 0))))))))) s;
          data_at shi (tarray tuchar inlen) (map Vint (map Int.repr bytes)) inp;
          data_at shh (Tstruct _huffman noattr) (cnt, sym) h;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr counts)) cnt;
          data_at shh (tarray tshort (Zlength syms)) syms sym))%assert
    break:
    (EX len : Z, EX code : Z, EX first : Z, EX index : Z, EX inc : Z,
     PROP (1 <= len <= 16; 0 <= first <= code; code < 2 ^ len; Z.even code = true;
           index = offsZ cF (Z.to_nat len);
           incnt <= inc <= inlen;
           0 <= 8 * inc - (p0 + len - 1) <= 8;
           goZ cF sF (bitZ bytes) (8 * inlen) p0 (Z.to_nat (16 - len)) len code first index = target;
           Z.min (8 * inc - (p0 + len - 1)) (16 - len) = 0)
     LOCAL (temp _len (Vint (Int.repr len)); temp _code (Vint (Int.repr code));
            temp _first (Vint (Int.repr first)); temp _index (Vint (Int.repr index));
            temp _bitbuf (Vint (Int.repr (bufval bytes inc (8 * inc - (p0 + len - 1)))));
            temp _left (Vint (Int.repr (-1)));
            temp _next (offset_val (2 * len) cnt); temp _s s; temp _h h)
     SEP (data_at sh (Tstruct _state noattr)
            (outp, (Vint (Int.repr outlen), (Vint (Int.repr outcnt), (inp, (Vint (Int.repr inlen), (Vint (Int.repr inc), (Vint (Int.repr bitbuf), (Vint (Int.repr bitcnt), Vint (Int.repr 0))))))))) s;
          data_at shi (tarray tuchar inlen) (map Vint (map Int.repr bytes)) inp;
          data_at shh (Tstruct _huffman noattr) (cnt, sym) h;
          data_at shh (tarray tshort 16) (map Vint (map Int.repr counts)) cnt;
          data_at shh (tarray tshort (Zlength syms)) syms sym))%assert.
    { Exists len code first index inc. entailer!. }
    { (* the inner loop body *)
      clear dependent len. clear dependent code. clear dependent first. clear dependent index. clear dependent inc.
      Intros len code first index inc.
      forward. forward.
      forward_if.
      2:{ (* left was 0: leave the inner loop *)
          match goal with H : Int.repr (Z.min ?a ?b) = Int.zero |- _ =>
            assert (Hm0 : Z.min a b = 0) by
              (apply repr_inj_signed; [rep_lia | rep_lia | exact H]) end.
          forward. Exists len code first index inc. entailer!.
          rewrite Hm0; reflexivity. }
      (* a bit is left in bitbuf: r >= 1 and len <= 15 *)
      assert (Hr : 1 <= 8 * inc - (p0 + len - 1) /\ len <= 15).
      { destruct (Z.min_spec (8 * inc - (p0 + len - 1)) (16 - len)) as [[_ E]|[_ E]];
          rewrite E in *; split; try lia;
          (assert (Z.min (8 * inc - (p0 + len - 1)) (16 - len) <> 0) by (intro Hc; rewrite Hc in *; contradiction); lia). }
      set (q := p0 + len - 1) in *.
      set (r := 8 * inc - q) in *.
      assert (Hbv := bufval_nonneg bytes inc r H ltac:(lia) ltac:(lia)).
      assert (Hbit := bufval_bit bytes inc q ltac:(unfold q, p0; lia) ltac:(fold r; lia)).
      fold r in Hbit.
      set (b := if bitZ bytes q then 1 else 0) in *.
      assert (Hb01 : b = 0 \/ b = 1) by (unfold b; destruct (bitZ bytes q); auto).
      forward. (* code |= bitbuf & 1 *)
      forward. (* bitbuf >>= 1 *)
      forward. forward. (* t4 = next; next = t4 + 1 *)
      assert (Hnext : offset_val (2 * len) cnt = field_address (tarray tshort 16) [ArraySubsc len] cnt).
      { rewrite field_address_offset by auto with field_compatible. reflexivity. }
      rewrite Hnext.
      assert (Hcl : 0 <= Znth len counts <= 320) by (apply Forall_Znth; auto; lia).
      forward. (* count = *t4 *)
      { entailer!. lia. }
      (* the C values in Z *)
      assert (Ecode : Int.or (Int.repr code) (Int.and (Int.repr (bufval bytes inc r)) (Int.repr 1)) =
                      Int.repr (code + b)).
      { rewrite and_repr by rep_lia. rewrite Hbit.
        assert (code < 2 ^ 16) by (apply Z.lt_le_trans with (2 ^ len); auto; apply Z.pow_le_mono_r; lia).
        rewrite or_repr by (destruct Hb01 as [-> | ->]; rep_lia).
        rewrite lor_even_bit; auto. }
      assert (Ebuf : Int.shr (Int.repr (bufval bytes inc r)) (Int.repr 1) = Int.repr (bufval bytes inc (r - 1))).
      { rewrite shr1_repr by rep_lia. rewrite bufval_shift by lia. reflexivity. }
      assert (Eleft : Int.sub (Int.repr (Z.min r (16 - len))) (Int.repr 1) =
                      Int.repr (Z.min (r - 1) (16 - (len + 1)))).
      { rewrite sub_repr. f_equal. lia. }
      assert (Enext : force_val (sem_binary_operation' Oadd (tptr tshort) tint
                        (field_address (tarray tshort 16) (SUB len) cnt) (Vint (Int.repr 1))) =
                      offset_val (2 * (len + 1)) cnt).
      { rewrite <- Hnext. destruct cnt; simpl; try reflexivity.
        f_equal. rewrite Ptrofs.add_assoc. f_equal.
        change (Ptrofs.of_ints (Int.repr 1)) with (Ptrofs.repr 1).
        rewrite ptrofs_mul_repr, ptrofs_add_repr. f_equal. lia. }
      rewrite Ecode, Ebuf, Eleft, Enext. clear Ecode Ebuf Eleft Enext.
      assert (Hcode16 : code + b < 2 ^ 16).
      { assert (code <= 2 ^ len - 2).
        { match goal with He : Z.even code = true |- _ => apply Z.even_spec in He; destruct He as [k ->] end.
          assert (2 * k < 2 ^ len) by auto.
          assert (2 ^ len = 2 * 2 ^ (len - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
          lia. }
        assert (2 ^ len <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia). lia. }
      (* the model's step at this length *)
      assert (Hstep : target =
        if code + b <? first + Znth len counts
        then Some (sF (index + (code + b - first)), p0 + len)
        else goZ cF sF (bitZ bytes) (8 * inlen) p0 (Z.to_nat (15 - len)) (len + 1)
               (2 * (code + b)) (2 * (first + Znth len counts)) (index + Znth len counts)).
      { match goal with Hg : goZ _ _ _ _ _ (Z.to_nat (16 - len)) _ _ _ _ = target |- _ => rewrite <- Hg end.
        replace (Z.to_nat (16 - len)) with (S (Z.to_nat (15 - len))) by lia.
        rewrite goZ_S.
        destruct (8 * inlen <? p0 + len) eqn:Enb; [apply Z.ltb_lt in Enb; unfold q, r, p0 in *; lia|].
        fold q b. reflexivity. }
      assert (Hidx : 0 <= index) by (subst index; apply offsZ_nonneg_counts; auto).
      assert (Hidx2 : index <= 320 * 16).
      { subst index. eapply Z.le_trans; [apply offsZ_le_counts; auto|]. lia. }
      assert (Hpow : 2 ^ len <= 2 ^ 16) by (apply Z.pow_le_mono_r; lia).
      forward_if.
      + (* a code of this length: return its symbol *)
        assert (Hbdef : b = (if bitZ bytes q then 1 else 0)) by reflexivity.
        clearbody b.
        set (j := index + (code + b - first)).
        assert (Hcf : forall l, 0 <= cF l) by
          (intros l; unfold cF, countF; destruct (zlt l 0);
           [rewrite Znth_underflow by lia | destruct (zlt l (Zlength counts));
             [rewrite Forall_Znth in H3; specialize (H3 l ltac:(lia)); lia
             |rewrite Znth_overflow by lia]]; unfold default, Inhabitant_Z; lia).
        assert (Hj : 0 <= j < ncodes counts).
        { split; [unfold j; lia|].
          apply Z.lt_le_trans with (index + Znth len counts); [unfold j; lia|].
          subst index.
          replace (offsZ cF (Z.to_nat len) + Znth len counts) with (offsZ cF (S (Z.to_nat len)))
            by (rewrite offsZ_succ by lia; unfold cF, countF; rewrite Z2Nat.id by lia; reflexivity).
          unfold ncodes. fold cF.
          clear - Hcf Hr H1.
          assert (Hm : forall a c, (1 <= a <= c)%nat -> offsZ cF a <= offsZ cF c).
          { intros a c [Ha Hac]. induction Hac; [lia|]. rewrite offsZ_succ by lia.
            specialize (Hcf (Z.of_nat m)). lia. }
          apply Hm. lia. }
        assert (Hjs : 0 <= j < Zlength syms) by lia.
        assert (Hjdef : index + (code + b - first) = j) by reflexivity.
        clearbody j.
        destruct (H5 j Hj) as (v & Hv & Hv0).
        assert (Hsj : sF j = v).
        { unfold sF, symF. destruct Hj as [Hj1 Hj2].
          rewrite (proj2 (Z.leb_le _ _) Hj1), (proj2 (Z.ltb_lt _ _) Hj2). cbn [andb].
          rewrite Hv. rewrite Int.signed_repr by rep_lia. lia. }
        change (@Znth val Inhabitant_val) with (@Znth val Vundef) in Hv.
        assert (Ht : target = Some (v, p0 + len)).
        { rewrite Hstep. rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite Hjdef, Hsj. reflexivity. }
        unfold target, cF, sF, p0, inlen in Ht.
        forward. (* s->bitbuf = bitbuf *)
        forward. (* t11 = s->bitcnt *)
        forward. (* s->bitcnt = (t11 - len) & 7 *)
        forward. (* t9 = h->symbol *)
        forward. (* t10 = symbol[j] *)
        { rewrite Hjdef. entailer!.
          match goal with Hf : Forall (value_fits tshort) syms |- _ => rename Hf into Hvf end.
          rewrite Forall_Znth in Hvf. specialize (Hvf _ Hjs).
          change (@Znth (reptype tshort) (Inhabitant_reptype tshort)) with (@Znth val Vundef) in Hvf.
          rewrite Hv in Hvf |- *. cbn in Hvf. apply Hvf. discriminate. }
        rewrite Hjdef, Hv.
        forward. (* return symbol[j] *)
        match goal with Ht' : decodeZ _ _ _ _ _ = Some (?a, _) |- _ =>
          Exists a inc (bufval bytes inc (r - 1)) ((bitcnt - len) mod 8) 0 end.
        assert (Hbc' : (bitcnt - len) mod 8 = r - 1).
        { symmetry. apply (Z.mod_unique_pos (bitcnt - len) 8 (incnt - inc) (r - 1)); unfold r, q, p0 in *; lia. }
        assert (Hp0 : 0 <= p0) by (unfold p0; destruct (Z.eq_dec incnt 0); [subst; rewrite Hinc0 by auto|]; lia).
        unfold state_rep. rewrite land7. entailer!.
        all: try (split; [rep_lia|]).
        rewrite Ht. split; [reflexivity|]. rewrite Hbc'. split; [unfold r, q, p0 in *; lia|].
        split; [|reflexivity].
        unfold buf_ok. split; [lia|]. split; [unfold r, q, p0 in *; lia|]. split.
        - intros ->. unfold r, q, p0 in *. lia.
        - unfold bufval. reflexivity.
      + (* not this length: on to the next *)
        do 5 (forward; try solve [entailer!]).
        Exists (len + 1) (2 * (code + b)) (2 * (first + Znth len counts)) (index + Znth len counts) inc.
        assert (Hcb : code + b < 2 ^ len).
        { assert (code <= 2 ^ len - 2).
          { match goal with He : Z.even code = true |- _ => apply Z.even_spec in He; destruct He as [k ->] end.
            assert (2 ^ len = 2 * 2 ^ (len - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
            lia. }
          lia. }
        assert (Hstep' := Hstep). unfold target, inlen in Hstep'.
        entailer!.
        repeat split.
        * rewrite Z.pow_add_r by lia. lia.
        * rewrite Z.even_mul. reflexivity.
        * replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
          rewrite offsZ_succ by lia. unfold cF, countF. rewrite Z2Nat.id by lia. reflexivity.
        * rewrite Hstep'. destruct (_ <? _) eqn:E; [apply Z.ltb_lt in E; lia|].
          replace (Z.to_nat (16 - (len + 1))) with (Z.to_nat (15 - len)) by lia. reflexivity.
        * rewrite shl1_repr by rep_lia. reflexivity.
        * rewrite shl1_repr by rep_lia. reflexivity.
        * do 3 f_equal. unfold r; lia.
        * do 2 f_equal. unfold r; lia. }
    (* after the inner loop *)
    clear dependent len. clear dependent code. clear dependent first. clear dependent index. clear dependent inc.
    Intros len code first index inc.
    forward. (* left = 16 - len *)
    forward_if.
    { (* no lengths left: break *)
      forward. Exists inc. entailer!.
      assert (len = 16).
      { match goal with Hl : Int.repr (15 + 1 - len) = Int.repr 0 |- _ =>
          apply repr_inj_signed in Hl; [|rep_lia|rep_lia] end. lia. }
      subst len.
      match goal with Hg : goZ _ _ _ _ _ (Z.to_nat (16 - 16)) _ _ _ _ = _ |- _ => rewrite <- Hg end.
      reflexivity. }
    assert (Hl16 : len < 16).
    { assert (len <> 16).
      { intro E. subst len.
        match goal with Hl : Int.sub _ (Int.repr 16) <> Int.repr 0 |- _ => apply Hl; reflexivity end. }
      lia. }
    assert (Hr0 : 8 * inc - (p0 + len - 1) = 0).
    { destruct (Z.min_spec (8 * inc - (p0 + len - 1)) (16 - len)) as [[_ E]|[_ E]]; lia. }
    forward. forward. (* t7 = s->incnt; t8 = s->inlen *)
    forward_if.
    { (* out of input: eof is set *)
      forward. forward.
      Exists (-10) (Zlength bytes) bitbuf bitcnt 1.
      unfold state_rep. entailer!.
      match goal with Hg : goZ _ _ _ _ _ (Z.to_nat (16 - len)) _ _ _ _ = ?t |- _ =>
        replace (decodeZ (countF counts) (symF syms (ncodes counts)) (bitZ bytes) (8 * Zlength bytes)
                   (8 * incnt - bitcnt)) with t by reflexivity; rewrite <- Hg end.
      replace (Z.to_nat (16 - len)) with (S (Z.to_nat (15 - len))) by lia.
      rewrite goZ_S. rewrite (proj2 (Z.ltb_lt _ _)) by lia. simpl; lia. }
    assert (Hinc' : inc < inlen) by lia.
    assert (Hbyte : 0 <= Znth inc bytes < 256) by (rewrite Forall_Znth in H; apply H; lia).
    forward. forward. forward. (* t5 = s->incnt; s->incnt = t5 + 1; t6 = s->in *)
    forward; try solve [entailer!; rep_lia]. (* bitbuf = in[t5] *)
    assert (Ebuf : bufval bytes (inc + 1) (8 * (inc + 1) - (p0 + len - 1)) = Znth inc bytes).
    { replace (8 * (inc + 1) - (p0 + len - 1)) with 8 by lia. unfold bufval.
      destruct (inc + 1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia|].
      rewrite Z.shiftr_0_r. f_equal. lia. }
    forward_if.
    + forward. Exists len code first index (inc + 1). entailer!.
      do 2 f_equal. lia.
    + forward. Exists len code first index (inc + 1). entailer!.
      all: try (do 2 f_equal; lia).
  - (* after the loop: ran out of lengths *)
    clear Hbuf. Intros inc.
    forward.
    Exists (-10) inc bitbuf bitcnt 0.
    unfold state_rep. entailer!.
    match goal with Hn : ?t = None |- _ =>
      replace (decodeZ (countF counts) (symF syms (ncodes counts)) (bitZ bytes) (8 * Zlength bytes)
                 (8 * incnt - bitcnt)) with t by reflexivity; rewrite Hn end.
    simpl; lia.
Qed.

(* decode_spec is decode_model_spec on construct's tables (Main.v) *)
Local Opaque krZ countsOf Bridge.lean_decode decodeZ.

Lemma decode_model_sub : funspec_sub (snd decode_model_spec) (snd decode_spec).
Proof.
  do_funspec_sub.
  destruct w as [[[[[[[[[[[[[[[[sh shi] shh] s] outp] outlen] outcnt] inp] bytes] incnt] bitbuf] bitcnt]
                   h] cnt] sym] lens] syms].
  clear H.
  normalize. unfold bytes_ok in *.
  destruct (construct_tables_decodable lens ltac:(assumption) ltac:(assumption) syms
              ltac:(assumption) ltac:(assumption)) as (Hd1 & Hd2 & Hd3 & Hd4).
  assert (Hp : 0 <= 8 * incnt - bitcnt) by (unfold buf_ok in *; lia).
  pose proof (decode_model_lean lens ltac:(assumption) ltac:(assumption) syms bytes (8 * incnt - bitcnt)
                ltac:(assumption) ltac:(assumption) ltac:(assumption) Hp) as Hm.
  Exists (sh, shi, shh, s, outp, outlen, outcnt, inp, bytes, incnt, bitbuf, bitcnt, h, cnt, sym,
          countsOf lens, syms) emp.
  entailer!.
  intros tau ? ?.
  Exists x0 x1 x2 x3 x4. entailer!.
  match goal with H : match decodeZ _ _ _ _ _ with _ => _ end |- _ => rewrite Hm in H; exact H end.
Qed.

Lemma body_decode : semax_body Vprog Gprog f_decode decode_spec.
Proof.
  eapply semax_body_funspec_sub; [exact body_decode_model | exact decode_model_sub |].
  compute; repeat (constructor; [intros H; repeat (destruct H as [H|H]; [discriminate|]); exact H|]);
    constructor.
Qed.
