-- @decreasing vbits::lsb::lval
all_goals
  have hs := Seq.len_nonneg «s»
  simp at h1
  rw [Seq.len_subrange «s» 1 (Seq.len «s») (by omega)]
  omega
-- @after vbits::lsb::lval
theorem lval_nonneg (u : Unspec) (s : List Bool) : 0 ≤ «vbits».«lsb».«lval» u s := by
  induction s using «vbits».«lsb».«lval».induct with
  | case1 s h => rw [«vbits».«lsb».«lval»]; simp [h]
  | case2 s h ih => rw [«vbits».«lsb».«lval», dif_neg (by simpa using h)]; exact clip_nat_nonneg u _
-- @after vdeflate::spec::getbits
theorem getbits_nonneg (u : Unspec) (b : List Bool) (p n : Int) (hn : 0 ≤ n)
    (h : ¬(«vdeflate».«spec».«getbits» u b p n).isNone = true) :
    0 ≤ someVal u (.int .nat) (α := Int) rfl («vdeflate».«spec».«getbits» u b p n) := by
  unfold «vdeflate».«spec».«getbits» at h ⊢
  simp only [IntRange.contains, decide_eq_true hn, dite_true] at h ⊢
  split
  · simp [someVal]; exact lval_nonneg u _
  · simp_all
-- @decreasing vbits::bitspec::bits_val
all_goals
  have hs := Seq.len_nonneg «s»
  simp at h1
  rw [Seq.len_dropLast «s» (by omega)]
  omega
-- @decreasing vdeflate::spec::find_sym
all_goals
  have hl : 0 ≤ «l» := by simpa [IntRange.contains] using hinv
  rw [clip_nat u _ (by omega)]
  simp_all [«vdeflate».«spec».«maxbits»]; omega
-- @decreasing vdeflate::spec::read_lens
all_goals first
  | vir_decreasing
  | (have hnb : 0 ≤ «nb_199» := by simp only [«nb_199», «tmp_1»]; split <;> (try split) <;> simp
     have hbase : 3 ≤ «base_200» := by simp only [«base_200», «tmp_1»]; split <;> (try split) <;> simp
     have he : 0 ≤ «e_219» := getbits_nonneg u «b» «p1_69» «nb_199» hnb h4
     have hr : «rep_231» = «base_200» + «e_219» := clip_nat u _ (by omega)
     have hc : clip u .nat (Seq.len acc + «rep_231») = Seq.len acc + «rep_231» :=
       clip_nat u _ (by have := Seq.len_nonneg acc; omega)
     show (total - Seq.len (Seq.add acc (Seq.new u (.int (.u 8)) (α := Int) rfl «rep_231» (fun _ => «v_326»)))).toNat < _
     rw [Seq.len_add, Seq.len_new u _ _ _ _ (by omega)]
     simp [hc] at h5 h1
     omega)
-- @validdec vbits::lsb::lval
first | vir_valid_dec | (have hs := Seq.len_nonneg «s»; simp at h1; rw [Seq.len_subrange «s» 1 (Seq.len «s») (by omega)]; omega)
-- @validdec vbits::bitspec::bits_val
first | vir_valid_dec | (have hs := Seq.len_nonneg «s»; simp at h1; rw [Seq.len_dropLast «s» (by omega)]; omega)
-- @validdec vdeflate::spec::find_sym
first | vir_valid_dec | (have hl : 0 ≤ l := (by simpa [VIR.invOk, VIR.enc, VModel.IntRange.contains] using hi); rw [clip_nat u _ (by omega)]; simp_all [V.vdeflate.spec.maxbits]; omega)
-- @validdec vdeflate::spec::read_lens
first | vir_valid_dec | (have he := V.getbits_nonneg u _ _ _ (by split <;> (try split) <;> decide) h4; simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt, Int.not_le, ge_iff_le, gt_iff_lt] at h1 h5; rw [Seq.len_add, Seq.len_new u _ _ _ _ ?hr]; have := Seq.len_nonneg acc; (split <;> (try split) <;> simp_all <;> simp (disch := omega) only [clip_nat] at * <;> omega); (split <;> (try split) <;> simp_all <;> simp (disch := omega) only [clip_nat] at * <;> omega))
-- @decreasing vdeflate::wrap::adler_a
all_goals
  have hs := Seq.len_nonneg «s»
  simp at h1
  rw [Seq.len_dropLast «s» (by omega)]
  omega
-- @decreasing vdeflate::wrap::adler_b
all_goals
  have hs := Seq.len_nonneg «s»
  simp at h1
  rw [Seq.len_dropLast «s» (by omega)]
  omega
-- @decreasing vdeflate::wrap::crc_run
all_goals
  have hs := Seq.len_nonneg «s»
  simp at h1
  rw [Seq.len_dropLast «s» (by omega)]
  omega
-- @decreasing vdeflate::wrap::gzip_members
all_goals
  have hs := Seq.len_nonneg «s»
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_le, Int.not_lt] at h3
  rw [Seq.len_skip «s» «n_62» (by omega)]
  omega
-- @validdec vdeflate::wrap::adler_a
first | vir_valid_dec | (have hs := Seq.len_nonneg «s»; simp at h1; rw [Seq.len_dropLast «s» (by omega)]; omega)
-- @validdec vdeflate::wrap::adler_b
first | vir_valid_dec | (have hs := Seq.len_nonneg «s»; simp at h1; rw [Seq.len_dropLast «s» (by omega)]; omega)
-- @validdec vdeflate::wrap::crc_run
first | vir_valid_dec | (have hs := Seq.len_nonneg «s»; simp at h1; rw [Seq.len_dropLast «s» (by omega)]; omega)
-- @validdec vdeflate::wrap::gzip_members
first | vir_valid_dec | (have hs := Seq.len_nonneg «s»; simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_le, Int.not_lt] at h3; rw [Seq.len_skip] <;> first | omega | exact ⟨by omega, by omega⟩)
