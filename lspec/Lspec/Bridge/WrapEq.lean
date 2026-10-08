import Lspec.Bridge.DeflateEq
import Lspec.Bridge.ContractsEq
import Lspec.Deflate.Wrap

/-!
# vdeflate's zlib and gzip wrappers are the Lean spec's

`vdeflate/src/wrap.rs`'s spec functions, as translated from Verus's VIR (`VDeflate.lean`),
compute `Lspec/Deflate/Wrap.lean`'s, for every choice of the values Verus leaves
unspecified: Adler-32 and CRC-32 (`adler32_eq`, `crc32_eq`), then `zlib_decode`,
`zlib_decode_dict`, `gzip_decode` and `gzip_file`.

The checksums are where the two are written differently. Verus recurses on the last byte
and reduces Adler-32's sums once at the end; the Lean spec, like the RFC, runs forward and
reduces at every step. Both are shown equal to one left fold.
-/

namespace Bridge

open VModel

/-- A byte list in the Verus model is `outV`; its bytes as naturals. -/
abbrev natsOf (s : Array UInt8) : List Nat := s.toList.map (fun x => x.toNat)

theorem outV_eq_nats (s : Array UInt8) : outV s = (natsOf s).map (fun (n : Nat) => (n : Int)) := by
  simp [outV, natsOf]

/-! ## Snoc induction on the Verus model's lists -/

theorem len_snoc_ne (l : List Int) (x : Int) : ¬(decide (Seq.len (l ++ [x]) = 0)) = true := by
  simp; omega

/-- Induction on a list from the end, as the Verus spec recurses (`drop_last`, `last`). -/
@[elab_as_elim]
theorem snoc_induction {α : Type} {motive : List α → Prop} (nil : motive [])
    (append_singleton : ∀ l x, motive l → motive (l ++ [x])) (l : List α) : motive l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons x t ih => rw [List.reverse_cons]; exact append_singleton _ x ih

/-! ## Adler-32 -/

/-- Adler-32's sums, unreduced, as a left fold: A is 1 plus the bytes, B the sum of each A. -/
def adlerStep (p : Nat × Nat) (x : Nat) : Nat × Nat := (p.1 + x, p.2 + (p.1 + x))

/-- The same, reduced at every step, as RFC 1950 8.2 does. -/
def adlerStepMod (p : Nat × Nat) (x : Nat) : Nat × Nat :=
  ((p.1 + x) % 65521, (p.2 + (p.1 + x) % 65521) % 65521)

theorem adler_ab_eq (u : Unspec) (l : List Nat) :
    V.vdeflate.wrap.adler_a u (l.map (fun (n : Nat) => (n : Int))) = ((l.foldl adlerStep (1, 0)).1 : Int) ∧
    V.vdeflate.wrap.adler_b u (l.map (fun (n : Nat) => (n : Int))) = ((l.foldl adlerStep (1, 0)).2 : Int) := by
  induction l using snoc_induction with
  | nil =>
    constructor
    · rw [V.vdeflate.wrap.adler_a]; simp
    · rw [V.vdeflate.wrap.adler_b]; simp
  | append_singleton l x ih =>
    have ha : V.vdeflate.wrap.adler_a u ((l ++ [x]).map (fun (n : Nat) => (n : Int))) =
        (((l ++ [x]).foldl adlerStep (1, 0)).1 : Int) := by
      rw [V.vdeflate.wrap.adler_a, List.map_append, List.map_singleton, dif_neg (len_snoc_ne _ _),
        Seq.dropLast_eq, Seq.last_eq, ih.1, clip_nat u _ (by omega)]
      simp [List.foldl_append, adlerStep]
    refine ⟨ha, ?_⟩
    rw [V.vdeflate.wrap.adler_b, List.map_append, List.map_singleton, dif_neg (len_snoc_ne _ _),
      Seq.dropLast_eq, ih.2, ← List.map_singleton, ← List.map_append, ha, clip_nat u _ (by omega)]
    simp [List.foldl_append, adlerStep]

theorem adler_fold_mod (l : List Nat) (a b : Nat) :
    l.foldl adlerStepMod (a % 65521, b % 65521) =
      ((l.foldl adlerStep (a, b)).1 % 65521, (l.foldl adlerStep (a, b)).2 % 65521) := by
  induction l generalizing a b with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    have : adlerStepMod (a % 65521, b % 65521) x = ((a + x) % 65521, (b + (a + x)) % 65521) := by
      simp only [adlerStepMod, Prod.mk.injEq]
      constructor
      · omega
      · omega
    rw [this, ih]; rfl

theorem adlerGo_eq (s : Array UInt8) : ∀ k i s1 s2, s.size - i = k →
    Deflate.adlerGo s i s1 s2 = ((natsOf s).drop i).foldl adlerStepMod (s1, s2) := by
  intro k
  induction k with
  | zero =>
    intro i s1 s2 hk
    rw [Deflate.adlerGo, if_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ k ih =>
    intro i s1 s2 hk
    have h : i < s.size := by omega
    rw [Deflate.adlerGo, if_pos h, ih (i + 1) _ _ (by omega)]
    have hd : (natsOf s).drop i = (natsOf s)[i]'(by simp; omega) :: (natsOf s).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons]
    rw [hd, List.foldl_cons]
    congr 1
    simp [adlerStepMod, Deflate.byteAt, natsOf, Array.getD, h]

/-- **Adler-32**: Verus's unreduced sums, reduced at the end, are RFC 1950's. -/
theorem adler32_eq (u : Unspec) (s : Array UInt8) :
    V.vdeflate.wrap.adler32 u (outV s) = (Deflate.adler32 s : Int) := by
  have hg : Deflate.adlerGo s 0 1 0 =
      (((natsOf s).foldl adlerStep (1, 0)).1 % 65521, ((natsOf s).foldl adlerStep (1, 0)).2 % 65521) := by
    rw [adlerGo_eq s _ 0 1 0 rfl, List.drop_zero]
    exact adler_fold_mod (natsOf s) 1 0
  unfold Deflate.adler32
  rw [hg]
  rw [V.vdeflate.wrap.adler32, outV_eq_nats, (adler_ab_eq u _).1, (adler_ab_eq u _).2,
    show V.vdeflate.wrap.adler_mod u 0 = 65521 from rfl,
    emod_ne u _ _ (by decide), emod_ne u _ _ (by decide)]
  generalize ((natsOf s).foldl adlerStep (1, 0)).1 = A
  generalize ((natsOf s).foldl adlerStep (1, 0)).2 = B
  have h1 : 0 ≤ ((B : Int) % 65521) * 65536 := by omega
  rw [clip_nat u _ h1, clip_nat u _ (by omega)]
  show _ = (((B % 65521) * 65536 + A % 65521 : Nat) : Int)
  omega

/-! ## CRC-32 -/

theorem crcBit_lt (c : Nat) (h : c < 2 ^ 32) : Deflate.crcBit c < 2 ^ 32 := by
  unfold Deflate.crcBit
  split
  · exact Nat.xor_lt_two_pow (by omega) (by decide)
  · omega

theorem clip_u32 (u : Unspec) (x : Int) (h0 : 0 ≤ x) (h1 : x < 2 ^ 32) : clip u (.u 32) x = x :=
  clip_of_contains u _ x (by simp [IntRange.contains]; omega)

theorem crc_bit_eq (u : Unspec) (c : Nat) (h : c < 2 ^ 32) :
    V.vdeflate.wrap.crc_bit u (c : Int) = (Deflate.crcBit c : Int) := by
  rw [V.vdeflate.wrap.crc_bit, dif_pos (by simp [IntRange.contains]; omega)]
  have hb : band (c : Int) 1 = ((c % 2 : Nat) : Int) := by
    unfold band; rw [Int.toNat_natCast, show (1 : Int).toNat = 1 from rfl, Nat.and_one_is_mod]
  have hs : shr (c : Int) 1 = ((c / 2 : Nat) : Int) := by
    unfold shr; rw [Int.toNat_natCast, show (1 : Int).toNat = 1 from rfl, Nat.shiftRight_eq_div_pow]
  have e1 : clip u (.u 32) ((c % 2 : Nat) : Int) = ((c % 2 : Nat) : Int) :=
    clip_u32 u _ (by omega) (by omega)
  have e2 : clip u (.u 32) ((c / 2 : Nat) : Int) = ((c / 2 : Nat) : Int) :=
    clip_u32 u _ (by omega) (by omega)
  have hx : c / 2 ^^^ 0xEDB88320 < 2 ^ 32 := Nat.xor_lt_two_pow (by omega) (by decide)
  have e3 : bxor ((c / 2 : Nat) : Int) 3988292384 = ((c / 2 ^^^ 0xEDB88320 : Nat) : Int) := by
    unfold bxor; rw [Int.toNat_natCast]; rfl
  have e4 : clip u (.u 32) ((c / 2 ^^^ 0xEDB88320 : Nat) : Int) = ((c / 2 ^^^ 0xEDB88320 : Nat) : Int) :=
    clip_u32 u _ (by omega) (by omega)
  rw [hb, hs, e1, e2, e3, e4]
  unfold Deflate.crcBit
  by_cases h1 : c % 2 = 1
  · rw [dif_pos (by simp [h1]), if_pos h1]
  · rw [dif_neg (by simp; omega), if_neg h1]

theorem crc_bit_nat (c : Nat) (h : c < 2 ^ 32) :
    ∃ d : Nat, Deflate.crcBit c = d ∧ d < 2 ^ 32 := ⟨_, rfl, crcBit_lt c h⟩

theorem crcByte_lt (c : Nat) (x : UInt8) (h : c < 2 ^ 32) : Deflate.crcByte c x < 2 ^ 32 := by
  unfold Deflate.crcByte
  have h0 : c ^^^ x.toNat < 2 ^ 32 :=
    Nat.xor_lt_two_pow h (by have := x.toNat_lt; omega)
  repeat (first | apply crcBit_lt | exact h0)

theorem crc_byte_eq (u : Unspec) (c : Nat) (x : UInt8) (h : c < 2 ^ 32) :
    V.vdeflate.wrap.crc_byte u (c : Int) (x.toNat : Int) = (Deflate.crcByte c x : Int) := by
  have hx := x.toNat_lt
  rw [V.vdeflate.wrap.crc_byte, dif_pos (by simp [IntRange.contains]; omega)]
  have h0 : c ^^^ x.toNat < 2 ^ 32 := Nat.xor_lt_two_pow h (by omega)
  simp only []
  have hx' : bxor (c : Int) (x.toNat : Int) = ((c ^^^ x.toNat : Nat) : Int) := by
    unfold bxor; simp
  rw [clip_u32 u (x.toNat : Int) (by omega) (by omega), hx',
    clip_u32 u ((c ^^^ x.toNat : Nat) : Int) (by omega) (by omega)]
  unfold Deflate.crcByte
  simp only []
  have b1 := crcBit_lt _ h0
  have b2 := crcBit_lt _ b1
  have b3 := crcBit_lt _ b2
  have b4 := crcBit_lt _ b3
  have b5 := crcBit_lt _ b4
  have b6 := crcBit_lt _ b5
  have b7 := crcBit_lt _ b6
  rw [crc_bit_eq u _ h0, crc_bit_eq u _ b1, crc_bit_eq u _ b2, crc_bit_eq u _ b3,
    crc_bit_eq u _ b4, crc_bit_eq u _ b5, crc_bit_eq u _ b6, crc_bit_eq u _ b7]

/-- `crcByte` on a list of bytes, as a left fold. -/
def crcFold (c : Nat) (l : List UInt8) : Nat := l.foldl Deflate.crcByte c

theorem crcFold_lt (c : Nat) (l : List UInt8) (h : c < 2 ^ 32) : crcFold c l < 2 ^ 32 := by
  induction l generalizing c with
  | nil => exact h
  | cons x l ih => exact ih _ (crcByte_lt c x h)

theorem crc_run_eq (u : Unspec) (c : Nat) (l : List UInt8) (h : c < 2 ^ 32) :
    V.vdeflate.wrap.crc_run u (c : Int) (l.map (fun x => (x.toNat : Int))) = (crcFold c l : Int) := by
  induction l using snoc_induction with
  | nil => rw [V.vdeflate.wrap.crc_run, dif_pos (by simp [IntRange.contains]; omega)]; simp [crcFold]
  | append_singleton l x ih =>
    rw [V.vdeflate.wrap.crc_run, dif_pos (by simp [IntRange.contains]; omega), List.map_append,
      List.map_singleton, dif_neg (len_snoc_ne _ _), Seq.dropLast_eq, Seq.last_eq, ih,
      crc_byte_eq u _ x (crcFold_lt c l h)]
    simp [crcFold, List.foldl_append]

theorem crcGo_eq (s : Array UInt8) : ∀ k i c, s.size - i = k →
    Deflate.crcGo s i c = crcFold c (s.toList.drop i) := by
  intro k
  induction k with
  | zero =>
    intro i c hk
    rw [Deflate.crcGo, dif_neg (by omega), List.drop_eq_nil_of_le (by simp; omega)]
    rfl
  | succ k ih =>
    intro i c hk
    have h : i < s.size := by omega
    rw [Deflate.crcGo, dif_pos h, ih (i + 1) _ (by omega)]
    conv => rhs; rw [List.drop_eq_getElem_cons (i := i) (by simp; omega)]
    simp [crcFold]

/-- **CRC-32**: Verus's last-byte recursion is RFC 1952's register run. -/
theorem crc32_eq (u : Unspec) (s : Array UInt8) :
    V.vdeflate.wrap.crc32 u (outV s) = (Deflate.crc32 s : Int) := by
  rw [V.vdeflate.wrap.crc32, show (4294967295 : Int) = ((4294967295 : Nat) : Int) from rfl,
    crc_run_eq u _ _ (by decide)]
  unfold Deflate.crc32
  rw [crcGo_eq s _ 0 _ rfl, List.drop_zero]
  have hl := crcFold_lt 4294967295 s.toList (by decide)
  have hx : crcFold 4294967295 s.toList ^^^ 0xFFFFFFFF < 2 ^ 32 :=
    Nat.xor_lt_two_pow hl (by decide)
  unfold bxor
  rw [Int.toNat_natCast, Int.toNat_natCast, clip_u32 u _ (by omega) (by omega)]

/-! ## Bytes -/

@[simp] theorem len_outV (s : Array UInt8) : Seq.len (outV s) = (s.size : Int) := by
  simp [outV]

theorem index_outV (u : Unspec) (s : Array UInt8) (j : Int) (i : Nat) (hj : j = i) (h : i < s.size) :
    Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) j = (Deflate.byteAt s i : Int) := by
  subst hj
  rw [Seq.index_eq u _ i (by simp [outV]; omega)]
  simp [outV, Deflate.byteAt, Array.getD, h]

theorem byteAt_lt (s : Array UInt8) (i : Nat) : Deflate.byteAt s i < 256 := by
  unfold Deflate.byteAt; exact (s.getD i 0).toNat_lt

theorem subrange_len_drop {α : Type} (l : List α) (n : Nat) :
    Seq.subrange l (n : Int) (l.length : Int) = l.drop n := by
  induction l generalizing n with
  | nil => simp [Seq.subrange]
  | cons x t ih =>
    simp only [Seq.subrange, List.length_cons]
    cases n with
    | zero =>
      rw [if_neg (by omega), if_neg (by omega), show ((t.length + 1 : Nat) : Int) - 1 = (t.length : Int) by omega,
        show ((0 : Nat) : Int) = ((0 : Nat) : Int) from rfl, ih 0]
      simp
    | succ n =>
      rw [if_pos (by omega), show ((n + 1 : Nat) : Int) - 1 = (n : Int) by omega,
        show ((t.length + 1 : Nat) : Int) - 1 = (t.length : Int) by omega, ih n]
      simp

/-- `skip`, for any start: past the end, both sides are empty. -/
theorem skip_outV (s : Array UInt8) (n : Nat) :
    Seq.skip (outV s) (n : Int) = outV (s.extract n s.size) := by
  unfold Seq.skip
  rw [len_outV, show (s.size : Int) = ((outV s).length : Int) by simp [outV], subrange_len_drop]
  simp [outV, List.map_drop, Array.toList_extract, List.extract]
  exact (List.take_of_length_le (by simp)).symm

theorem take_outV (s : Array UInt8) (n : Nat) (h : n ≤ s.size) :
    Seq.take (outV s) (n : Int) = outV (s.extract 0 n) := by
  unfold Seq.take
  rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, Seq.subrange_eq _ 0 n (by omega) (by simp [outV]; omega)]
  simp [outV, List.map_take, Array.toList_extract, List.extract]

theorem after_bits_eq (u : Unspec) (h q : Nat) :
    V.vdeflate.wrap.after_bits u (h : Int) (q : Int) = (Deflate.afterStream h q : Int) := by
  rw [V.vdeflate.wrap.after_bits, dif_pos (by simp [IntRange.contains]),
    clip_nat u _ (by omega), ediv_ne u _ _ (by decide)]
  unfold Deflate.afterStream
  omega

/-- The decoders' `inflate(lbits(s.skip(h)))`: the Lean spec on the bytes from `h`. -/
theorem inflate_skip_eq (u : Unspec) (s : Array UInt8) (h : Nat) :
    V.vdeflate.spec.inflate u (V.vbits.lsb.lbits u (Seq.skip (outV s) (h : Int))) =
      Option.map (fun d : Deflate.Decoded => (outV d.out, (d.bits : Int), d.zlib))
        (Deflate.inflate (Deflate.bitsOf (s.extract h s.size))) := by
  rw [skip_outV s h, lbits_eq, verus_inflate_eq]

/-! ## RFC 1950: zlib -/

/-- The Verus spec's big-endian ADLER32 at byte `a`, with its `nat` clips: `be32`. -/
theorem be32_eq (u : Unspec) (s : Array UInt8) (a : Nat) (j0 j1 j2 j3 : Int) (h0 : j0 = a)
    (h1 : j1 = (a + 1 : Nat)) (h2 : j2 = (a + 2 : Nat)) (h3 : j3 = (a + 3 : Nat)) (h : a + 4 ≤ s.size) :
    clip u .nat (clip u .nat (clip u .nat (clip u .nat (clip u .nat (clip u .nat
      (Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) j0 * 256) +
      Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) j1) * 256) +
      Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) j2) * 256) +
      Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) j3) =
      (Deflate.be32 s a : Int) := by
  rw [index_outV u s _ a h0 (by omega), index_outV u s _ (a + 1) h1 (by omega),
    index_outV u s _ (a + 2) h2 (by omega), index_outV u s _ (a + 3) h3 (by omega)]
  unclip
  unfold Deflate.be32
  omega

theorem trailer_eq (u : Unspec) (s o : Array UInt8) (a : Nat) (z : Bool) :
    (if h : decide ((a : Int) + 4 > (s.size : Int)) = true then none
      else if h5 : (!decide (clip u .nat (clip u .nat (clip u .nat (clip u .nat (clip u .nat (clip u .nat
          (Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) (a : Int) * 256) +
          Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) ((a : Int) + 1)) * 256) +
          Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) ((a : Int) + ((2 : Nat) : Int))) * 256) +
          Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) ((a : Int) + 3)) =
          V.vdeflate.wrap.adler32 u (outV o))) = true then none
      else some (outV o, (a : Int) + 4, z)) =
      Option.map (fun r : Deflate.Unwrapped => (outV r.out, (r.used : Int), r.zlib))
        (Deflate.zlibTrailer s o a z) := by
  unfold Deflate.zlibTrailer
  simp only [Option.bind_eq_bind]
  by_cases ha : a + 4 ≤ s.size
  · rw [dif_neg (by simp; omega), guard_pos' ha, Option.bind_some,
      be32_eq u s a _ _ _ _ rfl (by omega) (by omega) (by omega) ha, adler32_eq]
    by_cases hc : Deflate.be32 s a = Deflate.adler32 o
    · rw [dif_neg (by simp [hc]), guard_pos' hc, Option.bind_some]
      simp
    · rw [dif_pos (by simp; omega), guard_neg' hc]; rfl
  · rw [dif_pos (by simp; omega), guard_neg' ha]; rfl

theorem zlib_decode_eq (u : Unspec) (s : Array UInt8) :
    V.vdeflate.wrap.zlib_decode u (outV s) =
      Option.map (fun r : Deflate.Unwrapped => (outV r.out, (r.used : Int), r.zlib))
        (Deflate.zlibDecode s) := by
  unfold V.vdeflate.wrap.zlib_decode Deflate.zlibDecode
  simp only [len_outV]
  by_cases h2 : s.size < 2
  · rw [dif_pos (by simp; omega), guard_neg' (by omega)]; rfl
  rw [dif_neg (by simp; omega), guard_pos' (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [index_outV u s 0 0 rfl (by omega), index_outV u s 1 1 rfl (by omega)]
  have lb0 := byteAt_lt s 0
  have lb1 := byteAt_lt s 1
  rw [clip_nat u ((Deflate.byteAt s 0 : Int) * 256) (by omega), clip_nat u _ (by omega)]
  simp (disch := decide) only [emod_ne, ediv_ne]
  by_cases hh : Deflate.zlibHeaderOk (Deflate.byteAt s 0) (Deflate.byteAt s 1) = true ∧
      Deflate.fdict (Deflate.byteAt s 1) = false
  · obtain ⟨hh1, hh2⟩ := hh
    rw [guard_pos' hh1, Option.bind_some, guard_pos' (by simp [hh2]), Option.bind_some]
    simp only [Deflate.zlibHeaderOk, Deflate.fdict, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Bool.not_eq_true', beq_eq_false_iff_ne] at hh1 hh2
    refine dite_neg_eq (by simp; omega) ?_
    rw [show (2 : Int) = ((2 : Nat) : Int) from rfl, inflate_skip_eq u s 2]
    cases hd : Deflate.inflate (Deflate.bitsOf (s.extract 2 s.size)) with
    | none => rfl
    | some d =>
      rw [Option.map_some, Option.isNone_some, dif_neg (by simp), Option.bind_some]
      dsimp only [someVal_some]
      simp only [after_bits_eq]
      exact trailer_eq u s d.out _ d.zlib
  · have hn : ¬(Deflate.zlibHeaderOk (Deflate.byteAt s 0) (Deflate.byteAt s 1) = true ∧
        (!Deflate.fdict (Deflate.byteAt s 1)) = true) := by simpa using hh
    refine dite_pos_eq (by
      simp only [Deflate.zlibHeaderOk, Deflate.fdict, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        Bool.not_eq_true', beq_eq_false_iff_ne, not_and, ne_eq] at hn
      simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
        decide_eq_true_eq]
      omega) ?_
    by_cases h1 : Deflate.zlibHeaderOk (Deflate.byteAt s 0) (Deflate.byteAt s 1) = true
    · rw [guard_pos' h1, Option.bind_some, guard_neg' (fun h => hn ⟨h1, h⟩)]; rfl
    · rw [guard_neg' h1]; rfl

theorem zlib_decode_dict_eq (u : Unspec) (s dict : Array UInt8) :
    V.vdeflate.wrap.zlib_decode_dict u (outV s) (outV dict) =
      Option.map (fun r : Deflate.Unwrapped => (outV r.out, (r.used : Int), r.zlib))
        (Deflate.zlibDecodeDict s dict) := by
  unfold V.vdeflate.wrap.zlib_decode_dict Deflate.zlibDecodeDict
  simp only [len_outV]
  by_cases h2 : s.size < 2
  · rw [dif_pos (by simp; omega), guard_neg' (by omega)]; rfl
  rw [dif_neg (by simp; omega), guard_pos' (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [index_outV u s 0 0 rfl (by omega), index_outV u s 1 1 rfl (by omega)]
  have lb0 := byteAt_lt s 0
  have lb1 := byteAt_lt s 1
  simp (disch := decide) only [emod_ne, ediv_ne]
  by_cases hf : Deflate.fdict (Deflate.byteAt s 1) = true
  · have hf' : Deflate.byteAt s 1 / 32 % 2 = 1 := by simpa [Deflate.fdict] using hf
    rw [dif_neg (by simp; omega), if_pos hf]
    rw [clip_nat u ((Deflate.byteAt s 0 : Int) * 256) (by omega), clip_nat u _ (by omega)]
    by_cases hh : Deflate.zlibHeaderOk (Deflate.byteAt s 0) (Deflate.byteAt s 1) = true ∧ 6 ≤ s.size
    · obtain ⟨hh1, hh6⟩ := hh
      rw [guard_pos' hh1, Option.bind_some, guard_pos' hh6, Option.bind_some]
      simp only [Deflate.zlibHeaderOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh1
      refine dite_neg_eq (by simp; omega) ?_
      try dsimp only
      simp only [be32_eq u s 2 2 3 4 5 rfl rfl rfl rfl (by omega), adler32_eq]
      by_cases hid : Deflate.be32 s 2 = Deflate.adler32 dict
      · rw [dif_neg (by simp [hid]), guard_pos' hid, Option.bind_some]
        rw [show (6 : Int) = ((6 : Nat) : Int) from rfl, skip_outV, lbits_eq,
          show (0 : Int) = ((0 : Nat) : Int) from rfl, inflate_blocks_eq]
        cases hb : Deflate.inflateBlocks (Deflate.bitsOf (s.extract 6 s.size)) 0 dict true with
        | none => rfl
        | some r =>
          obtain ⟨full, q, z⟩ := r
          rw [Option.map_some, Option.isNone_some, dif_neg (by simp), Option.bind_some]
          dsimp only [someVal_some]
          simp only [clip_nat u (q : Int) (by omega), after_bits_eq, skip_outV, len_outV,
            show decide ((q : Int) < ((0 : Nat) : Int)) = false by simp, Bool.false_or]
          exact trailer_eq u s _ _ z
      · rw [dif_pos (by simp; omega), guard_neg' hid]; rfl
    · refine dite_pos_eq (by
        simp only [Deflate.zlibHeaderOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
        simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
          decide_eq_true_eq]
        omega) ?_
      by_cases h1 : Deflate.zlibHeaderOk (Deflate.byteAt s 0) (Deflate.byteAt s 1) = true
      · rw [guard_pos' h1, Option.bind_some, guard_neg' (fun h => hh ⟨h1, h⟩)]; rfl
      · rw [guard_neg' h1]; rfl
  · have hf' : Deflate.byteAt s 1 / 32 % 2 = 0 := by simp [Deflate.fdict] at hf; omega
    rw [dif_pos (by simp; omega), if_neg hf, zlib_decode_eq]

/-! ## RFC 1952: gzip -/

theorem zero_at_eq (u : Unspec) (s : Array UInt8) : ∀ k i, s.size - i = k →
    V.vdeflate.wrap.zero_at u (outV s) (i : Int) =
      Option.map (fun n : Nat => (n : Int)) (Deflate.zeroAt s i) := by
  intro k
  induction k with
  | zero =>
    intro i hk
    rw [V.vdeflate.wrap.zero_at, Deflate.zeroAt, dif_pos (by simp; omega), if_neg (by omega)]; rfl
  | succ k ih =>
    intro i hk
    rw [V.vdeflate.wrap.zero_at, Deflate.zeroAt, dif_neg (by simp; omega), if_pos (by omega),
      index_outV u s _ i rfl (by omega)]
    by_cases hz : Deflate.byteAt s i = 0
    · rw [dif_pos (by simp [hz]), if_pos hz]; rfl
    · rw [dif_neg (by simp; omega), if_neg hz, show (i : Int) + 1 = ((i + 1 : Nat) : Int) by omega,
        ih (i + 1) (by omega)]

/-- The position after FEXTRA, as `gzipHeader` computes it. -/
def gzI1 (s : Array UInt8) (f : Nat) : Option Nat :=
  if f / 4 % 2 = 1 then
    if 12 ≤ s.size then
      if 12 + Deflate.le16 s 10 ≤ s.size then some (12 + Deflate.le16 s 10) else none
    else none
  else some 10

theorem gz_i1_eq (u : Unspec) (s : Array UInt8) (f : Nat) :
    (if h : decide (emod u (ediv u (f : Int) 4) 2 = 1) = true then
      (if h : decide ((10 : Int) + 2 > (s.size : Int)) = true then (none : Option Int)
       else if h : decide ((10 : Int) + 2 + (Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) 10 +
           256 * Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) (10 + 1)) > (s.size : Int)) = true then none
       else some ((10 : Int) + 2 + (Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) 10 +
           256 * Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) (10 + 1))))
     else some 10) = (gzI1 s f).map (fun n : Nat => (n : Int)) := by
  rw [ediv_ne u _ _ (by decide), emod_ne u _ _ (by decide)]
  unfold gzI1
  by_cases hx : f / 4 % 2 = 1
  · rw [dif_pos (by simp; omega), if_pos hx]
    by_cases h12 : 12 ≤ s.size
    · rw [dif_neg (by simp; omega), if_pos h12, index_outV u s 10 10 rfl (by omega),
        index_outV u s (10 + 1) 11 rfl (by omega)]
      have hl : (Deflate.le16 s 10 : Int) = (Deflate.byteAt s 10 : Int) + 256 * (Deflate.byteAt s 11 : Int) := by
        simp [Deflate.le16]
      by_cases h14 : 12 + Deflate.le16 s 10 ≤ s.size
      · rw [dif_neg (by simp; omega), if_pos h14]; simp; omega
      · rw [dif_pos (by simp; omega), if_neg h14]; rfl
    · rw [dif_pos (by simp; omega), if_neg h12]; rfl
  · rw [dif_neg (by simp; omega), if_neg hx]; rfl

theorem gzI1_lean (s : Array UInt8) (f : Nat) :
    (if f / 4 % 2 = 1 then
      ((guard (12 ≤ s.size) : Option Unit).bind fun _ =>
        (guard (12 + Deflate.le16 s 10 ≤ s.size) : Option Unit).bind fun _ => some (12 + Deflate.le16 s 10))
     else some 10) = gzI1 s f := by
  unfold gzI1
  by_cases hx : f / 4 % 2 = 1
  · rw [if_pos hx, if_pos hx]
    by_cases h12 : 12 ≤ s.size
    · rw [guard_pos' h12, Option.bind_some, if_pos h12]
      by_cases h14 : 12 + Deflate.le16 s 10 ≤ s.size
      · rw [guard_pos' h14, Option.bind_some, if_pos h14]
      · rw [guard_neg' h14, if_neg h14]; rfl
    · rw [guard_neg' h12, if_neg h12]; rfl
  · rw [if_neg hx, if_neg hx]

/-- FNAME and FCOMMENT: a zero-terminated field at `v` if bit `k` of FLG is set. -/
theorem gz_skip_eq (u : Unspec) (s : Array UInt8) (f k v : Nat) (hk : k ≠ 0) :
    (if h : decide (emod u (ediv u (f : Int) (k : Int)) 2 = 1) = true then
      (if h : (V.vdeflate.wrap.zero_at u (outV s) (v : Int)).isNone = true then (none : Option Int)
       else some (someVal u (.int .int) (α := Int) rfl (V.vdeflate.wrap.zero_at u (outV s) (v : Int)) + 1))
     else some (v : Int)) =
      (Deflate.skipZ s v (f / k % 2 = 1)).map (fun n : Nat => (n : Int)) := by
  rw [ediv_ne u _ _ (by omega), emod_ne u _ _ (by decide), zero_at_eq u s _ v rfl]
  unfold Deflate.skipZ
  by_cases hx : f / k % 2 = 1
  · rw [dif_pos (by simp; omega), if_pos (by simp [hx])]
    cases hz : Deflate.zeroAt s v with
    | none => rfl
    | some z => simp [someVal_some]
  · rw [dif_neg (by simp; omega), if_neg (by simp [hx])]; rfl

/-- FHCRC at `i3`, as `gzipHeader` checks it. -/
def gzHcrc (s : Array UInt8) (f i3 : Nat) : Option Nat :=
  if f / 2 % 2 = 1 then
    if i3 + 2 ≤ s.size ∧ Deflate.le16 s i3 = Deflate.crc32 (s.extract 0 i3) % 65536 then some (i3 + 2)
    else none
  else some i3

theorem gzHcrc_lean (s : Array UInt8) (f i3 : Nat) :
    (if f / 2 % 2 = 1 then
      ((guard (i3 + 2 ≤ s.size) : Option Unit).bind fun _ =>
        (guard (Deflate.le16 s i3 = Deflate.crc32 (s.extract 0 i3) % 65536) : Option Unit).bind fun _ =>
          some (i3 + 2))
     else some i3) = gzHcrc s f i3 := by
  unfold gzHcrc
  by_cases hx : f / 2 % 2 = 1
  · rw [if_pos hx, if_pos hx]
    by_cases hc : i3 + 2 ≤ s.size ∧ Deflate.le16 s i3 = Deflate.crc32 (s.extract 0 i3) % 65536
    · rw [if_pos hc, guard_pos' hc.1, Option.bind_some, guard_pos' hc.2, Option.bind_some]
    · rw [if_neg hc]
      by_cases hc1 : i3 + 2 ≤ s.size
      · rw [guard_pos' hc1, Option.bind_some, guard_neg' (fun h => hc ⟨hc1, h⟩)]; rfl
      · rw [guard_neg' hc1]; rfl
  · rw [if_neg hx, if_neg hx]

/-- `gzipHeader`, stage by stage. -/
theorem gzipHeader_stages (s : Array UInt8) : Deflate.gzipHeader s =
    if 10 ≤ s.size ∧ (Deflate.byteAt s 0 = 0x1f ∧ Deflate.byteAt s 1 = 0x8b ∧ Deflate.byteAt s 2 = 8) ∧
        Deflate.byteAt s 3 / 32 = 0 then
      (gzI1 s (Deflate.byteAt s 3)).bind fun i1 =>
        (Deflate.skipZ s i1 (decide (Deflate.byteAt s 3 / 8 % 2 = 1))).bind fun i2 =>
          (Deflate.skipZ s i2 (decide (Deflate.byteAt s 3 / 16 % 2 = 1))).bind fun i3 =>
            gzHcrc s (Deflate.byteAt s 3) i3
    else none := by
  unfold Deflate.gzipHeader gzI1
  simp only [Option.bind_eq_bind, gzHcrc_lean]
  by_cases h10 : 10 ≤ s.size
  · rw [guard_pos' h10, Option.bind_some]
    by_cases hb : (Deflate.byteAt s 0 = 0x1f && Deflate.byteAt s 1 = 0x8b && Deflate.byteAt s 2 = 8) = true
    · rw [guard_pos' hb, Option.bind_some]
      have hb' : Deflate.byteAt s 0 = 0x1f ∧ Deflate.byteAt s 1 = 0x8b ∧ Deflate.byteAt s 2 = 8 := by
        simpa [and_assoc] using hb
      by_cases h32 : Deflate.byteAt s 3 / 32 = 0
      · have hc : 10 ≤ s.size ∧ (Deflate.byteAt s 0 = 0x1f ∧ Deflate.byteAt s 1 = 0x8b ∧
            Deflate.byteAt s 2 = 8) ∧ Deflate.byteAt s 3 / 32 = 0 := ⟨h10, hb', h32⟩
        rw [guard_pos' h32, Option.bind_some, if_pos hc]
        by_cases hx : Deflate.byteAt s 3 / 4 % 2 = 1
        · rw [if_pos hx]
          by_cases h12 : 12 ≤ s.size
          · rw [guard_pos' h12, Option.bind_some, if_pos h12]
            by_cases h14 : 12 + Deflate.le16 s 10 ≤ s.size
            · rw [guard_pos' h14, Option.bind_some, if_pos h14, if_pos hx]
            · rw [guard_neg' h14, if_neg h14, if_pos hx]; rfl
          · rw [guard_neg' h12, if_neg h12, if_pos hx]; rfl
        · rw [if_neg hx, if_neg hx]
      · have hc : ¬(10 ≤ s.size ∧ (Deflate.byteAt s 0 = 0x1f ∧ Deflate.byteAt s 1 = 0x8b ∧
            Deflate.byteAt s 2 = 8) ∧ Deflate.byteAt s 3 / 32 = 0) := fun h => h32 h.2.2
        rw [guard_neg' h32, if_neg hc]; rfl
    · have hc : ¬(10 ≤ s.size ∧ (Deflate.byteAt s 0 = 0x1f ∧ Deflate.byteAt s 1 = 0x8b ∧
          Deflate.byteAt s 2 = 8) ∧ Deflate.byteAt s 3 / 32 = 0) := fun h => hb (by simp [h.2.1])
      rw [guard_neg' hb, if_neg hc]; rfl
  · have hc : ¬(10 ≤ s.size ∧ (Deflate.byteAt s 0 = 0x1f ∧ Deflate.byteAt s 1 = 0x8b ∧
        Deflate.byteAt s 2 = 8) ∧ Deflate.byteAt s 3 / 32 = 0) := fun h => h10 h.1
    rw [guard_neg' h10, if_neg hc]; rfl

theorem gz_hcrc_eq (u : Unspec) (s : Array UInt8) (f x : Nat) :
    (if h : decide (emod u (ediv u (f : Int) 2) 2 = 1) = true then
      (if h : decide ((x : Int) + 2 > (s.size : Int)) = true then (none : Option Int)
       else if h : (!decide (clip u .nat (Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) (x : Int) +
           clip u .nat (256 * Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) ((x : Int) + 1))) =
           emod u (V.vdeflate.wrap.crc32 u (Seq.take (outV s) (x : Int))) 65536)) = true then none
       else some ((x : Int) + 2))
     else some (x : Int)) = (gzHcrc s f x).map (fun n : Nat => (n : Int)) := by
  rw [ediv_ne u _ _ (by decide), emod_ne u _ _ (by decide)]
  unfold gzHcrc
  by_cases hx : f / 2 % 2 = 1
  · rw [dif_pos (by simp; omega), if_pos hx]
    by_cases h2 : x + 2 ≤ s.size
    · rw [dif_neg (by simp; omega), index_outV u s _ x rfl (by omega),
        index_outV u s _ (x + 1) (by omega) (by omega), take_outV s x (by omega), crc32_eq,
        emod_ne u _ _ (by decide)]
      have b0 := byteAt_lt s x
      have b1 := byteAt_lt s (x + 1)
      rw [clip_nat u (256 * (Deflate.byteAt s (x + 1) : Int)) (by omega), clip_nat u _ (by omega)]
      have hl : (Deflate.le16 s x : Int) = (Deflate.byteAt s x : Int) + 256 * (Deflate.byteAt s (x + 1) : Int) := by
        simp [Deflate.le16]
      by_cases hc : Deflate.le16 s x = Deflate.crc32 (s.extract 0 x) % 65536
      · rw [dif_neg (by simp; omega), if_pos ⟨h2, hc⟩]; rfl
      · rw [dif_pos (by simp; omega), if_neg (fun h => hc h.2)]; rfl
    · rw [dif_pos (by simp; omega), if_neg (fun h => h2 h.1)]; rfl
  · rw [dif_neg (by simp; omega), if_neg hx]; rfl

theorem gzip_header_eq (u : Unspec) (s : Array UInt8) :
    V.vdeflate.wrap.gzip_header u (outV s) =
      Option.map (fun n : Nat => (n : Int)) (Deflate.gzipHeader s) := by
  rw [gzipHeader_stages]
  unfold V.vdeflate.wrap.gzip_header
  simp only [len_outV]
  by_cases h10 : s.size < 10
  · rw [dif_pos (by simp; omega), if_neg (fun h => by omega)]; rfl
  rw [index_outV u s 0 0 rfl (by omega), index_outV u s 1 1 rfl (by omega),
    index_outV u s 2 2 rfl (by omega), index_outV u s 3 3 rfl (by omega)]
  have l3 := byteAt_lt s 3
  simp only [ediv_ne u ((Deflate.byteAt s 3 : Int)) 32 (by decide)]
  by_cases hid : ¬((Deflate.byteAt s 0 = 0x1f ∧ Deflate.byteAt s 1 = 0x8b ∧ Deflate.byteAt s 2 = 8) ∧
      Deflate.byteAt s 3 / 32 = 0)
  · rw [dif_pos (by simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not]; omega), if_neg (fun h => hid h.2)]; rfl
  have hid' := Decidable.of_not_not hid
  refine dite_neg_eq (by simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not]; omega) ?_
  conv => rhs; rw [if_pos ⟨by omega, hid'⟩]
  generalize Deflate.byteAt s 3 = f at l3 hid'
  have hI := gz_i1_eq u s f
  cases h1 : gzI1 s f with
  | none =>
    simp only [h1, Option.map_none] at hI
    simp only [hI, Option.isNone_none, ↓reduceDIte, Option.bind_none, Option.map_none]
  | some v =>
    simp only [h1, Option.map_some] at hI
    simp only [hI, Option.isNone_some, someVal_some, Option.bind_some, Bool.false_eq_true, ↓reduceDIte]
    have g8 := gz_skip_eq u s f 8 v (by decide)
    rw [show ((8 : Nat) : Int) = 8 from rfl] at g8
    cases h2 : Deflate.skipZ s v (decide (f / 8 % 2 = 1)) with
    | none =>
      simp only [h2, Option.map_none] at g8
      simp only [g8, Option.isNone_none, ↓reduceDIte, Option.bind_none, Option.map_none]
    | some w =>
      simp only [h2, Option.map_some] at g8
      simp only [g8, Option.isNone_some, someVal_some, Option.bind_some, Bool.false_eq_true, ↓reduceDIte]
      have g16 := gz_skip_eq u s f 16 w (by decide)
      rw [show ((16 : Nat) : Int) = 16 from rfl] at g16
      cases h3 : Deflate.skipZ s w (decide (f / 16 % 2 = 1)) with
      | none =>
        simp only [h3, Option.map_none] at g16
        simp only [g16, Option.isNone_none, ↓reduceDIte, Option.bind_none, Option.map_none]
      | some x =>
        simp only [h3, Option.map_some] at g16
        simp only [g16, Option.isNone_some, someVal_some, Option.bind_some, Bool.false_eq_true,
          ↓reduceDIte]
        exact gz_hcrc_eq u s f x

/-- The Verus spec's little-endian CRC32 or ISIZE at byte `a`, with its `nat` clips: `le32`. -/
theorem le32_eq (u : Unspec) (s : Array UInt8) (a : Nat) (j0 j1 j2 j3 : Int) (h0 : j0 = a)
    (h1 : j1 = (a + 1 : Nat)) (h2 : j2 = (a + 2 : Nat)) (h3 : j3 = (a + 3 : Nat)) (h : a + 4 ≤ s.size) :
    clip u .nat (clip u .nat (clip u .nat (clip u .nat (clip u .nat (clip u .nat
      (Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) j3 * 256) +
      Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) j2) * 256) +
      Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) j1) * 256) +
      Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) j0) =
      (Deflate.le32 s a : Int) := by
  rw [index_outV u s _ a h0 (by omega), index_outV u s _ (a + 1) h1 (by omega),
    index_outV u s _ (a + 2) h2 (by omega), index_outV u s _ (a + 3) h3 (by omega)]
  unclip
  simp only [Deflate.le32, Deflate.le16, show a + 2 + 1 = a + 3 by omega]
  omega

/-- A gzip member's trailer: CRC32 and ISIZE after the data `o`, whose stream ended at `a`. -/
def gzTrailer (s o : Array UInt8) (a : Nat) (z : Bool) : Option Deflate.Unwrapped := do
  guard (a + 8 ≤ s.size)
  guard (Deflate.le32 s a = Deflate.crc32 o)
  guard (Deflate.le32 s (a + 4) = o.size % 4294967296)
  some { out := o, used := a + 8, zlib := z }

theorem gzipDecode_stages (s : Array UInt8) : Deflate.gzipDecode s =
    (Deflate.gzipHeader s).bind fun h =>
      (Deflate.inflate (Deflate.bitsOf (s.extract h s.size))).bind fun d =>
        gzTrailer s d.out (Deflate.afterStream h d.bits) d.zlib := rfl

theorem gz_trailer_eq (u : Unspec) (s o : Array UInt8) (a : Nat) (z : Bool) :
    (if h : decide ((a : Int) + 8 > (s.size : Int)) = true then none
      else if h4 : ((!decide (clip u .nat (clip u .nat (clip u .nat (clip u .nat (clip u .nat (clip u .nat
          (Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) ((a : Int) + 3) * 256) +
          Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) ((a : Int) + 2)) * 256) +
          Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) ((a : Int) + 1)) * 256) +
          Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) (a : Int)) = V.vdeflate.wrap.crc32 u (outV o))) ||
        (!decide (clip u .nat (clip u .nat (clip u .nat (clip u .nat (clip u .nat (clip u .nat
          (Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) ((a : Int) + 7) * 256) +
          Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) ((a : Int) + 6)) * 256) +
          Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) ((a : Int) + 5)) * 256) +
          Seq.index u (.int (.u 8)) (α := Int) rfl (outV s) ((a : Int) + 4)) =
          emod u (o.size : Int) 4294967296))) = true then none
      else some (outV o, (a : Int) + 8, z)) =
      Option.map (fun r : Deflate.Unwrapped => (outV r.out, (r.used : Int), r.zlib)) (gzTrailer s o a z) := by
  unfold gzTrailer
  simp only [Option.bind_eq_bind]
  by_cases ha : a + 8 ≤ s.size
  · rw [dif_neg (by simp; omega), guard_pos' ha, Option.bind_some,
      le32_eq u s a _ _ _ _ rfl (by omega) (by omega) (by omega) (by omega),
      le32_eq u s (a + 4) _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega),
      crc32_eq, emod_ne u _ _ (by decide)]
    by_cases hc : Deflate.le32 s a = Deflate.crc32 o
    · rw [guard_pos' hc, Option.bind_some]
      by_cases hi : Deflate.le32 s (a + 4) = o.size % 4294967296
      · rw [dif_neg (by simp; omega), guard_pos' hi, Option.bind_some]; simp
      · rw [dif_pos (by simp; omega), guard_neg' hi]; rfl
    · rw [dif_pos (by simp; omega), guard_neg' hc]; rfl
  · rw [dif_pos (by simp; omega), guard_neg' ha]; rfl

theorem gzip_decode_eq (u : Unspec) (s : Array UInt8) :
    V.vdeflate.wrap.gzip_decode u (outV s) =
      Option.map (fun r : Deflate.Unwrapped => (outV r.out, (r.used : Int), r.zlib))
        (Deflate.gzipDecode s) := by
  rw [gzipDecode_stages]
  unfold V.vdeflate.wrap.gzip_decode
  have hH := gzip_header_eq u s
  cases h1 : Deflate.gzipHeader s with
  | none =>
    simp only [h1, Option.map_none] at hH
    simp only [hH, Option.isNone_none, ↓reduceDIte, Option.bind_none, Option.map_none]
  | some h =>
    simp only [h1, Option.map_some] at hH
    simp only [hH, Option.isNone_some, someVal_some, Option.bind_some, Bool.false_eq_true, ↓reduceDIte]
    have hD := inflate_skip_eq u s h
    cases h2 : Deflate.inflate (Deflate.bitsOf (s.extract h s.size)) with
    | none =>
      simp only [h2, Option.map_none] at hD
      simp only [hD, Option.isNone_none, ↓reduceDIte, Option.bind_none, Option.map_none]
    | some d =>
      simp only [h2, Option.map_some] at hD
      simp only [hD, Option.isNone_some, someVal_some, Option.bind_some, Bool.false_eq_true, ↓reduceDIte,
        after_bits_eq, len_outV]
      exact gz_trailer_eq u s d.out _ d.zlib

theorem gzipDecode_used (t : Array UInt8) (r : Deflate.Unwrapped) (h : Deflate.gzipDecode t = some r) :
    8 ≤ r.used ∧ r.used ≤ t.size := by
  rw [gzipDecode_stages] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨hh, -, d, -, h⟩ := h
  unfold gzTrailer at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, hg, _, -, _, -, h⟩ := h
  have hg' : Deflate.afterStream hh d.bits + 8 ≤ t.size := by
    by_cases hc : Deflate.afterStream hh d.bits + 8 ≤ t.size
    · exact hc
    · rw [guard_neg' hc] at hg; simp at hg
  simp only [Option.some.injEq] at h
  subst h
  simp only
  omega

theorem gzipMembers_acc (s : Array UInt8) : ∀ k i (acc : Array UInt8), s.size - i = k →
    Deflate.gzipMembers s i acc = (Deflate.gzipMembers s i #[]).map (acc ++ ·) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro i acc hk
    conv => lhs; rw [Deflate.gzipMembers]
    conv => rhs; rw [Deflate.gzipMembers]
    by_cases hi : i < s.size
    · rw [if_pos hi, if_pos hi]
      simp only [Option.bind_eq_bind]
      cases hd : Deflate.gzipDecode (s.extract i s.size) with
      | none => rfl
      | some r =>
        simp only [Option.bind_some]
        by_cases hu : 0 < r.used
        · rw [if_pos hu, if_pos hu, ih (s.size - (i + r.used)) (by omega) (i + r.used) _ rfl,
            ih (s.size - (i + r.used)) (by omega) (i + r.used) (#[] ++ r.out) rfl]
          cases Deflate.gzipMembers s (i + r.used) #[] with
          | none => rfl
          | some x => simp [Array.append_assoc]
        · rw [if_neg hu, if_neg hu]; rfl
    · rw [if_neg hi, if_neg hi]; simp

theorem extract_extract' (s : Array UInt8) (i n : Nat) :
    (s.extract i s.size).extract n (s.extract i s.size).size = s.extract (i + n) s.size := by
  apply Array.ext'
  simp [Array.toList_extract, List.extract]
  omega

theorem gzip_members_eq (u : Unspec) (s : Array UInt8) : ∀ k i, s.size - i = k →
    V.vdeflate.wrap.gzip_members u (outV (s.extract i s.size)) =
      (Deflate.gzipMembers s i #[]).map outV := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro i hk
    rw [V.vdeflate.wrap.gzip_members, Deflate.gzipMembers]
    by_cases hi : i < s.size
    · rw [dif_neg (by simp; omega), if_pos hi]
      simp only [Option.bind_eq_bind]
      have hD := gzip_decode_eq u (s.extract i s.size)
      cases hd : Deflate.gzipDecode (s.extract i s.size) with
      | none =>
        simp only [hd, Option.map_none] at hD
        simp only [hD, Option.isNone_none, ↓reduceDIte, Option.bind_none, Option.map_none]
      | some r =>
        have hu := gzipDecode_used _ r hd
        have hsz : (s.extract i s.size).size = s.size - i := by simp
        rw [hsz] at hu
        simp only [hd, Option.map_some] at hD
        simp only [hD, Option.isNone_some, someVal_some, Option.bind_some, Bool.false_eq_true,
          ↓reduceDIte, len_outV]
        rw [dif_neg (by simp; omega), if_pos (by omega : 0 < r.used), skip_outV, extract_extract',
          ih (s.size - (i + r.used)) (by omega) (i + r.used) rfl,
          gzipMembers_acc s _ (i + r.used) (#[] ++ r.out) rfl]
        cases Deflate.gzipMembers s (i + r.used) #[] with
        | none => rfl
        | some x =>
          simp only [Option.map_some, Option.isNone_some, someVal_some, Bool.false_eq_true,
            ↓reduceDIte, Option.some.injEq]
          simp [outV, Seq.add_eq]
    · rw [dif_pos (by simp; omega), if_neg hi]; rfl

/-- A whole gzip file: Verus's `gzip_file` is `Deflate.gzipFile`. -/
theorem gzip_file_eq (u : Unspec) (s : Array UInt8) :
    V.vdeflate.wrap.gzip_file u (outV s) = (Deflate.gzipFile s).map outV := by
  unfold V.vdeflate.wrap.gzip_file Deflate.gzipFile
  simp only [len_outV]
  by_cases h0 : s.size = 0
  · rw [dif_pos (by simp only [decide_eq_true_eq]; omega), if_pos h0]; rfl
  · rw [dif_neg (by simp only [decide_eq_true_eq]; omega), if_neg h0]
    have := gzip_members_eq u s _ 0 rfl
    rwa [show s.extract 0 s.size = s by simp] at this

end Bridge
