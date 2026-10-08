import Lspec.Deflate.Spec

/-!
# Checks on the DEFLATE spec

Theorems a reviewer can read instead of the definitions: that the spec
reproduces the RFC's own examples and tables, and that its decoding steps
behave as the text describes.
-/

namespace Deflate

/-! ## 3.2.2: the RFC's examples -/

/-- The first example: lengths (2, 1, 3, 3) give A = 10, B = 0, C = 110,
D = 111. -/
theorem rfc_example_ABCD :
    code #[2, 1, 3, 3] = #[(2, 0b10), (1, 0b0), (3, 0b110), (3, 0b111)] := by decide

/-- The worked example: lengths (3, 3, 3, 3, 3, 2, 4, 4) for ABCDEFGH. -/
theorem rfc_example_ABCDEFGH :
    code #[3, 3, 3, 3, 3, 2, 4, 4] =
      #[(3, 0b010), (3, 0b011), (3, 0b100), (3, 0b101), (3, 0b110),
        (2, 0b00), (4, 0b1110), (4, 0b1111)] := by decide

/-- Its `next_code` column: N = 1..4 give 0, 0, 2, 14. -/
theorem rfc_example_next_code :
    (List.range 4).map (fun i => nextCode #[3, 3, 3, 3, 3, 2, 4, 4] (i + 1)) = [0, 0, 2, 14] := by
  decide

/-! ## 3.2.6: the fixed code's table -/

/-- The "Codes" column of the fixed lit/length table, at each range's ends. -/
theorem fixed_lit_codes :
    (code fixedLit)[0]! = (8, 0b00110000) ∧ (code fixedLit)[143]! = (8, 0b10111111) ∧
    (code fixedLit)[144]! = (9, 0b110010000) ∧ (code fixedLit)[255]! = (9, 0b111111111) ∧
    (code fixedLit)[256]! = (7, 0b0000000) ∧ (code fixedLit)[279]! = (7, 0b0010111) ∧
    (code fixedLit)[280]! = (8, 0b11000000) ∧ (code fixedLit)[287]! = (8, 0b11000111) := by
  decide +kernel

/-- Both fixed codes are complete, so every bit string decodes to some symbol. -/
theorem fixed_complete : complete fixedLit ∧ complete fixedDist := by decide +kernel

/-- The fixed distance code is the 5-bit binary number of the symbol. -/
theorem fixed_dist_code : ∀ i : Fin 32, (code fixedDist)[i.val]! = (5, i.val) := by
  decide +kernel

/-! ## 3.2.5: the tables -/

/-- The length table's ranges follow on from one another (each symbol's
lengths start where the previous one's end), from 3 for symbol 257. -/
theorem len_table_ranges :
    lenTable.size = 29 ∧ lenTable[0]! = (3, 0) ∧
    ∀ i : Fin 27, (lenTable[i.val + 1]!).1 = (lenTable[i.val]!).1 + 2 ^ (lenTable[i.val]!).2 := by
  decide

/-- Symbol 284 with its 5 extra bits reaches 258, one past the table's
227-257, and 285 is 258 with no extra bits (open point 6). -/
theorem len_table_top :
    lenTable[27]! = (227, 5) ∧ 227 + 2 ^ 5 - 1 = 258 ∧ lenTable[28]! = (258, 0) := by decide

/-- The distance table's ranges follow on from one another, from 1 for symbol
0 to 32768 for symbol 29: "the distance is drawn from (1..32,768)". -/
theorem dist_table_ranges :
    distTable.size = 30 ∧ distTable[0]! = (1, 0) ∧
    (∀ i : Fin 29,
      (distTable[i.val + 1]!).1 = (distTable[i.val]!).1 + 2 ^ (distTable[i.val]!).2) ∧
    (distTable[29]!).1 + 2 ^ (distTable[29]!).2 - 1 = 32768 := by
  decide

/-! ## 3.2.1: decoding a symbol -/

theorem decodeSym_go_spec (c : Array (Nat × Nat)) (b : Bits) (p l : Nat) :
    ∀ s q, decodeSym.go c b p l = some (s, q) → s < c.size ∧ p < q ∧ q ≤ b.size := by
  induction l using decodeSym.go.induct c b p with
  | case1 l h =>
    intro s q hs; rw [decodeSym.go] at hs; simp [h] at hs
  | case2 l h n hn =>
    intro s q hs; rw [decodeSym.go] at hs; simp [h, hn] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have := Array.findIdx?_eq_some_iff_findIdx_eq.mp hn
    refine ⟨this.1, ?_, ?_⟩ <;> omega
  | case3 l h hn ih =>
    intro s q hs; rw [decodeSym.go] at hs; simp [h, hn] at hs
    exact ih s q hs

/-- A decoded symbol is in the alphabet, and its code is at least one bit and
in the stream. So the "not reached" guards after `decodeSym` always hold. -/
theorem decodeSym_spec {c : Array (Nat × Nat)} {b : Bits} {p s q : Nat}
    (h : decodeSym c b p = some (s, q)) : s < c.size ∧ p < q ∧ q ≤ b.size :=
  decodeSym_go_spec c b p 1 s q h

end Deflate
