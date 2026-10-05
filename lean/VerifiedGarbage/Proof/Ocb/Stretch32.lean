import VerifiedGarbage.Proof.Ocb.Stretch

/-!
# OCB: `Offset_0` in 32-bit words

Untrusted: everything here is checked by Lean. As `Stretch.lean`, on six
32-bit words (`cat6`): `Stretch` is `Ktop` (four words) and two words
`((x ⋘ 8) ∨ (y ⋙ 24)) ⊕ x` (`stretch_words32`); a shift left by `a` (from 1
to 31) is a shift of each word with the top bits of the next (`shl6`, with
`ror_mask32`), and by 32 a move of each word to the one above (`shl6_32`);
each stage is kept or not by a mask (`sel_mask32`).
-/

namespace VG.Proof.Ocb

/-- Six words, the most significant first. -/
abbrev cat6 (x0 x1 x2 x3 x4 x5 : BitVec 32) : BitVec 192 := x0 ++ x1 ++ x2 ++ x3 ++ x4 ++ x5

/-- Bit `32 k + j` of six words: bit `j` of word `5 − k`. -/
theorem getLsbD_cat6 (x0 x1 x2 x3 x4 x5 : BitVec 32) (i : Nat) :
    (cat6 x0 x1 x2 x3 x4 x5).getLsbD i =
      if i < 32 then x5.getLsbD i else if i < 64 then x4.getLsbD (i - 32) else
      if i < 96 then x3.getLsbD (i - 64) else if i < 128 then x2.getLsbD (i - 96) else
      if i < 160 then x1.getLsbD (i - 128) else x0.getLsbD (i - 160) := by
  simp only [cat6, BitVec.getLsbD_append]
  simp only [Nat.sub_sub, Nat.reduceAdd]
  by_cases h1 : i < 32
  · simp only [h1, ↓reduceIte]
  by_cases h2 : i < 64
  · simp only [h1, h2, show i - 32 < 32 by omega, ↓reduceIte]
  by_cases h3 : i < 96
  · simp only [h1, h2, h3, show ¬ i - 32 < 32 by omega, show i - 64 < 32 by omega, ↓reduceIte]
  by_cases h4 : i < 128
  · simp only [h1, h2, h3, h4, show ¬ i - 32 < 32 by omega, show ¬ i - 64 < 32 by omega,
      show i - 96 < 32 by omega, ↓reduceIte]
  by_cases h5 : i < 160
  · simp only [h1, h2, h3, h4, h5, show ¬ i - 32 < 32 by omega, show ¬ i - 64 < 32 by omega,
      show ¬ i - 96 < 32 by omega, show i - 128 < 32 by omega, ↓reduceIte]
  · simp only [h1, h2, h3, h4, h5, show ¬ i - 32 < 32 by omega, show ¬ i - 64 < 32 by omega,
      show ¬ i - 96 < 32 by omega, show ¬ i - 128 < 32 by omega, ↓reduceIte]

/-- The word `x` shifted left by `a` with the top bits of the next, `y`. -/
abbrev shlW (a : Nat) (x y : BitVec 32) : BitVec 32 := x <<< a ||| y >>> (32 - a)

theorem getLsbD_shlW (a : Nat) (ha : 0 < a) (ha' : a < 32) (x y : BitVec 32) {j : Nat} (hj : j < 32) :
    (shlW a x y).getLsbD j = if j < a then y.getLsbD (32 - a + j) else x.getLsbD (j - a) := by
  simp only [shlW, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hj, decide_true,
    Bool.true_and]
  by_cases h : j < a
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge y (32 - a + j) (by omega)]

/-- A shift of six words left by `a` (from 1 to 31), a word at a time. -/
theorem shl6 (a : Nat) (ha : 0 < a) (ha' : a < 32) (x0 x1 x2 x3 x4 x5 : BitVec 32) :
    cat6 (shlW a x0 x1) (shlW a x1 x2) (shlW a x2 x3) (shlW a x3 x4) (shlW a x4 x5) (x5 <<< a) =
      cat6 x0 x1 x2 x3 x4 x5 <<< a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_cat6 (shlW a x0 x1), BitVec.getLsbD_shiftLeft (cat6 x0 x1 x2 x3 x4 x5), getLsbD_cat6 x0 x1]
  simp only [hi, decide_true, Bool.true_and]
  by_cases h1 : i < 32
  · simp only [h1, ↓reduceIte, BitVec.getLsbD_shiftLeft, decide_true, Bool.true_and]
    by_cases h : i < a
    · simp [h]
    · simp [h, show i - a < 32 by omega]
  by_cases h2 : i < 64
  · simp only [h1, h2, ↓reduceIte, getLsbD_shlW a ha ha' _ _ (show i - 32 < 32 by omega)]
    by_cases h : i - 32 < a
    · simp [h, show ¬ i < a by omega, show i - a < 32 by omega, show 32 - a + (i - 32) = i - a by omega]
    · simp [h, show ¬ i < a by omega, show ¬ i - a < 32 by omega, show i - a < 64 by omega,
        show i - 32 - a = i - a - 32 by omega]
  by_cases h3 : i < 96
  · simp only [h1, h2, h3, ↓reduceIte, getLsbD_shlW a ha ha' _ _ (show i - 64 < 32 by omega)]
    by_cases h : i - 64 < a
    · simp [h, show ¬ i < a by omega, show ¬ i - a < 32 by omega, show i - a < 64 by omega,
        show 32 - a + (i - 64) = i - a - 32 by omega]
    · simp [h, show ¬ i < a by omega, show ¬ i - a < 32 by omega, show ¬ i - a < 64 by omega,
        show i - a < 96 by omega, show i - 64 - a = i - a - 64 by omega]
  by_cases h4 : i < 128
  · simp only [h1, h2, h3, h4, ↓reduceIte, getLsbD_shlW a ha ha' _ _ (show i - 96 < 32 by omega)]
    by_cases h : i - 96 < a
    · simp [h, show ¬ i < a by omega, show ¬ i - a < 32 by omega, show ¬ i - a < 64 by omega,
        show i - a < 96 by omega, show 32 - a + (i - 96) = i - a - 64 by omega]
    · simp [h, show ¬ i < a by omega, show ¬ i - a < 32 by omega, show ¬ i - a < 64 by omega,
        show ¬ i - a < 96 by omega, show i - a < 128 by omega, show i - 96 - a = i - a - 96 by omega]
  by_cases h5 : i < 160
  · simp only [h1, h2, h3, h4, h5, ↓reduceIte, getLsbD_shlW a ha ha' _ _ (show i - 128 < 32 by omega)]
    by_cases h : i - 128 < a
    · simp [h, show ¬ i < a by omega, show ¬ i - a < 32 by omega, show ¬ i - a < 64 by omega,
        show ¬ i - a < 96 by omega, show i - a < 128 by omega, show 32 - a + (i - 128) = i - a - 96 by omega]
    · simp [h, show ¬ i < a by omega, show ¬ i - a < 32 by omega, show ¬ i - a < 64 by omega,
        show ¬ i - a < 96 by omega, show ¬ i - a < 128 by omega, show i - a < 160 by omega,
        show i - 128 - a = i - a - 128 by omega]
  · simp only [h1, h2, h3, h4, h5, ↓reduceIte, getLsbD_shlW a ha ha' _ _ (show i - 160 < 32 by omega)]
    by_cases h : i - 160 < a
    · simp [h, show ¬ i < a by omega, show ¬ i - a < 32 by omega, show ¬ i - a < 64 by omega,
        show ¬ i - a < 96 by omega, show ¬ i - a < 128 by omega, show i - a < 160 by omega,
        show 32 - a + (i - 160) = i - a - 128 by omega]
    · simp [h, show ¬ i < a by omega, show ¬ i - a < 32 by omega, show ¬ i - a < 64 by omega,
        show ¬ i - a < 96 by omega, show ¬ i - a < 128 by omega, show ¬ i - a < 160 by omega,
        show i - 160 - a = i - a - 160 by omega]

/-- A shift of six words left by 32: each word moves to the one above. -/
theorem shl6_32 (x0 x1 x2 x3 x4 x5 : BitVec 32) :
    cat6 x1 x2 x3 x4 x5 0 = cat6 x0 x1 x2 x3 x4 x5 <<< 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_cat6 x1, BitVec.getLsbD_shiftLeft (cat6 x0 x1 x2 x3 x4 x5), getLsbD_cat6 x0 x1]
  simp only [hi, decide_true, Bool.true_and]
  by_cases h1 : i < 32
  · simp [h1]
  by_cases h2 : i < 64
  · simp [h1, h2, show i - 32 < 32 by omega]
  by_cases h3 : i < 96
  · simp [h1, h2, h3, show ¬ i - 32 < 32 by omega, show i - 32 < 64 by omega, show i - 32 - 32 = i - 64 by omega]
  by_cases h4 : i < 128
  · simp [h1, h2, h3, h4, show ¬ i - 32 < 32 by omega, show ¬ i - 32 < 64 by omega, show i - 32 < 96 by omega,
      show i - 32 - 64 = i - 96 by omega]
  by_cases h5 : i < 160
  · simp [h1, h2, h3, h4, h5, show ¬ i - 32 < 32 by omega, show ¬ i - 32 < 64 by omega,
      show ¬ i - 32 < 96 by omega, show i - 32 < 128 by omega, show i - 32 - 96 = i - 128 by omega]
  · simp [h1, h2, h3, h4, h5, show ¬ i - 32 < 32 by omega, show ¬ i - 32 < 64 by omega,
      show ¬ i - 32 < 96 by omega, show ¬ i - 32 < 128 by omega, show i - 32 < 160 by omega,
      show i - 32 - 128 = i - 160 by omega]

/-- Rotating right by `32 − a` and masking off the `a` low bits shifts left
by `a`. -/
theorem ror_mask32 (x : BitVec 32) {a : Nat} (ha : 0 < a) (ha' : a < 32) :
    x.rotateRight (32 - a) &&& (BitVec.allOnes 32 <<< a) = x <<< a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, hi, decide_true, Bool.true_and]
  by_cases hia : i < a
  · simp [hia]
  · simp only [hia, decide_false, Bool.not_false, Bool.true_and]
    simp only [BitVec.getLsbD, show i < 32 - (32 - a) ↔ i < a by omega, hia, ↓reduceIte,
      Nat.mod_eq_of_lt (show 32 - a < 32 by omega)]
    rw [show i - (32 - (32 - a)) = i - a by omega]
    simp [show i - a < 32 by omega]

/-- The choice of `x'` or `x` with a mask of all ones or all zeros. -/
theorem sel_mask32 (x x' : BitVec 32) (b : Bool) :
    x ^^^ ((x' ^^^ x) &&& ((0 : BitVec 32) - (if b then 1 else 0))) = if b then x' else x := by
  cases b
  · simp
  · have h : (0 : BitVec 32) - 1 = BitVec.allOnes 32 := by decide
    simp only [↓reduceIte, h, BitVec.and_allOnes]
    rw [BitVec.xor_comm x' x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Bit `k` of `bottom` (less than 64), as 0 or 1. -/
theorem bit_bottom32 {v : Nat} (hv : v < 64) (k : Nat) :
    (BitVec.ofNat 32 v >>> k) &&& 1 = if v.testBit k then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq,
    Nat.shiftRight_eq_div_pow]
  have h2 : v / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : v / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]; omega

theorem getLsbD_cat4 (k0 k1 k2 k3 : BitVec 32) (i : Nat) :
    (k0 ++ k1 ++ k2 ++ k3).getLsbD i =
      if i < 32 then k3.getLsbD i else if i < 64 then k2.getLsbD (i - 32) else
      if i < 96 then k1.getLsbD (i - 64) else k0.getLsbD (i - 96) := by
  simp only [BitVec.getLsbD_append]
  simp only [Nat.sub_sub, Nat.reduceAdd]
  by_cases h1 : i < 32
  · simp only [h1, ↓reduceIte]
  by_cases h2 : i < 64
  · simp only [h1, h2, show i - 32 < 32 by omega, ↓reduceIte]
  by_cases h3 : i < 96
  · simp only [h1, h2, h3, show ¬ i - 32 < 32 by omega, show i - 64 < 32 by omega, ↓reduceIte]
  · simp only [h1, h2, h3, show ¬ i - 32 < 32 by omega, show ¬ i - 64 < 32 by omega, ↓reduceIte]

/-- `Stretch` in words: `Ktop` and `Ktop[1..64] ⊕ Ktop[9..72]`. -/
theorem stretch_words32 (k0 k1 k2 k3 : BitVec 32) :
    (k0 ++ k1 ++ k2 ++ k3) ++ ((k0 ++ k1 ++ k2 ++ k3).extractLsb' 64 64 ^^^ (k0 ++ k1 ++ k2 ++ k3).extractLsb' 56 64) =
      cat6 k0 k1 k2 k3 ((k0 <<< 8 ||| k1 >>> 24) ^^^ k0) ((k1 <<< 8 ||| k2 >>> 24) ^^^ k1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_cat6, BitVec.getLsbD_append]
  by_cases h1 : i < 32
  · simp only [h1, show i < 64 by omega, ↓reduceIte, BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb',
      decide_true, Bool.true_and, getLsbD_cat4, show ¬ 64 + i < 32 by omega, show ¬ 64 + i < 64 by omega,
      show 64 + i < 96 by omega, show 64 + i - 64 = i by omega, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight]
    by_cases h8 : i < 8
    · simp only [h8, show 56 + i < 64 by omega, show ¬ 56 + i < 32 by omega, ↓reduceIte, decide_true,
        Bool.not_true, Bool.false_and, Bool.false_or, show 56 + i - 32 = 24 + i by omega]
      rw [Bool.xor_comm]
    · simp only [h8, show ¬ 56 + i < 32 by omega, show ¬ 56 + i < 64 by omega, show 56 + i < 96 by omega,
        ↓reduceIte, decide_false, Bool.not_false, Bool.true_and, show 56 + i - 64 = i - 8 by omega,
        BitVec.getLsbD_of_ge k2 (24 + i) (by omega), Bool.or_false]
      rw [Bool.xor_comm]
  by_cases h2 : i < 64
  · simp only [h1, h2, ↓reduceIte, BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb',
      decide_true, Bool.true_and, getLsbD_cat4, show ¬ 64 + i < 32 by omega, show ¬ 64 + i < 64 by omega,
      show ¬ 64 + i < 96 by omega, show 64 + i - 96 = i - 32 by omega, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, show i - 32 < 32 by omega]
    by_cases h8 : i - 32 < 8
    · simp only [h8, show ¬ 56 + i < 32 by omega, show ¬ 56 + i < 64 by omega, show 56 + i < 96 by omega,
        ↓reduceIte, decide_true, Bool.not_true, Bool.false_and, Bool.false_or,
        show 56 + i - 64 = 24 + (i - 32) by omega]
      rw [Bool.xor_comm]
    · simp only [h8, show ¬ 56 + i < 32 by omega, show ¬ 56 + i < 64 by omega, show ¬ 56 + i < 96 by omega,
        ↓reduceIte, decide_false,
        Bool.not_false, Bool.true_and, show 56 + i - 96 = i - 32 - 8 by omega,
        BitVec.getLsbD_of_ge k1 (24 + (i - 32)) (by omega), Bool.or_false]
      rw [Bool.xor_comm]
  · simp only [h1, h2, ↓reduceIte, getLsbD_cat4]
    by_cases h3 : i - 64 < 32
    · simp [h3, show i < 96 by omega]
    by_cases h4 : i - 64 < 64
    · simp [h3, h4, show ¬ i < 96 by omega, show i < 128 by omega, show i - 64 - 32 = i - 96 by omega]
    by_cases h5 : i - 64 < 96
    · simp [h3, h4, h5, show ¬ i < 96 by omega, show ¬ i < 128 by omega, show i < 160 by omega,
        show i - 64 - 64 = i - 128 by omega]
    · simp [h3, h4, h5, show ¬ i < 96 by omega, show ¬ i < 128 by omega, show ¬ i < 160 by omega,
        show i - 64 - 96 = i - 160 by omega]

end VG.Proof.Ocb
