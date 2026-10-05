import VerifiedGarbage.Proof.Ocb.Stretch

/-!
# OCB: `Offset_0` in 32-bit words

Untrusted: everything here is checked by Lean. The facts of `Stretch.lean`
for a target with 32-bit words: `Stretch` is six words (`stretch_words32`),
shifted left by `bottom` (less than 64) in six stages, each kept or not by a
mask from a bit of `bottom` (`sel_mask32`, `bit32`, `bit32_0`); the stages of
1 to 16 bits shift a word at a time (`shl6`), the stage of 32 bits moves the
words (`shl6_32`), and `Offset_0` is the top four words (`top4`).
-/

namespace VG.Proof.Ocb

/-- Shifting `X ++ y` left by `a ≤ 32` shifts `X`, fills it from the top of
`y`, and shifts `y`. -/
private theorem shl_app {n : Nat} (X : BitVec n) (y : BitVec 32) {a : Nat} (ha' : a ≤ 32) :
    (X ++ y) <<< a = ((X <<< a) ||| (y >>> (32 - a)).setWidth n) ++ (y <<< a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases h : i < 32
  · by_cases h2 : i < a
    · simp [h, h2]
    · simp [h, h2, show i - a < 32 by omega]
  · simp only [h, ↓reduceIte, show ¬ i < a by omega, decide_false, Bool.not_false, Bool.true_and,
      show i - 32 < n by omega]
    by_cases h2 : i - 32 < a
    · simp [h2, show i - a < 32 by omega, show 32 - a + (i - 32) = i - a by omega]
    · simp [h2, show ¬ i - a < 32 by omega, BitVec.getLsbD_of_ge y (32 - a + (i - 32)) (by omega),
        show i - a - 32 = i - 32 - a by omega]

/-- Or-ing a word into the low word of `P ++ q`. -/
private theorem or_setWidth_append {n : Nat} (P : BitVec n) (q r : BitVec 32) :
    (P ++ q) ||| r.setWidth (n + 32) = P ++ (q ||| r) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  by_cases h : i < 32
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge r i (by omega)]

private theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] {t e : α} (h : c) : ite c t e = t := by
  simp [h]

private theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] {t e : α} (h : ¬ c) : ite c t e = e := by
  simp [h]

private theorem dec_pos {p : Prop} [Decidable p] (h : p) : decide p = true := decide_eq_true h

private theorem dec_neg {p : Prop} [Decidable p] (h : ¬ p) : decide p = false := decide_eq_false h

private theorem getLsbD_ge32 (x : BitVec 32) {k : Nat} (h : 32 ≤ k) : x.getLsbD k = false :=
  BitVec.getLsbD_of_ge x k h

/-- A shift of six 32-bit words left by `a` (from 1 to 31), a word at a time. -/
theorem shl6 (x₀ x₁ x₂ x₃ x₄ x₅ : BitVec 32) {a : Nat} (ha : 0 < a) (ha' : a < 32) :
    (x₀ <<< a ||| x₁ >>> (32 - a)) ++ (x₁ <<< a ||| x₂ >>> (32 - a)) ++ (x₂ <<< a ||| x₃ >>> (32 - a)) ++
      (x₃ <<< a ||| x₄ >>> (32 - a)) ++ (x₄ <<< a ||| x₅ >>> (32 - a)) ++ (x₅ <<< a) =
      (x₀ ++ x₁ ++ x₂ ++ x₃ ++ x₄ ++ x₅) <<< a := by
  -- `0 < a` is not needed: the shift by 0 is the identity on both sides.
  have _ := ha
  simp only [shl_app _ _ (Nat.le_of_lt ha'), or_setWidth_append, BitVec.setWidth_eq]

/-- A shift of six 32-bit words left by a word. -/
theorem shl6_32 (x₀ x₁ x₂ x₃ x₄ x₅ : BitVec 32) :
    x₁ ++ x₂ ++ x₃ ++ x₄ ++ x₅ ++ (0 : BitVec 32) = (x₀ ++ x₁ ++ x₂ ++ x₃ ++ x₄ ++ x₅) <<< 32 := by
  have hz : ∀ y : BitVec 32, y <<< 32 = 0 := fun y => BitVec.shiftLeft_eq_zero (Nat.le_refl _)
  have hz' : ∀ y : BitVec 32, (0 : BitVec 32) ||| y = y := fun y => by simp
  simp only [shl_app _ _ (Nat.le_refl 32), or_setWidth_append, BitVec.setWidth_eq, Nat.sub_self,
    BitVec.ushiftRight_zero, hz, hz']

/-- The choice of `x'` or `x` with a mask of all ones or all zeros. -/
theorem sel_mask32 (x x' : BitVec 32) (b : Bool) :
    x ^^^ ((x' ^^^ x) &&& ((0 : BitVec 32) - (if b then 1 else 0))) = if b then x' else x := by
  cases b
  · simp
  · have h : (0 : BitVec 32) - 1 = BitVec.allOnes 32 := by decide
    simp only [↓reduceIte, h, BitVec.and_allOnes]
    rw [BitVec.xor_comm x' x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Bit `k` of `bottom` (less than 64), as 0 or 1. -/
theorem bit32 {v : Nat} (hv : v < 64) (k : Nat) :
    (BitVec.ofNat 32 v >>> k) &&& BitVec.ofNat 32 1 = if v.testBit k then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    show (BitVec.ofNat 32 1).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq,
    Nat.shiftRight_eq_div_pow]
  have h2 : v / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : v / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]; omega

/-- Bit 0 of `bottom`, as 0 or 1. -/
theorem bit32_0 {v : Nat} (hv : v < 64) :
    BitVec.ofNat 32 v &&& BitVec.ofNat 32 1 = if v.testBit 0 then 1 else 0 := by
  have h := bit32 hv 0
  rwa [BitVec.ushiftRight_zero] at h

/-- `Stretch` in 32-bit words: `Ktop` (the words `k₀ ++ k₁ ++ k₂ ++ k₃`, `k₀`
the most significant) and `Ktop[1..64] ⊕ Ktop[9..72]`. -/
theorem stretch_words32 (k₀ k₁ k₂ k₃ : BitVec 32) :
    (k₀ ++ k₁ ++ k₂ ++ k₃) ++ ((k₀ ++ k₁ ++ k₂ ++ k₃).extractLsb' 64 64 ^^^ (k₀ ++ k₁ ++ k₂ ++ k₃).extractLsb' 56 64) =
      k₀ ++ k₁ ++ k₂ ++ k₃ ++ (((k₀ <<< 8) ||| (k₁ >>> 24)) ^^^ k₀) ++ (((k₁ <<< 8) ||| (k₂ >>> 24)) ^^^ k₁) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨
      (96 ≤ i ∧ i < 128) ∨ (128 ≤ i ∧ i < 160) ∨ 160 ≤ i by omega)
    with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h
  · simp (disch := omega) only [ite_pos, ite_neg, dec_pos, Bool.true_and,
      show 64 + i - 32 - 32 = i by omega, show 56 + i - 32 = 24 + i by omega]
    exact Bool.xor_comm _ _
  · simp (disch := omega) only [ite_pos, ite_neg, dec_pos, dec_neg, Bool.true_and, Bool.not_true,
      Bool.or_false, show 64 + i - 32 - 32 = i by omega, show 56 + i - 32 - 32 = i - 8 by omega,
      getLsbD_ge32]
    exact Bool.xor_comm _ _
  · simp (disch := omega) only [ite_pos, ite_neg, dec_pos, Bool.true_and,
      show 64 + i - 32 - 32 - 32 = i - 32 by omega,
      show 56 + i - 32 - 32 = i - 8 by omega, show 24 + (i - 32) = i - 8 by omega]
    exact Bool.xor_comm _ _
  · simp (disch := omega) only [ite_pos, ite_neg, dec_pos, dec_neg, Bool.true_and, Bool.not_true,
      Bool.or_false, show 64 + i - 32 - 32 - 32 = i - 32 by omega,
      show 56 + i - 32 - 32 - 32 = i - 32 - 8 by omega, getLsbD_ge32]
    exact Bool.xor_comm _ _
  all_goals simp (disch := omega) only [ite_pos, ite_neg, Nat.sub_sub, Nat.reduceAdd]

/-- The top four of six words. -/
theorem top4 (x₀ x₁ x₂ x₃ x₄ x₅ : BitVec 32) :
    (x₀ ++ x₁ ++ x₂ ++ x₃ ++ x₄ ++ x₅).extractLsb' 64 128 = x₀ ++ x₁ ++ x₂ ++ x₃ := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 64 + i < 32 by omega, show ¬ 64 + i - 32 < 32 by omega, show 64 + i - 32 - 32 = i by omega,
    ↓reduceIte]

/-! ## Words as six-word values, for x86 -/

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

end VG.Proof.Ocb
