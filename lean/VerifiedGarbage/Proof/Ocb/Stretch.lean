import VerifiedGarbage.Proof.Ocb.Spec

/-!
# OCB: `Offset_0` in 64-bit words

Untrusted: everything here is checked by Lean. `Stretch` (§4.2) is 192 bits:
`Ktop` (the words `H ++ L`) and `Ktop[1..64] ⊕ Ktop[9..72]`, the word
`((H ⋘ 8) ∨ (L ⋙ 56)) ⊕ H` (`stretch_words`). An implementation shifts it
left by `bottom` (less than 64) in six stages, by 1, 2, 4, 8, 16 and 32 bits,
each kept or not by a mask from a bit of `bottom` (`sel_mask`), on three
words (`shl3`, with `ror_mask`), so that `Offset_0` is the top 128 bits
(`offset_shl`, `shl_stages`).
-/

namespace VG.Proof.Ocb

/-- Rotating right by `64 − a` and masking off the `a` low bits shifts left
by `a`. -/
theorem ror_mask (x : BitVec 64) {a : Nat} (ha : 0 < a) (ha' : a < 64) :
    x.rotateRight (64 - a) &&& (BitVec.allOnes 64 <<< a) = x <<< a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, hi, decide_true, Bool.true_and]
  by_cases hia : i < a
  · simp [hia]
  · simp only [hia, decide_false, Bool.not_false, Bool.true_and]
    simp only [BitVec.getLsbD, show i < 64 - (64 - a) ↔ i < a by omega, hia, ↓reduceIte,
      Nat.mod_eq_of_lt (show 64 - a < 64 by omega)]
    rw [show i - (64 - (64 - a)) = i - a by omega]
    simp [show i - a < 64 by omega]

/-- Bit `k` of `bottom` (less than 64), as 0 or 1. -/
theorem bit_bottom {v : Nat} (hv : v < 64) (k : Nat) :
    (BitVec.ofNat 64 v >>> k) &&& BitVec.signExtend 64 (1 : BitVec 32) =
      if v.testBit k then 1 else 0 := by
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  rw [e1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  have h2 : v / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : v / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]; omega

/-- A shift of three words left by `a` (from 1 to 63), a word at a time. -/
theorem shl3 (x y z : BitVec 64) {a : Nat} (ha : 0 < a) (ha' : a < 64) :
    (x <<< a ||| y >>> (64 - a)) ++ (y <<< a ||| z >>> (64 - a)) ++ (z <<< a) = (x ++ y ++ z) <<< a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  rcases (show i < 64 ∨ (64 ≤ i ∧ i < 128) ∨ (128 ≤ i ∧ i < 192) by omega) with h | ⟨h, h'⟩ | ⟨h, h'⟩
  · by_cases h2 : i < a
    · simp [h, h2]
    · simp [h, h2, show i - a < 64 by omega]
  · simp only [show ¬ i < 64 by omega, show i - 64 < 64 by omega, show ¬ i < a by omega, ↓reduceIte,
      decide_false, Bool.not_false, Bool.true_and]
    by_cases h2 : i - 64 < a
    · simp [h2, show i - a < 64 by omega, show 64 - a + (i - 64) = i - a by omega]
    · simp [h2, show ¬ i - a < 64 by omega, BitVec.getLsbD_of_ge z (64 - a + (i - 64)) (by omega),
        show i - a - 64 = i - 64 - a by omega, show i - 64 - a < 64 by omega]
  · simp only [show ¬ i < 64 by omega, show ¬ i - 64 < 64 by omega, show ¬ i < a by omega, ↓reduceIte,
      decide_false, Bool.not_false, Bool.true_and, show ¬ i - a < 64 by omega]
    by_cases h2 : i - 128 < a
    · simp [show i - 64 - 64 < a by omega, show i - a - 64 < 64 by omega,
        show 64 - a + (i - 64 - 64) = i - a - 64 by omega]
    · simp [show ¬ i - 64 - 64 < a by omega, show i - 64 - 64 < 64 by omega, show ¬ i - a - 64 < 64 by omega,
        BitVec.getLsbD_of_ge y (64 - a + (i - 64 - 64)) (by omega), show i - a - 64 - 64 = i - 64 - 64 - a by omega]

/-- The choice of `x'` or `x` with a mask of all ones or all zeros. -/
theorem sel_mask (x x' : BitVec 64) (b : Bool) :
    x ^^^ ((x' ^^^ x) &&& ((0 : BitVec 64) - (if b then 1 else 0))) = if b then x' else x := by
  cases b
  · simp
  · have h : (0 : BitVec 64) - 1 = BitVec.allOnes 64 := by decide
    simp only [↓reduceIte, h, BitVec.and_allOnes]
    rw [BitVec.xor_comm x' x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- `Stretch` in words. -/
theorem stretch_words (h l : BitVec 64) :
    (h ++ l) ++ ((h ++ l).extractLsb' 64 64 ^^^ (h ++ l).extractLsb' 56 64) =
      h ++ l ++ (((h <<< 8) ||| (l >>> 56)) ^^^ h) := by
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.xor_comm _ h]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hi, decide_true,
    Bool.true_and, show ¬ 64 + i < 64 by omega, ↓reduceIte, show 64 + i - 64 = i by omega]
  congr 1
  by_cases h8 : i < 8
  · simp [h8, show 56 + i < 64 by omega]
  · simp [h8, show ¬ 56 + i < 64 by omega, show 56 + i - 64 = i - 8 by omega,
      BitVec.getLsbD_of_ge l (56 + i) (by omega)]

/-- The top 128 bits of `Stretch` shifted left by `b ≤ 64` are its bits from
`64 − b`. -/
theorem offset_shl (s : BitVec 192) {b : Nat} (hb : b ≤ 64) :
    (s <<< b).extractLsb' 64 128 = s.extractLsb' (64 - b) 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    show 64 + i < 192 by omega, show ¬ 64 + i < b by omega, decide_false, Bool.not_false]
  congr 1; omega

/-- A shift left by `k` if `c`. -/
def shlIf (c : Bool) (k : Nat) (x : BitVec 192) : BitVec 192 := if c then x <<< k else x

/-- The six stages shift left by `bottom`. -/
theorem shl_stages (s : BitVec 192) {v : Nat} (hv : v < 64) :
    shlIf (v.testBit 5) 32 (shlIf (v.testBit 4) 16 (shlIf (v.testBit 3) 8 (shlIf (v.testBit 2) 4
      (shlIf (v.testBit 1) 2 (shlIf (v.testBit 0) 1 s))))) = s <<< v := by
  have key : ∀ (c : Bool) (k : Nat) (x : BitVec 192), shlIf c k x = x <<< (if c then k else 0) := by
    intro c k x; cases c <;> simp [shlIf]
  simp only [key, ← BitVec.shiftLeft_add]
  congr 1
  revert v
  decide

end VG.Proof.Ocb
