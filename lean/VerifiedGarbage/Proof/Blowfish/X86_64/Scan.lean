module

import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Vector
public import VerifiedGarbage.Impl.Blowfish.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Framework.Mem

/-!
# One row of a byte plane's scan

`scanAcc p x r`: the accumulator of a plane `p` (its 256 bytes) after the
rows `< r`, scanning for entry `x`: in byte lane `x % 16`, `p x` if `x`'s row
is one of them, and zero elsewhere (`row_acc`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64
open VG.Proof.Rc2.X86_64.Sse2 (mask_eq word_por)

theorem itT {c : Prop} [Decidable c] {α : Type} (a b : α) (h : c) : ite c a b = a :=
  ite_eq_left_of_eq_true a b (eq_true h)
theorem itF {c : Prop} [Decidable c] {α : Type} (a b : α) (h : ¬ c) : ite c a b = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

def scanAcc (p : Nat → Byte) (x r : Nat) : BitVec 128 :=
  ofWords fun w => if x / 16 < r ∧ x % 16 / 2 = w then ((p x).setWidth 16 <<< (8 * (x % 2))) else 0

theorem scanAcc_zero (p : Nat → Byte) (x : Nat) : scanAcc p x 0 = 0 :=
  ext_word fun i hi => by
    rw [scanAcc, word_ofWords _ hi]
    simp only [Nat.not_lt_zero, false_and, ite_false]
    exact (BitVec.extractLsb'_zero ..).symm

theorem word_or (a b : BitVec 128) (i : Nat) : word (a ||| b) i = word a i ||| word b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [getLsbD_word, BitVec.getLsbD_or, decide_eq_true hj, Bool.true_and]

theorem word_pand (a b : BitVec 128) (i : Nat) : word (a &&& b) i = word a i &&& word b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [getLsbD_word, BitVec.getLsbD_and, decide_eq_true hj, Bool.true_and]

theorem word_pxor (a b : BitVec 128) (i : Nat) : word (a ^^^ b) i = word a i ^^^ word b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [getLsbD_word, BitVec.getLsbD_xor, decide_eq_true hj, Bool.true_and]

/-- The even bytes of a value, as words. -/
theorem word_low (a : BitVec 128) {i : Nat} (hi : i < 8) :
    word (a &&& wordsOf 0xFF) i = (byte a (2 * i)).setWidth 16 := by
  rw [word_pand, wordsOf, word_ofWords _ hi]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [getLsbD_word, BitVec.getLsbD_and, decide_eq_true hj, Bool.true_and, byte,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat]
  by_cases h : j < 8
  · simp [h, show 8 * (2 * i) + j = 16 * i + j by omega]
    rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.testBit_two_pow_sub_one]; simp [h]
  · simp only [h, decide_false, Bool.false_and]
    rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.testBit_two_pow_sub_one]; simp [h]

/-- The odd bytes of a value, as words. -/
theorem word_psrlw8 (a : BitVec 128) {i : Nat} (hi : i < 8) :
    word (XShiftOp.eval .psrlw a (BitVec.ofNat 8 8)) i = (byte a (2 * i + 1)).setWidth 16 := by
  simp only [XShiftOp.eval, BitVec.toNat_ofNat, show 8 % 2 ^ 8 = 8 by rfl, show ¬ 15 < 8 by decide,
    ite_false, word_ofWords _ hi]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_ushiftRight, getLsbD_word, byte, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
  by_cases h : j < 8
  · simp only [h, decide_true, Bool.true_and]
    rw [decide_eq_true (show 8 + j < 16 by omega), Bool.true_and]
    exact congrArg _ (by omega)
  · simp [h, show ¬ 8 + j < 16 by omega]

/-- The word of a mask. -/
theorem word_mask (x : Byte) (k : Nat) (hk : k < 256) :
    ((BitVec.ofNat 16 k ^^^ x.setWidth 16) - 1).sshiftRight 15 =
      if x.toNat = k then BitVec.allOnes 16 else 0 := by
  have e : BitVec.ofNat 16 k = (BitVec.ofNat 8 k).setWidth 16 := by
    apply BitVec.eq_of_toNat_eq; simp; omega
  rw [e, BitVec.xor_comm, mask_eq]
  congr 1
  apply propext; constructor
  · intro h; rw [h, BitVec.toNat_ofNat]; omega
  · intro h; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega

/-- The byte mask of a row's word. -/
def byteMask (x k : Nat) : BitVec 16 :=
  (if x = k then 255#16 else 0#16) ||| (if x = k + 1 then 65280#16 else 0#16)

/-- One row: the selected byte stays in its original byte lane. -/
theorem row_acc (p : Nat → Byte) (x : Byte) {r : Nat} (data mE : BitVec 128)
    (hd : ∀ e < 16, byte data e = p (16 * r + e))
    (hE : ∀ w < 8, word mE w = byteMask x.toNat (16 * r + 2 * w)) :
    scanAcc p x.toNat r ||| (data &&& mE) = scanAcc p x.toNat (r + 1) := by
  have hx := x.isLt
  refine ext_word fun w hw => ?_
  rw [word_por, word_pand, hE w hw, scanAcc, scanAcc, word_ofWords _ hw, word_ofWords _ hw]
  have lo : word data w &&& 255#16 = (p (16 * r + 2 * w)).setWidth 16 := by
    have h := word_low data hw
    rw [word_pand, wordsOf, word_ofWords _ hw, hd _ (by omega)] at h
    exact h
  have hi : word data w &&& 65280#16 = (p (16 * r + (2 * w + 1))).setWidth 16 <<< 8 := by
    rw [← hd _ (by omega)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, getLsbD_word, byte, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> exact congrArg _ (by omega)
  by_cases h1 : x.toNat = 16 * r + 2 * w
  · rw [byteMask, ite_eq_left h1, ite_eq_right (show ¬ x.toNat = 16 * r + 2 * w + 1 by omega),
      BitVec.or_zero, lo,
      ite_eq_right (show ¬ (x.toNat / 16 < r ∧ x.toNat % 16 / 2 = w) by omega),
      ite_eq_left (show x.toNat / 16 < r + 1 ∧ x.toNat % 16 / 2 = w by omega)]
    rw [show x.toNat % 2 = 0 by omega, h1]
    simp
  · by_cases h2 : x.toNat = 16 * r + 2 * w + 1
    · rw [byteMask, ite_eq_right h1, ite_eq_left h2, BitVec.zero_or, hi,
        ite_eq_right (show ¬ (x.toNat / 16 < r ∧ x.toNat % 16 / 2 = w) by omega),
        ite_eq_left (show x.toNat / 16 < r + 1 ∧ x.toNat % 16 / 2 = w by omega)]
      rw [show x.toNat % 2 = 1 by omega, h2]
      simp [Nat.add_assoc]
    · rw [byteMask, ite_eq_right h1, ite_eq_right h2, BitVec.or_zero, BitVec.and_zero, BitVec.or_zero]
      by_cases h3 : x.toNat / 16 < r ∧ x.toNat % 16 / 2 = w
      · rw [itT _ _ h3, itT _ _ (show x.toNat / 16 < r + 1 ∧ x.toNat % 16 / 2 = w by omega)]
      · rw [itF _ _ h3, itF _ _ (show ¬ (x.toNat / 16 < r + 1 ∧ x.toNat % 16 / 2 = w) by omega)]

end VG.Proof.Blowfish.X86_64
