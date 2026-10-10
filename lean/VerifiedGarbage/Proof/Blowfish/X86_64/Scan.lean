import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Vector
import VerifiedGarbage.Impl.Blowfish.X86_64

/-!
# One row of a byte plane's scan

`scanAcc p x r`: the accumulator of a plane `p` (its 256 bytes) after the
rows `< r`, scanning for entry `x`: in word `x % 16 / 2`, `p x` if `x`'s row
is one of them, and zero elsewhere (`row_acc`).
-/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64
open VG.Proof.Rc2.X86_64.Sse2 (mask_eq word_por)

theorem itT {c : Prop} [Decidable c] {α : Type} (a b : α) (h : c) : ite c a b = a :=
  ite_eq_left_of_eq_true a b (eq_true h)
theorem itF {c : Prop} [Decidable c] {α : Type} (a b : α) (h : ¬ c) : ite c a b = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

def scanAcc (p : Nat → Byte) (x r : Nat) : BitVec 128 :=
  ofWords fun w => if x / 16 < r ∧ x % 16 / 2 = w then (p x).setWidth 16 else 0

theorem scanAcc_zero (p : Nat → Byte) (x : Nat) : scanAcc p x 0 = 0 :=
  ext_word fun i hi => by
    rw [scanAcc, word_ofWords _ hi]
    simp only [Nat.not_lt_zero, false_and, ite_false]
    exact (BitVec.extractLsb'_zero ..).symm

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
  · simp [h, show 8 * (2 * i) + j = 16 * i + j by omega_arith]
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
    rw [decide_eq_true (show 8 + j < 16 by omega_arith), Bool.true_and]
    exact congrArg _ (by omega_arith)
  · simp [h, show ¬ 8 + j < 16 by omega_arith]

/-- The word of a mask. -/
theorem word_mask (x : Byte) (k : Nat) (hk : k < 256) :
    ((BitVec.ofNat 16 k ^^^ x.setWidth 16) - 1).sshiftRight 15 =
      if x.toNat = k then BitVec.allOnes 16 else 0 := by
  have e : BitVec.ofNat 16 k = (BitVec.ofNat 8 k).setWidth 16 := by
    apply BitVec.eq_of_toNat_eq; simp; omega_arith
  rw [e, BitVec.xor_comm, mask_eq]
  congr 1
  apply propext; constructor
  · intro h; rw [h, BitVec.toNat_ofNat]; omega_arith
  · intro h; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; omega_arith

/-- One row: the even and odd entries masked into the accumulator. -/
theorem row_acc (p : Nat → Byte) (x : Byte) {r : Nat} (data mE mO : BitVec 128)
    (hd : ∀ e < 16, byte data e = p (16 * r + e))
    (hE : ∀ w < 8, word mE w = if x.toNat = 16 * r + 2 * w then BitVec.allOnes 16 else 0)
    (hO : ∀ w < 8, word mO w = if x.toNat = 16 * r + 2 * w + 1 then BitVec.allOnes 16 else 0) :
    (scanAcc p x.toNat r ||| ((data &&& wordsOf 0xFF) &&& mE)) |||
        (XShiftOp.eval .psrlw data (BitVec.ofNat 8 8) &&& mO) = scanAcc p x.toNat (r + 1) := by
  have hx := x.isLt
  refine ext_word fun w hw => ?_
  rw [word_por, word_por, word_pand _ mE, word_low _ hw, word_pand _ mO, word_psrlw8 _ hw, hE w hw, hO w hw,
    scanAcc, scanAcc, word_ofWords _ hw, word_ofWords _ hw, hd _ (by omega_arith), hd _ (by omega_arith)]
  have and1 : ∀ v : BitVec 16, v &&& BitVec.allOnes 16 = v := fun v => BitVec.and_allOnes
  by_cases h1 : x.toNat = 16 * r + 2 * w
  · rw [itT _ _ h1, itF _ _ (show ¬ x.toNat = 16 * r + 2 * w + 1 by omega_arith),
      itF _ _ (show ¬ (x.toNat / 16 < r ∧ x.toNat % 16 / 2 = w) by omega_arith),
      itT _ _ (show x.toNat / 16 < r + 1 ∧ x.toNat % 16 / 2 = w by omega_arith), h1, and1]
    simp
  · by_cases h2 : x.toNat = 16 * r + 2 * w + 1
    · rw [itF _ _ h1, itT _ _ h2,
        itF _ _ (show ¬ (x.toNat / 16 < r ∧ x.toNat % 16 / 2 = w) by omega_arith),
        itT _ _ (show x.toNat / 16 < r + 1 ∧ x.toNat % 16 / 2 = w by omega_arith), h2, and1]
      simp [Nat.add_assoc]
    · rw [itF _ _ h1, itF _ _ h2]
      simp only [BitVec.and_zero, BitVec.or_zero, BitVec.ofNat_eq_ofNat]
      by_cases h3 : x.toNat / 16 < r ∧ x.toNat % 16 / 2 = w
      · rw [itT _ _ h3, itT _ _ (show x.toNat / 16 < r + 1 ∧ x.toNat % 16 / 2 = w by omega_arith)]
      · rw [itF _ _ h3, itF _ _ (show ¬ (x.toNat / 16 < r + 1 ∧ x.toNat % 16 / 2 = w) by omega_arith)]

end VG.Proof.Blowfish.X86_64
