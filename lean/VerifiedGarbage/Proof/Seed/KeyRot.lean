import VerifiedGarbage.Proof.Seed.KeySchedule

/-!
# Rotations of 64-bit words, as two 32-bit words

The key schedule's rotations of `Key0 || Key1` and `Key2 || Key3` by eight
bits (`keyStep`) are two shifts of each word, ORed (`rotr8_hi`, …), which
the 32-bit targets compute.
-/

namespace VG.Proof.Seed

theorem getLsbD_congr (x : BitVec 32) {i j : Nat} (h : i = j) : x.getLsbD i = x.getLsbD j := by rw [h]

theorem rotr8_hi (a b : BitVec 32) : ((a ++ b).rotateRight 8).extractLsb' 32 32 = a >>> 8 ||| b <<< 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 24 with h | h
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), getLsbD_congr a (show 8 % (32 + 32) + (32 + i) - 32 = 8 + i by omega)]
    simp [h]
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    simp only [show 32 + i < 32 + 32 by omega, decide_true, Bool.true_and, show ¬ i < 24 by omega, decide_false,
      Bool.not_false]
    rw [getLsbD_congr b (show 32 + i - (32 + 32 - 8 % (32 + 32)) = i - 24 by omega), BitVec.getLsbD_of_ge a (8 + i) (by omega)]
    simp

theorem rotr8_lo (a b : BitVec 32) : ((a ++ b).rotateRight 8).setWidth 32 = b >>> 8 ||| a <<< 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_rotateRight, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 24 with h | h
  · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    simp [h]
  · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    simp only [show ¬ i < 24 by omega, decide_false, Bool.not_false, Bool.true_and]
    rw [getLsbD_congr a (show 8 % (32 + 32) + i - 32 = i - 24 by omega), BitVec.getLsbD_of_ge b (8 + i) (by omega)]
    simp

theorem rotl8_hi (a b : BitVec 32) : ((a ++ b).rotateLeft 8).extractLsb' 32 32 = a <<< 8 ||| b >>> 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateLeft, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rw [ite_eq_right (by omega)]
  simp only [show 32 + i < 32 + 32 by omega, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 8 with h | h
  · rw [ite_eq_left (by omega), getLsbD_congr b (show 32 + i - 8 % (32 + 32) = 24 + i by omega)]
    simp [h]
  · rw [ite_eq_right (by omega), getLsbD_congr a (show 32 + i - 8 % (32 + 32) - 32 = i - 8 by omega),
      BitVec.getLsbD_of_ge b (24 + i) (by omega)]
    simp [show ¬ i < 8 by omega]

theorem rotl8_lo (a b : BitVec 32) : ((a ++ b).rotateLeft 8).setWidth 32 = b <<< 8 ||| a >>> 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_rotateLeft, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 8 with h | h
  · rw [ite_eq_left (by omega), ite_eq_right (by omega),
      getLsbD_congr a (show 32 + 32 - 8 % (32 + 32) + i - 32 = 24 + i by omega)]
    simp [h]
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), getLsbD_congr b (show i - 8 % (32 + 32) = i - 8 by omega),
      BitVec.getLsbD_of_ge a (24 + i) (by omega)]
    simp [show ¬ i < 8 by omega, show i < 32 + 32 by omega]

end VG.Proof.Seed
