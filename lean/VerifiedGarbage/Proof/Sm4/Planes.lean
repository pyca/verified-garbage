import VerifiedGarbage.Impl.Sm4.Planes
import VerifiedGarbage.Proof.Sm4.Bitsliced
import VerifiedGarbage.Proof.Sm4.Bitsliced32

/-! # The bits of the key schedule's constant planes -/

namespace VG.Proof.Sm4

open VG.Impl.Sm4 (planeOf fkWord planeOf32 fkLE bitsOf planeBits)

theorem testBit_mask (c : Bool) (w s p : Nat) :
    (if c then (2 ^ w - 1) <<< s else 0).testBit p = (c && decide (s ≤ p ∧ p < s + w)) := by
  cases c
  · simp
  · simp only [ite_true, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Bool.true_and]
    by_cases h : s ≤ p <;> simp [h] <;> omega_arith

/-- Bit `p` of a plane of 16 bits per byte: bit `j` of byte `p / 16`. -/
theorem testBit_planeBits16 {n j p : Nat} (hp : p < 64) :
    (planeBits n 16 j).testBit p = n.testBit (8 * (3 - p / 16) + j) := by
  simp only [planeBits, Nat.testBit_or, testBit_mask]
  rcases (by omega_arith : p < 16 ∨ 16 ≤ p ∧ p < 32 ∨ 32 ≤ p ∧ p < 48 ∨ 48 ≤ p) with h | h | h | h
  · rw [show 8 * (3 - p / 16) + j = 24 + j by omega_arith]
    simp (disch := omega_arith) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.and_false,
      Bool.or_false]
  · rw [show 8 * (3 - p / 16) + j = 16 + j by omega_arith]
    simp (disch := omega_arith) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.and_false,
      Bool.or_false, Bool.false_or]
  · rw [show 8 * (3 - p / 16) + j = 8 + j by omega_arith]
    simp (disch := omega_arith) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.and_false,
      Bool.or_false, Bool.false_or]
  · rw [show 8 * (3 - p / 16) + j = j by omega_arith]
    simp (disch := omega_arith) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.and_false,
      Bool.or_false, Bool.false_or]

/-- Bit `p` of a plane of 8 bits per byte: bit `j` of byte `p / 8`. -/
theorem testBit_planeBits8 {n j p : Nat} (hp : p < 32) :
    (planeBits n 8 j).testBit p = n.testBit (8 * (3 - p / 8) + j) := by
  simp only [planeBits, Nat.testBit_or, testBit_mask]
  rcases (by omega_arith : p < 8 ∨ 8 ≤ p ∧ p < 16 ∨ 16 ≤ p ∧ p < 24 ∨ 24 ≤ p) with h | h | h | h
  · rw [show 8 * (3 - p / 8) + j = 24 + j by omega_arith]
    simp (disch := omega_arith) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.and_false,
      Bool.or_false]
  · rw [show 8 * (3 - p / 8) + j = 16 + j by omega_arith]
    simp (disch := omega_arith) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.and_false,
      Bool.or_false, Bool.false_or]
  · rw [show 8 * (3 - p / 8) + j = 8 + j by omega_arith]
    simp (disch := omega_arith) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.and_false,
      Bool.or_false, Bool.false_or]
  · rw [show 8 * (3 - p / 8) + j = j by omega_arith]
    simp (disch := omega_arith) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.and_false,
      Bool.or_false, Bool.false_or]

theorem testBit_bitsOf (f : Nat → Bool) (n c : Nat) :
    (bitsOf f n).testBit c = (decide (c < n) && f c) := by
  induction n with
  | zero => simp [bitsOf]
  | succ n ih =>
    rw [bitsOf, Nat.testBit_or, ih]
    have hlt : decide (c < n + 1) = (decide (c < n) || decide (c = n)) := by
      by_cases h : c < n <;> by_cases h' : c = n <;> simp [h, h'] <;> omega_arith
    rw [hlt]
    by_cases hcn : c = n
    · subst hcn; split <;> simp_all
    · split <;> simp [hcn, Ne.symm hcn]

theorem planeOf_bit (x : BitVec 32) (j : Nat) {p : Nat} (hp : p < 64) :
    (planeOf x j).getLsbD p = x.getLsbD (8 * (3 - p / 16) + j) := by
  rw [planeOf, BitVec.getLsbD_ofNat, testBit_planeBits16 hp]
  simp [hp, BitVec.testBit_toNat]

theorem planeOf_rel (x : BitVec 32) : WordRel (planeOf x) (fun _ => x) := fun b _ i hi j _ => by
  rw [planeOf_bit x j (by omega_arith), show (16 * i + b) / 16 = i by omega_arith]

theorem fkWord_bit {h t : Nat} (ht : t < 64) :
    (fkWord h).getLsbD t = (Spec.Sm4.fk.getD (2 * h + t / 32) 0).getLsbD (8 * (3 - t % 32 / 8) + t % 8) := by
  rw [fkWord, BitVec.getLsbD_ofNat, testBit_bitsOf]
  simp [ht, BitVec.testBit_toNat]

theorem planeOf32_bit (x : BitVec 32) (j : Nat) {p : Nat} (hp : p < 32) :
    (planeOf32 x j).getLsbD p = x.getLsbD (8 * (3 - p / 8) + j) := by
  rw [planeOf32, BitVec.getLsbD_ofNat, testBit_planeBits8 hp]
  simp [hp, BitVec.testBit_toNat]

theorem planeOf32_rel (x : BitVec 32) : W32.WordRel (planeOf32 x) (fun _ => x) := fun b _ i hi j _ => by
  rw [planeOf32_bit x j (by omega_arith), show (8 * i + b) / 8 = i by omega_arith]

theorem fkLE_bit {w t : Nat} (ht : t < 32) :
    (fkLE w).getLsbD t = (Spec.Sm4.fk.getD w 0).getLsbD (8 * (3 - t / 8) + t % 8) := by
  rw [fkLE, BitVec.getLsbD_ofNat, testBit_bitsOf]
  simp [ht, BitVec.testBit_toNat]

end VG.Proof.Sm4
