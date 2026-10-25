module

public import VerifiedGarbage.Proof.Framework.PowLit

/-! # The key schedule's halves, with shifts -/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Key

/-- Two shifts keep the low `n` bits. -/
theorem mask_shift (y : BitVec 64) (n : Nat) (hn : n ≤ 64) :
    (y <<< (64 - n)) >>> (64 - n) = (y.setWidth n).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hj,
    decide_true, Bool.true_and]
  by_cases h : j < n
  · simp (disch := omega) only [h, decide_true, show 64 - n + j < 64 by omega,
      show ¬ 64 - n + j < 64 - n by omega, decide_false, Bool.not_false, Bool.true_and,
      show 64 - n + j - (64 - n) = j by omega]
  · simp only [h, decide_false, show ¬ 64 - n + j < 64 by omega, Bool.false_and]

/-- A rotation of a 28-bit half, as the code computes it. -/
theorem rot28_word (x : BitVec 28) (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    ((x.setWidth 64 <<< n ^^^ x.setWidth 64 >>> (28 - n)) <<< 36) >>> 36 =
      (x.rotateLeft n).setWidth 64 := by
  rw [show (36 : Nat) = 64 - 28 from rfl, mask_shift _ 28 (by decide)]
  apply congrArg (BitVec.setWidth 64)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hn']
  by_cases h : j < n
  · simp (disch := omega) [h, hj, show j < 64 by omega, show 28 - n + j < 64 by omega]
  · simp (disch := omega) [h, hj, show j < 64 by omega, show j - n < 64 by omega,
      BitVec.getLsbD_of_ge]

/-- C and D joined, as the code computes it. -/
theorem pack28_word (c d : BitVec 28) :
    ((c.setWidth 64 <<< 28 ^^^ d.setWidth 64).setWidth 56) = c ++ d := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  by_cases h : j < 28
  · simp (disch := omega) [h, show j < 64 by omega]
  · simp (disch := omega) [h, show j < 64 by omega, show j - 28 < 64 by omega,
      BitVec.getLsbD_of_ge]

end VG.Proof.TripleDes.RISCV64.Key
