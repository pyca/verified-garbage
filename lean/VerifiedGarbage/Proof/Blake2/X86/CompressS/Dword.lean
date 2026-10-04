import VerifiedGarbage.Proof.Framework.X86.SseDword

/-!
# BLAKE2s on x86 (32-bit): what the doubleword lemmas leave out

`movd` stated on the doublewords of its result, a rotation to the right as
two shifts, and the rotation by 16 in both directions (the framework's
`dword_rot16` rotates to the left; BLAKE2s rotates to the right).
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86

theorem dword_movd_0 (v : BitVec 32) : dword ((0 : BitVec 96) ++ v) 0 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
    Bool.true_and, Nat.mul_zero, Nat.zero_add, ite_true]

theorem dword_movd_1 (v : BitVec 32) : dword ((0 : BitVec 96) ++ v) 1 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true,
    Bool.true_and, Nat.mul_one, show ¬ 32 + j < 32 by omega, ite_false]
  simp

/-- A rotation to the right as two shifts. -/
theorem shr_or_shl (x : BitVec 32) {k : Nat} (hk : k < 32) :
    x >>> k ||| x <<< (32 - k) = x.rotateRight k := by
  simp only [BitVec.rotateRight, BitVec.rotateRightAux, Nat.mod_eq_of_lt hk]

theorem rotateLeft_16 (x : BitVec 32) : x.rotateLeft 16 = x.rotateRight 16 := by
  simp only [BitVec.rotateLeft, BitVec.rotateLeftAux, BitVec.rotateRight, BitVec.rotateRightAux,
    Nat.reduceMod, Nat.reduceSub]
  exact BitVec.or_comm _ _

end VG.Proof.Blake2.X86.CompressS
