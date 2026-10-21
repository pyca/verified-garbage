module

public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Native public bit-length policy for the two safe-prime phases. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate

theorem witnessWidth_word {bits : Nat} (bound : bits ≤ 8192) :
    (BitVec.ofNat 32 bits + 7) >>> 3 = BitVec.ofNat 32 ((bits + 7) / 8) := by
  change (BitVec.ofNat 32 bits + BitVec.ofNat 32 7) >>> 3 = _
  rw [BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : bits + 7 < 2 ^ 32), Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (bits + 7) / 8 < 2 ^ 32)]

theorem checks_word {bits : Nat} (positive : 0 < bits) (bound : bits ≤ 8192) :
    (((if decide (2048 ≤ (BitVec.ofNat 32 bits - 1).toNat) = true then (1 : BitVec 32) else 0) <<< 6) + 64) =
      BitVec.ofNat 32 (VG.Spec.Ffdh.primeChecks bits) := by
  have sub : BitVec.ofNat 32 bits - 1 = BitVec.ofNat 32 (bits - 1) := by
    change BitVec.ofNat 32 bits - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive]
  rw [sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bits - 1 < 2 ^ 32)]
  by_cases small : bits ≤ 2048
  · have flag : ¬ 2048 ≤ bits - 1 := by omega
    simp only [flag, decide_false, Bool.false_eq_true, ite_false,
      VG.Spec.Ffdh.primeChecks, small, ite_true]
    rfl
  · have flag : 2048 ≤ bits - 1 := by omega
    simp only [flag, decide_true, ite_true, VG.Spec.Ffdh.primeChecks, small, ite_false]
    rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
