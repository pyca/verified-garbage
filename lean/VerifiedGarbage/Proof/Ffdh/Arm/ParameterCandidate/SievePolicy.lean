module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Public requested-width bounds for RSA's trial table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)

theorem trialCount_positive (n : Nat) : 0 < trialCount n := by
  unfold trialCount; split <;> omega

theorem trialCount_bound (n : Nat) : trialCount n ≤ 1024 := by
  unfold trialCount; split <;> omega

theorem trialCount_lower (n : Nat) : 53 ≤ trialCount n := by
  unfold trialCount; split <;> omega

theorem trialCount_word {n : Nat} (bound : n ≤ 1024) :
    (((if decide (129 ≤ (BitVec.ofNat 32 n).toNat) = true then (1 : BitVec 32) else 0) <<< 9) + 512) =
      BitVec.ofNat 32 (trialCount n) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2^32)]
  unfold trialCount
  by_cases small : n ≤ 128
  · have flag : ¬129 ≤ n := by omega
    simp only [flag, decide_false, Bool.false_eq_true, ite_false, small, ite_true]
    rfl
  · have flag : 129 ≤ n := by omega
    simp only [flag, decide_true, ite_true, small, ite_false]
    rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
