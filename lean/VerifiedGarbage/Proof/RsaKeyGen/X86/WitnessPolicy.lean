module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStatus
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessChecks
public import VerifiedGarbage.Spec.RsaKeyGen

/-! # Native counting and width selection agree with the reviewed primality policy -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessStatus
open VG

theorem continue_iff {passed : Bool} {rounds uniform checks : Nat} :
    status passed rounds uniform checks = 4 ↔ passed = true ∧ (rounds < 16 ∨ uniform < checks) := by
  cases passed <;> simp [status]
  omega

theorem accepted_iff {passed : Bool} {rounds uniform checks : Nat} :
    status passed rounds uniform checks = 1 ↔ passed = true ∧ 16 ≤ rounds ∧ checks ≤ uniform := by
  cases passed <;> simp [status]

theorem rejected_iff {passed : Bool} {rounds uniform checks : Nat} :
    status passed rounds uniform checks = 3 ↔ passed = false := by
  cases passed <;> simp [status]
  split <;> decide

theorem more_iff {rounds uniform checks : Nat} :
    rounds < 16 ∨ uniform < checks ↔ rounds + 1 ≤ Spec.RsaKeyGen.blindedChecks ∨ uniform < checks := by
  unfold Spec.RsaKeyGen.blindedChecks
  omega

end VG.Proof.RsaKeyGen.X86.WitnessStatus

namespace VG.Proof.RsaKeyGen.X86.WitnessChecks
open VG VG.Impl.RsaKeyGen.X86.WitnessChecks

theorem checks_table : ∀ w < 65, 4 ≤ w → checks w = Spec.RsaKeyGen.checksForSize (64 * w) := by
  decide

theorem checks_eq {w : Nat} (lo : 4 ≤ w) (hi : w ≤ 64) :
    checks w = Spec.RsaKeyGen.checksForSize (64 * w) := checks_table w (by omega) lo

end VG.Proof.RsaKeyGen.X86.WitnessChecks
