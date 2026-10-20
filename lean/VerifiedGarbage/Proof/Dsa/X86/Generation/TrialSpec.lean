module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialState
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # The reciprocal table implements the specification's trial-division policy -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.RsaKeyGen

/-- Rounding the bit width up to a 64-bit limb does not cross the table threshold. -/
theorem trialStatus_spec {bits value : Nat} (large : 8161 < value) :
    trialStatus (Spec.RsaKeyGen.trialPrimes bits) value =
      if Spec.RsaKeyGen.obviouslyComposite bits value then 0 else 1 := by
  have eq := trialAny_eq (w := (bits + 63) / 64) large
  have threshold : (17 ≤ (bits + 63) / 64) ↔ 1024 < bits := by omega
  have rounded : (1024 < 64 * ((bits + 63) / 64)) ↔ 1024 < bits := by omega
  unfold trialAny Spec.RsaKeyGen.obviouslyComposite Spec.RsaKeyGen.trialPrimes at eq
  simp only [threshold, rounded] at eq
  unfold trialStatus Spec.RsaKeyGen.obviouslyComposite Spec.RsaKeyGen.trialPrimes
  rw [← eq]
  split <;> rfl
end VG.Proof.Dsa.X86.Generation
