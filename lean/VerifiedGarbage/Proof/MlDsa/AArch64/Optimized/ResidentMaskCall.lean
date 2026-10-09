import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64 VG.Spec.MlDsa

/-- The inline paired sampler uses no stack frame; it may be called from any
of the existing ML-DSA caller stack budgets. -/
theorem pair_callee {S : Nat} (hS : S<2^64) :
    CalleeOk S Impl.MlDsa.AArch64.Optimized.ResidentMask.raw
      (expandMaskPairContract AArch64.abi S) :=
  CalleeOk.of_verified hS pair_verified (by omega) (by
    have h : Impl.MlDsa.AArch64.Optimized.ResidentMask.raw.aarch64Depth=0 := by decide
    rw [h]; omega)

theorem pair_n2_callee {S : Nat} (hS : S<2^64) :
    CalleeOk S (Impl.MlDsa.AArch64.Optimized.ResidentMask.rawWith Resident.n2Core.code)
      (expandMaskPairContract AArch64.abi S) :=
  CalleeOk.of_verified hS pair_n2_verified (by omega) (by
    have h : (Impl.MlDsa.AArch64.Optimized.ResidentMask.rawWith Resident.n2Core.code).aarch64Depth=0 := by decide
    rw [h]; omega)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
