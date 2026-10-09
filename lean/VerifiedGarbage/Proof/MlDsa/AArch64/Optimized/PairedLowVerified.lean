import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowContractTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowSat

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Exact selected batched low-part kernel, including all-path outputs,
strict norm return, restored ABI, and the shared public-input timing policy. -/
theorem pairedLow_verified : Verified target (selected .r0)
    (pairedLowContract (abi.withConsts pairedConsts)) :=
  ⟨pairedLow_correct,pairedLow_contract_ct,⟨lowSat,pairedLow_sat⟩⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
