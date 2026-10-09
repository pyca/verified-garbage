import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZContractTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZSat

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Exact selected batched response-sum kernel, including all-path outputs,
strict norm return, restored ABI, and the shared public-input timing policy. -/
theorem pairedZ_verified : Verified target (selected .z)
    (pairedZContract (abi.withConsts pairedConsts)) :=
  ⟨pairedZ_correct,pairedZ_contract_ct,⟨zSat,pairedZ_sat⟩⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
