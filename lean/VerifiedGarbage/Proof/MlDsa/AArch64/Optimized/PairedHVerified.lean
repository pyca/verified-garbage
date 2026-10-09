import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintContractTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintSat

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

/-- Exact paired hint generation, all-path hint outputs/counts and strict
product norm, with the original ABI and public-input timing policy. -/
theorem pairedHint_verified : Verified target (selected .h)
    (pairedHintContract (abi.withConsts pairedConsts)) :=
  ⟨pairedHint_correct,pairedHint_contract_ct,⟨hintSat,pairedHint_sat⟩⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
