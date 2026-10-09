import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowFunctional
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedAbi
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLow_post {s t : State} (h : LowResult s t) :
    (pairedLowContract (abi.withConsts pairedConsts)).post s t := by
  sig_post [pairedLowContract,pairedLowSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
  refine ⟨h.fields,?_⟩
  rw [h.ret]
  split <;> rfl

theorem pairedLow_correct (s : State)
    (h : (pairedLowContract (abi.withConsts pairedConsts)).pre s) :
    ∃tr t,Exec isa (selected .r0) s tr t ∧ abiPreserved s t ∧
      (pairedLowContract (abi.withConsts pairedConsts)).post s t := by
  obtain ⟨tr,t,he,hr⟩ := pairedLow_functional (pairedLow_pre h)
  exact ⟨tr,t,he,entryKeep_abi hr.keep,pairedLow_post hr⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
