import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZFunctional
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedAbi
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedZ_post {s t : State} (h : ZResult s t) :
    (pairedZContract (abi.withConsts pairedConsts)).post s t := by
  sig_post [pairedZContract,pairedZSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
  refine ⟨h.fields,?_⟩
  rw [h.ret]
  split <;> rfl

theorem pairedZ_correct (s : State)
    (h : (pairedZContract (abi.withConsts pairedConsts)).pre s) :
    ∃tr t,Exec isa (selected .z) s tr t ∧ abiPreserved s t ∧
      (pairedZContract (abi.withConsts pairedConsts)).post s t := by
  obtain ⟨tr,t,he,hr⟩ := pairedZ_functional (pairedZ_pre h)
  exact ⟨tr,t,he,entryKeep_abi hr.keep,pairedZ_post hr⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
