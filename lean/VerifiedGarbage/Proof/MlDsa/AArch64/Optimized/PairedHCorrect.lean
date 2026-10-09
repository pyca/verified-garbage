import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHFunctional
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedAbi
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedHint_post {s t : State} (h : HResult s t) :
    (pairedHintContract (abi.withConsts pairedConsts)).post s t := by
  sig_post [pairedHintContract,pairedHintSig,abi,argRegs,Abi.withConsts,pairedConsts_eq]
  exact ⟨h.fields,h.ret⟩

theorem pairedHint_correct (s : State)
    (h : (pairedHintContract (abi.withConsts pairedConsts)).pre s) :
    ∃tr t,Exec isa (selected .h) s tr t ∧ abiPreserved s t ∧
      (pairedHintContract (abi.withConsts pairedConsts)).post s t := by
  obtain ⟨tr,t,he,hr⟩ := pairedHint_functional (pairedHint_pre h)
  exact ⟨tr,t,he,entryKeep_abi hr.keep,pairedHint_post hr⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
