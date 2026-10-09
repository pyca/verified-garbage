import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowAccess
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedWordTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedLow_public {s t : State}
    (h : (pairedLowContract (abi.withConsts pairedConsts)).pub s t) : WordPublic s t := by
  sig_pub [pairedLowContract,pairedLowSig,abi,argRegs,Abi.withConsts,pairedConsts_eq] at h
  obtain ⟨hsp,htable,h0,h1,h2,h3,h4,h5⟩ := h
  refine ⟨hsp,?_,h5,htable⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl <;> with_reducible assumption

theorem pairedLow_contract_ct : ConstantTime isa
    (pairedLowContract (abi.withConsts pairedConsts)).pre
    (pairedLowContract (abi.withConsts pairedConsts)).pub (selected .r0) := by
  intro s t tr1 tr2 s' t' hs ht hp he hf
  exact r0_word_ct s t tr1 tr2 s' t' (pairedLow_pre hs).access (pairedLow_pre ht).access
    (pairedLow_public hp) he hf

end VG.Proof.MlDsa.AArch64.Optimized.Paired
