import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

theorem pairedHint_public {s t : State}
    (h : (pairedHintContract (abi.withConsts pairedConsts)).pub s t) :
    Taint.AgreeS ["VG_MLDSA_INV_PAIR"] (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4]) s t := by
  sig_pub [pairedHintContract,pairedHintSig,abi,argRegs,Abi.withConsts,pairedConsts_eq] at h
  obtain ⟨hsp,htable,h0,h1,h2,h3,h4,_hgamma⟩ := h
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hsp ?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> with_reducible assumption
  · intro name hn
    have he : name="VG_MLDSA_INV_PAIR" := by simpa only [List.mem_singleton] using hn
    subst name
    exact htable

theorem pairedHint_contract_ct : ConstantTime isa
    (pairedHintContract (abi.withConsts pairedConsts)).pre
    (pairedHintContract (abi.withConsts pairedConsts)).pub (selected .h) := by
  intro s t tr1 tr2 s' t' _ _ hp he hf
  exact h_ct s t tr1 tr2 s' t' trivial trivial (pairedHint_public hp) he hf

end VG.Proof.MlDsa.AArch64.Optimized.Paired
