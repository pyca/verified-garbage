import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejSelected
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Depth

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem legacy_pre {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.r4K.pre s) : Pre 4 s := by
  obtain ⟨hr,hw,hsa,hss,has⟩ := h
  exact ⟨Or.inr rfl,hr,hw,hsa,hss,has⟩

theorem selected_verified (sha3 : Bool) : Verified target (selected sha3) (Spec.MlDsa.rejNTT4Contract abi) := by
  cases sha3
  · exact VG.Proof.MlDsa.AArch64.Sample.Rej4.verified false
  · exact four_verified

theorem selected_correct (sha3 : Bool) (s : State)
    (h : VG.Proof.MlDsa.AArch64.Sample.Rej4.r4K.pre s) :
    WP isa (selected sha3) s fun t => abiPreserved s t ∧ VG.Proof.MlDsa.AArch64.Sample.Rej4.r4K.post s t := by
  cases sha3
  · exact VG.Proof.MlDsa.AArch64.Sample.Rej4.correct false s h
  · exact WP.mono (four_ok (legacy_pre h)) fun _ ht => ⟨ht.abi,result_legacy ht⟩

theorem selected_ct (sha3 : Bool) : ConstantTime isa VG.Proof.MlDsa.AArch64.Sample.Rej4.r4K.pre
    VG.Proof.MlDsa.AArch64.Sample.Rej4.r4K.pub (selected sha3) := by
  cases sha3
  · exact VG.Proof.MlDsa.AArch64.Sample.Rej4.ct false
  · intro s t tr ur s' t' hs ht pub es et
    exact four_ct _ _ _ _ _ _ (legacy_pre hs) (legacy_pre ht) pub es et

theorem selected_depth (sha3 : Bool) : (selected sha3).aarch64Depth=0 := by
  cases sha3
  · exact VG.Proof.MlDsa.AArch64.Sample.Rej4.depth false
  · decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
