import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.StaticCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Spec.MlDsa.PositiveNtt
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.NttTable

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def positiveNttK : Contract isa where
  pre s := expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED") ∈ s.rd++s.wr ∧
    outputRegion (s.gpr .x0) ∈ s.wr ∧
    (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion (s.gpr .x0)) ∧
    ExpandedArtifact s.mem (s.syms "VG_MLDSA_NTT_EXPANDED") ∧ Reduced s.mem (s.gpr .x0)
  post s t := PositivePolyIs t.mem (s.gpr .x0) (ntt (polyAt s.mem (s.gpr .x0)))
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.sp=t.sp ∧
    s.syms "VG_MLDSA_NTT_EXPANDED"=t.syms "VG_MLDSA_NTT_EXPANDED"

theorem positiveNtt_correct (s : State) (hp : positiveNttK.pre s) :
    ∃ trace t, Exec isa staticNtt s trace t ∧ abiPreserved s t ∧ positiveNttK.post s t := by
  obtain ⟨htr,hw,hsep,ht,hred⟩ := hp
  obtain ⟨tr,t,he,hk,hf,hm⟩ := staticNtt_words_ok ht htr hw hsep
  have hv := nttMemory_field (m := s.mem) (p := s.gpr .x0) ⟨hred,rfl⟩
  rw [← hm] at hv
  refine ⟨tr,t,he,⟨?_,hk.sp,hk.vcs⟩,hv.bound,hv.value⟩
  intro r hr
  apply hk.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem positiveNtt_ct : ConstantTime isa positiveNttK.pre positiveNttK.pub staticNtt := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply staticNtt_ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.1 ?_,?_⟩
  · intro r hr
    have he : r=.x0 := by simpa only [List.mem_singleton] using hr
    subst r; exact hp.1
  · intro name hn
    have he : name="VG_MLDSA_NTT_EXPANDED" := by simpa only [List.mem_singleton] using hn
    subst name; exact hp.2.2

end VG.Proof.MlDsa.AArch64.Optimized
