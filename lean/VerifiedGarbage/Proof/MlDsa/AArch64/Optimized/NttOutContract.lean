import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.StaticCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOutTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Spec.MlDsa.PositiveNtt
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.NttTable

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def positiveNttOutK : Contract isa where
  pre s := expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED") ∈ s.rd++s.wr ∧
    outputRegion (s.gpr .x0) ∈ s.wr ∧
    outputRegion (s.gpr .x1) ∈ s.rd++s.wr ∧
    (outputRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0)) ∧
    (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion (s.gpr .x0)) ∧
    ExpandedArtifact s.mem (s.syms "VG_MLDSA_NTT_EXPANDED") ∧ Reduced s.mem (s.gpr .x1)
  post s t := PositivePolyIs t.mem (s.gpr .x0) (ntt (polyAt s.mem (s.gpr .x1)))
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.sp=t.sp ∧
    s.syms "VG_MLDSA_NTT_EXPANDED"=t.syms "VG_MLDSA_NTT_EXPANDED"

theorem positiveNttOut_correct (s : State) (hp : positiveNttOutK.pre s) :
    ∃ trace t, Exec isa outNtt s trace t ∧ abiPreserved s t ∧ positiveNttOutK.post s t := by
  obtain ⟨htr,hw,hr,hio,hsep,ht,hred⟩ := hp
  obtain ⟨tr,t,he,hk,hf,hm⟩ := outNtt_words_ok ht htr hr hw hsep
  have hv := outMemory_field_disjoint (m := s.mem) (p := s.gpr .x0) ⟨hred,rfl⟩ hio
  rw [← hm] at hv
  refine ⟨tr,t,he,⟨?_,hk.sp,hk.vcs⟩,hv.bound,hv.value⟩
  intro r hr
  apply hk.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem positiveNttOut_ct : ConstantTime isa positiveNttOutK.pre positiveNttOutK.pub outNtt := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply outNtt_ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.2.1 ?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.1
    · exact hp.2.1
  · intro name hn
    have he : name="VG_MLDSA_NTT_EXPANDED" := by simpa only [List.mem_singleton] using hn
    subst name; exact hp.2.2.2

end VG.Proof.MlDsa.AArch64.Optimized
