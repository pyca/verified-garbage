import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith (polyRegion)

def canonicalizeK : Contract isa where
  pre s := s.wr=[polyRegion (s.gpr .x0)] ∧ CenteredReduced s.mem (s.gpr .x0)
  post s t := PolyIs t.mem (s.gpr .x0) (signedPolyAt s.mem (s.gpr .x0))
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.sp=t.sp

theorem canonicalize_correct (s : State) (hp : canonicalizeK.pre s) :
    ∃ trace t, Exec isa VG.Impl.MlDsa.AArch64.Optimized.Response.canonicalize s trace t ∧
      abiPreserved s t ∧ canonicalizeK.post s t := by
  obtain ⟨hw,hb⟩ := hp
  have hwrite : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    rw [hw]
    exact ⟨polyRegion (s.gpr .x0),List.mem_singleton_self _,Offset.contains_base _ ho (by omega)⟩
  have hread : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    obtain ⟨r,hr,hc⟩ := hwrite off ho
    exact ⟨r,List.mem_append_right _ hr,hc⟩
  obtain ⟨tr,t,he,hk,hpost⟩ := canonicalize_ok s hb hread hwrite
  refine ⟨tr,t,he,⟨?_,hk.sp,hk.vcs⟩,hpost⟩
  intro r hr
  apply hk.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.Response
