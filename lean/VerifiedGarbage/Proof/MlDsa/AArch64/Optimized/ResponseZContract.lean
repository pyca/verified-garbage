import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith (polyRegion)

def addNormK : Contract isa where
  pre s := s.wr=[polyRegion (s.gpr .x0)] ∧ s.rd=[polyRegion (s.gpr .x1)] ∧
    (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x1)) ∧
    Reduced s.mem (s.gpr .x0) ∧ RawReduced s.mem (s.gpr .x1) ∧
    1≤((s.gpr .x2).setWidth 32).toNat ∧ ((s.gpr .x2).setWidth 32).toNat≤524288
  post s t := CenteredReduced t.mem (s.gpr .x0) ∧
    signedPolyAt t.mem (s.gpr .x0)=add (polyAt s.mem (s.gpr .x0)) (signedPolyAt s.mem (s.gpr .x1)) ∧
    (t.gpr .x0).setWidth 32=if normRq [add (polyAt s.mem (s.gpr .x0)) (signedPolyAt s.mem (s.gpr .x1))]<
      ((s.gpr .x2).setWidth 32).toNat then 1 else 0
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.sp=t.sp

theorem addNorm_correct (s : State) (hp : addNormK.pre s) :
    ∃trace t,Exec isa VG.Impl.MlDsa.AArch64.Optimized.Response.addNorm s trace t ∧
      abiPreserved s t ∧ addNormK.post s t := by
  obtain ⟨hw,hr,hd,ha,hb,hB,hB'⟩ := hp
  have hwrite : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    rw [hw]
    exact ⟨polyRegion (s.gpr .x0),List.mem_singleton_self _,Offset.contains_base _ ho (by omega)⟩
  have hread : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    obtain ⟨r,hr,hc⟩ := hwrite off ho
    exact ⟨r,List.mem_append_right _ hr,hc⟩
  have hinput : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
    intro off ho
    rw [hr]
    exact ⟨polyRegion (s.gpr .x1),by simp,Offset.contains_base _ ho (by omega)⟩
  obtain ⟨tr,t,he,hk,hcenter,hpoly,hret⟩ := addNorm_ok s hd ha hb hB hB' hread hinput hwrite
  refine ⟨tr,t,he,⟨?_,hk.sp,hk.vcs⟩,hcenter,hpoly,?_⟩
  · intro r hr
    apply hk.gpr r
    simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hret]
    split <;> rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response
