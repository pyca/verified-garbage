import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintSpec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith (polyRegion)
open VG.Proof.MlDsa.AArch64.Round

def hintNormK : Contract isa where
  pre s := s.rd=[polyRegion (s.gpr .x1),polyRegion (s.gpr .x2)] ∧ s.wr=[polyRegion (s.gpr .x0)] ∧
    (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x1)) ∧
    (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x2)) ∧
    IsG (arg32 s .x3) ∧ RawReduced s.mem (s.gpr .x1) ∧
    ResponseDecomposed s.mem (s.gpr .x0) (s.gpr .x2) (arg32 s .x3)
  post s t := HintIs t.mem (s.gpr .x0) 1
      [responseHintPoly s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (arg32 s .x3)] ∧
    t.gpr .x0=BitVec.ofNat 64 (hintOnes [responseHintPoly s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (arg32 s .x3)]+
      if normRq [signedPolyAt s.mem (s.gpr .x1)]<arg32 s .x3 then 4294967296 else 0)
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.gpr .x2=t.gpr .x2 ∧ s.sp=t.sp

theorem hintNorm_correct (s : State) (hp : hintNormK.pre s) :
    ∃trace t,Exec isa Impl.MlDsa.AArch64.Optimized.Response.hintNorm s trace t ∧
      abiPreserved s t ∧ hintNormK.post s t := by
  obtain ⟨hr,hw,hd,he,hg,hraw,hparts⟩ := hp
  have hwrite : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    exact ⟨polyRegion (s.gpr .x0),by rw [hw]; simp,Offset.contains_base _ ho (by omega)⟩
  have hread0 : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    obtain ⟨r,hm,hc⟩ := hwrite off ho
    exact ⟨r,List.mem_append_right _ hm,hc⟩
  have hread (r : Reg) (hm : polyRegion (s.gpr r)∈s.rd) :
      ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr r+BitVec.ofNat 64 off) 16 := by
    intro off ho
    exact ⟨polyRegion (s.gpr r),List.mem_append_left _ hm,Offset.contains_base _ ho (by omega)⟩
  obtain ⟨tr,t,ex,hk,hout,hret⟩ := hintNorm_spec_ok s (arg32 s .x3) hg
    (by simp only [arg32,BitVec.ofNat_toNat,BitVec.setWidth_eq]) hraw hparts hd he hread0
    (hread .x1 (by rw [hr]; simp)) (hread .x2 (by rw [hr]; simp)) hwrite
  refine ⟨tr,t,ex,⟨?_,hk.sp,hk.vcs⟩,hout,hret⟩
  intro r hr
  apply hk.gpr r
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem hintNorm_contract_ct : ConstantTime isa hintNormK.pre hintNormK.pub
    Impl.MlDsa.AArch64.Optimized.Response.hintNorm := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply hintNorm_ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.2.2 ?_,by simp⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2.1

end VG.Proof.MlDsa.AArch64.Optimized.Response
