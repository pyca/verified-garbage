import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseLowCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith (polyRegion)
open VG.Proof.MlDsa.AArch64.Round

def subLowNormK : Contract isa where
  pre s := s.rd=[polyRegion (s.gpr .x1)] ∧ s.wr=[polyRegion (s.gpr .x0),polyRegion (s.gpr .x2)] ∧
    (polyRegion (s.gpr .x0)).Disjoint (polyRegion (s.gpr .x2)) ∧
    (polyRegion (s.gpr .x1)).Disjoint (polyRegion (s.gpr .x0)) ∧
    (polyRegion (s.gpr .x1)).Disjoint (polyRegion (s.gpr .x2)) ∧
    Reduced s.mem (s.gpr .x0) ∧ RawReduced s.mem (s.gpr .x1) ∧
    IsG (arg32 s .x3) ∧ 1≤arg32 s .x4 ∧ arg32 s .x4≤524288
  post s t :=
    (∀i<n,(coeffAt t.mem (s.gpr .x0) i).toNat=(highBits (arg32 s .x3)
      (responseDifference s.mem (s.gpr .x0) (s.gpr .x1) i)).toNat) ∧
    (∀i<n,(coeffAt t.mem (s.gpr .x2) i).toInt=lowBits (arg32 s .x3)
      (responseDifference s.mem (s.gpr .x0) (s.gpr .x1) i)) ∧
    (t.gpr .x0).setWidth 32=if responseLowPass s.mem (s.gpr .x0) (s.gpr .x1) (arg32 s .x3) (arg32 s .x4) then 1 else 0
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.gpr .x2=t.gpr .x2 ∧
    (s.gpr .x3).setWidth 32=(t.gpr .x3).setWidth 32 ∧ s.sp=t.sp

theorem subLowNorm_correct (s : State) (hp : subLowNormK.pre s) :
    ∃ trace t,Exec isa VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm s trace t ∧
      abiPreserved s t ∧ subLowNormK.post s t := by
  obtain ⟨hr,hw,hpl,hap,hal,hcan,hraw,hg,hB,hB'⟩ := hp
  have hwrite (r : Reg) (hm : polyRegion (s.gpr r)∈s.wr) :
      ∀off,off+16≤1024 → InRegions s.wr (s.gpr r+BitVec.ofNat 64 off) 16 := by
    intro off ho
    exact ⟨_,hm,Offset.contains_base _ ho (by omega)⟩
  have hw0 := hwrite .x0 (by rw [hw]; simp)
  have hw2 := hwrite .x2 (by rw [hw]; simp)
  have hr0 : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16 := by
    intro off ho
    obtain ⟨r,hm,hc⟩ := hw0 off ho
    exact ⟨r,List.mem_append_right _ hm,hc⟩
  have hr1 : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16 := by
    intro off ho
    exact ⟨polyRegion (s.gpr .x1),by rw [hr]; simp,Offset.contains_base _ ho (by omega)⟩
  obtain ⟨tr,t,he,hk,hh,hl,hn⟩ := subLowNorm_ok s hg hB hB' hcan hraw hpl hap hal hr0 hr1 hw0 hw2
  refine ⟨tr,t,he,⟨?_,hk.sp,hk.vcs⟩,hh,hl,?_⟩
  · intro r hp
    apply hk.gpr r
    simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · rw [hn]
    split <;> rfl

theorem subLowNorm_contract_ct : ConstantTime isa subLowNormK.pre subLowNormK.pub
    VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Response.subLowNorm
  apply zext_ct (τ:=Taint.ofRegs [.x0,.x1,.x2,.x3]) ?_ (by taint_decide)
  intro s t hp
  have h := agree_zext (gr:=.x3) (rs:=[.x0,.x1,.x2]) hp.2.2.2.2 hp.2.2.2.1 ?_
  · exact ⟨h.1,fun r hr=>h.2 r (by simpa [Taint.mem_ofRegs,List.mem_cons,or_comm,or_left_comm,or_assoc] using hr)⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2.1

end VG.Proof.MlDsa.AArch64.Optimized.Response
