import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotField
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Arith (pR)

def contract (n : Nat) : Contract isa where
  pre := Pre n
  post s t := PolyIs t.mem (s.gpr .x0) (value s n)
  pub s t := (∀r∈[Reg.x0,.x1,.x2],s.gpr r=t.gpr r) ∧ s.sp=t.sp

theorem pre {n : Nat} (hn : n≤7) {s : State} (h : (montDotContract abi n).pre s) : Pre n s := by
  sig_pre [montDotContract,montDotSig,abi,argRegs,stackBelow] at h
  have he : 256*n*4=1024*n := by omega
  rw [he] at h
  obtain ⟨hr,hw,ha,hb,_,_,_,hpa,hpb⟩ := h
  refine ⟨by rw [hw];simp [pR],?_,?_,?_⟩
  · intro r hr' j hj
    apply VG.CallLay.inRegions_sub (n:=1024*n) (off:=1024*j) (l:=1024)
    · refine ⟨⟨s.gpr r,1024*n⟩,?_,by simp [Region.Contains]⟩
      rw [hr]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
      rcases hr' with rfl|rfl <;> simp
    · omega
    · omega
  · intro r hr' j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
    rcases hr' with rfl|rfl
    · exact ha.symm.sub_left (Offset.sub_base _ (by omega))
    · exact hb.symm.sub_left (Offset.sub_base _ (by omega))
  · intro r hr' j hj i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
    rcases hr' with rfl|rfl
    · exact hpa j hj i hi
    · exact hpb j hj i hi

theorem correct {n : Nat} (hc : n=4∨n=5∨n=7) (s : State) (hp : (contract n).pre s) :
    ∃tr t,Exec isa (VG.Impl.MlDsa.AArch64.Optimized.MontDot.dot n) s tr t ∧
      abiPreserved s t ∧ (contract n).post s t := by
  obtain ⟨tr,t,he,hi⟩ := run_ok (by omega) (by omega) s hp
  refine ⟨tr,t,he,?_,output_ok (by omega) hp hi⟩
  rcases hc with rfl|rfl|rfl
  all_goals exact VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he (by decide +kernel)

end VG.Proof.MlDsa.AArch64.Optimized.MontDot
