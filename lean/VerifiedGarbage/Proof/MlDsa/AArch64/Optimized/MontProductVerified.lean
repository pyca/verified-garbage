import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontProductCorrect

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.MontProduct (code)
open VG.Proof.MlDsa.AArch64.Arith (mulSat)

theorem pub {s t : State} (h : (montProductContract abi).pub s t) : contract.pub s t := by
  sig_pub [montProductContract,montProductSig,abi,argRegs] at h
  refine ⟨?_,h.1⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem ct : ConstantTime isa contract.pre contract.pub code :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ h => VG.Proof.MlKem.AArch64.agree_of h.2 h.1) (by taint_decide)

theorem verified : Verified target code (montProductContract abi) := by
  refine Verified.of_correct correct ct
    { pre := fun _ h => pre h, post := ?_,pub := fun _ _ _ _ h => pub h,sat := ?_ }
  · intro s t _ h
    sig_post [montProductContract,montProductSig,abi,argRegs]
    exact h
  · refine ⟨mulSat,?_⟩
    sig_pre [montProductContract,montProductSig,abi,argRegs,stackBelow,mulSat]
    refine ⟨Region.disjoint_of_sep (by decide),Region.disjoint_of_sep (by decide),
      by decide,by decide,by decide,?_,?_⟩
    all_goals intro i hi; simp [coeffAt,Mem.readW,Mem.read,VG.Spec.MlDsa.q]
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct
