import VerifiedGarbage.Spec.MlDsa.MontProduct
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Arith (pR)

structure Pre (s : State) : Prop where
  a : pR (s.gpr .x1) ∈ s.rd++s.wr
  b : pR (s.gpr .x2) ∈ s.rd++s.wr
  out : pR (s.gpr .x0) ∈ s.wr
  oa : (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1))
  ob : (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x2))
  pa : PositiveReduced s.mem (s.gpr .x1)
  pb : PositiveReduced s.mem (s.gpr .x2)

def contract : Contract isa where
  pre := Pre
  post s t := PolyIs t.mem (s.gpr .x0)
    (montgomeryMultiplyNTT (polyAt s.mem (s.gpr .x1)) (polyAt s.mem (s.gpr .x2)))
  pub s t := (∀r∈[Reg.x0,.x1,.x2],s.gpr r=t.gpr r) ∧ s.sp=t.sp

theorem pre {s : State} (h : (montProductContract abi).pre s) : Pre s := by
  sig_pre [montProductContract,montProductSig,abi,argRegs,stackBelow] at h
  obtain ⟨hr,hw,ha,hb,_,_,_,hpa,hpb⟩ := h
  exact ⟨by rw [hr]; simp [pR],by rw [hr]; simp [pR],by rw [hw]; simp [pR],ha,hb,hpa,hpb⟩
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct
