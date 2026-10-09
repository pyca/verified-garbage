import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotStatic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemoryField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def dotK (count : Nat) : Contract isa where
  pre s := tableRegion (s.syms "VG_MLDSA_INV_FOLDED")∈s.rd++s.wr ∧
    dotFamilyRegion (s.gpr .x1) count∈s.rd++s.wr ∧ dotFamilyRegion (s.gpr .x2) count∈s.rd++s.wr ∧
    outputRegion (s.gpr .x0)∈s.wr ∧
    (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s.gpr .x0)) ∧
    (dotFamilyRegion (s.gpr .x1) count).Disjoint (outputRegion (s.gpr .x0)) ∧
    (dotFamilyRegion (s.gpr .x2) count).Disjoint (outputRegion (s.gpr .x0)) ∧
    InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED") ∧
    (∀j<count,PositiveReduced s.mem (s.gpr .x1+BitVec.ofNat 64 (1024*j))) ∧
    (∀j<count,PositiveReduced s.mem (s.gpr .x2+BitVec.ofNat 64 (1024*j)))
  post s t := PolyIs t.mem (s.gpr .x0) (nttInv (dotNTT
    (fun j => polyAt s.mem (s.gpr .x1+BitVec.ofNat 64 (1024*j)))
    (fun j => polyAt s.mem (s.gpr .x2+BitVec.ofNat 64 (1024*j))) count))
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧ s.gpr .x2=t.gpr .x2 ∧
    s.sp=t.sp ∧ s.syms "VG_MLDSA_INV_FOLDED"=t.syms "VG_MLDSA_INV_FOLDED"

theorem dot_pre {count : Nat} {s : State}
    (h : (dotInverseContract count (abi.withConsts inverseConsts)).pre s) : (dotK count).pre s := by
  sig_pre [dotInverseContract,dotInverseSig,abi,argRegs,inverseConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow] at h
  obtain ⟨hd,held,_,hsep,ht,hw,rest⟩ := h
  have hrd : s.rd=[dotFamilyRegion (s.gpr .x1) count,dotFamilyRegion (s.gpr .x2) count,
      tableRegion (s.syms "VG_MLDSA_INV_FOLDED")] := by
    rw [← List.take_append_drop (s.rd.length-1) s.rd,ht,hd]
    have he : count*256*4=1024*count := by omega
    rw [he]
    rfl
  refine ⟨by rw [hrd]; simp,by rw [hrd]; simp,by rw [hrd]; simp,
    by rw [hw]; simp [outputRegion],?_,?_,?_,?_,?_,?_⟩
  · exact hsep _ (by rw [hw]; simp [outputRegion])
  · have hh : (outputRegion (s.gpr .x0)).Disjoint (dotFamilyRegion (s.gpr .x1) count) := by
      dsimp only [outputRegion,dotFamilyRegion]; grind only
    exact hh.symm
  · have hh : (outputRegion (s.gpr .x0)).Disjoint (dotFamilyRegion (s.gpr .x2) count) := by
      dsimp only [outputRegion,dotFamilyRegion]; grind only
    exact hh.symm
  · intro i hi
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact (held i hi).trans (eq _ _ (by rw [InverseTable.expandedWords_length]; exact hi))
  · grind only
  · grind only

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
