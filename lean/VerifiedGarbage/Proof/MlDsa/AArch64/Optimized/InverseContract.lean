import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStaticCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def inverseK : Contract isa where
  pre s := tableRegion (s.syms "VG_MLDSA_INV_FOLDED")∈s.rd++s.wr ∧
    outputRegion (s.gpr .x0)∈s.wr ∧
    (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s.gpr .x0)) ∧
    InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED") ∧ Reduced s.mem (s.gpr .x0)
  post s t := PolyIs t.mem (s.gpr .x0) (montgomeryNttInv (polyAt s.mem (s.gpr .x0)))
  pub s t := s.gpr .x0=t.gpr .x0 ∧ s.sp=t.sp ∧
    s.syms "VG_MLDSA_INV_FOLDED"=t.syms "VG_MLDSA_INV_FOLDED"

theorem inverse_pre {s : State}
    (h : (montgomeryNttInvContract (abi.withConsts inverseConsts)).pre s) : inverseK.pre s := by
  sig_pre [montgomeryNttInvContract,inPlaceContract,inPlaceSig,abi,argRegs,inverseConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow] at h
  obtain ⟨hd,held,_,hsep,ht,hw,_,_,_,hred⟩ := h
  have hrd : s.rd=[tableRegion (s.syms "VG_MLDSA_INV_FOLDED")] := by
    rw [← List.take_append_drop (s.rd.length-1) s.rd,ht,hd]
    rfl
  refine ⟨by rw [hrd]; simp,by rw [hw]; simp [outputRegion],?_,?_,hred⟩
  · exact hsep _ (by rw [hw]; simp [outputRegion])
  · intro i hi
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact (held i hi).trans (eq _ _ (by rw [InverseTable.expandedWords_length]; exact hi))

theorem inverse_ct : ConstantTime isa inverseK.pre inverseK.pub staticCode := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply staticCode_ct s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.1 ?_,?_⟩
  · intro r hr
    have he : r=.x0 := by simpa only [List.mem_singleton] using hr
    subst r; exact hp.1
  · intro name hn
    have he : name="VG_MLDSA_INV_FOLDED" := by simpa only [List.mem_singleton] using hn
    subst name; exact hp.2.2

theorem inverse_pub {s t : State}
    (h : (montgomeryNttInvContract (abi.withConsts inverseConsts)).pub s t) : inverseK.pub s t := by
  sig_pub [montgomeryNttInvContract,inPlaceContract,inPlaceSig,abi,argRegs,Abi.withConsts,inverseConsts_eq] at h
  exact ⟨h.2.2.1,h.1,h.2.1⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
