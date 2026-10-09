import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductStatic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductFullTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
import VerifiedGarbage.Spec.MlDsa.RawInverse

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

def productRawK : Contract isa where
  pre s := tableRegion (s.syms "VG_MLDSA_INV_FOLDED")∈s.rd++s.wr ∧
    polyRegion (s.gpr .x1)∈s.rd++s.wr ∧ polyRegion (s.gpr .x2)∈s.rd++s.wr ∧
    outputRegion (s.gpr .x0)∈s.wr ∧
    (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s.gpr .x0)) ∧
    (polyRegion (s.gpr .x1)).Disjoint (outputRegion (s.gpr .x0)) ∧
    (polyRegion (s.gpr .x2)).Disjoint (outputRegion (s.gpr .x0)) ∧
    InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED") ∧
    PositiveReduced s.mem (s.gpr .x1) ∧ PositiveReduced s.mem (s.gpr .x2)
  post s t := RawPolyIs t.mem (s.gpr .x0)
    (nttInv (multiplyNTT (polyAt s.mem (s.gpr .x1)) (polyAt s.mem (s.gpr .x2))))
  pub s t := (∀ r∈[Reg.x0,.x1,.x2], s.gpr r=t.gpr r) ∧ s.sp=t.sp ∧
    s.syms "VG_MLDSA_INV_FOLDED"=t.syms "VG_MLDSA_INV_FOLDED"

theorem productRaw_pre {s : State}
    (h : (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre s) : productRawK.pre s := by
  sig_pre [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,
    inverseConsts_eq,Abi.withConsts,Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow] at h
  obtain ⟨hd,held,_,hsep,ht,hw,hoa,hob,_,_,_,_,_,_,_,hpa,hpb⟩ := h
  have hrd : s.rd=[polyRegion (s.gpr .x1),polyRegion (s.gpr .x2),tableRegion (s.syms "VG_MLDSA_INV_FOLDED")] := by
    rw [← List.take_append_drop (s.rd.length-1) s.rd,ht,hd]
    rfl
  refine ⟨by rw [hrd]; simp,by rw [hrd]; simp,by rw [hrd]; simp,
    by rw [hw]; simp [outputRegion],?_,hoa.symm,hob.symm,?_,hpa,hpb⟩
  · exact hsep _ (by rw [hw]; simp [outputRegion])
  · intro i hi
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact (held i hi).trans (eq _ _ (by rw [InverseTable.expandedWords_length]; exact hi))

theorem productRaw_ct : ConstantTime isa productRawK.pre productRawK.pub
    (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true) := by
  intro s t tr₁ tr₂ s' t' _ _ hp he₁ he₂
  apply productStatic_ct true s t tr₁ tr₂ s' t' trivial trivial ?_ he₁ he₂
  refine ⟨VG.Proof.MlKem.AArch64.agree_of hp.2.1 hp.1,?_⟩
  intro name hn
  have he : name="VG_MLDSA_INV_FOLDED" := by simpa only [List.mem_singleton] using hn
  subst name; exact hp.2.2

theorem productRaw_pub {s t : State}
    (h : (multiplyInverseRawContract (abi.withConsts inverseConsts)).pub s t) : productRawK.pub s t := by
  sig_pub [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq] at h
  refine ⟨?_,h.1,h.2.1⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
