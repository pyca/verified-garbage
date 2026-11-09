module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStaticCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryCorrect
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.InverseTable
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlKem.AArch64.Common

/-! ## From `InverseContract.lean` -/

@[expose] public section

section

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

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

theorem inverse_correct (s : State) (hp : inverseK.pre s) :
    ∃ trace t, Exec isa staticCode s trace t ∧ abiPreserved s t ∧ inverseK.post s t := by
  obtain ⟨htr,hw,hsep,ht,hred⟩ := hp
  obtain ⟨tr,t,he,hk,_,_,hm⟩ := staticCode_words_ok ht htr hw hsep
  have hv := inverseMem_field (m := s.mem) (p := s.gpr .x0) ⟨hred,rfl⟩
  rw [← hm] at hv
  exact ⟨tr,t,he,coreKeep_abi hk,hv⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
