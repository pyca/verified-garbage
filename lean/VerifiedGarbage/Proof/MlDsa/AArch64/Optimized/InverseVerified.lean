import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseContract
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryCorrect
import VerifiedGarbage.Proof.Framework.Contract

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

/-- Selected folded inverse satisfies the existing canonical contract. -/
theorem inverse_verified : Verified target staticCode
    (montgomeryNttInvContract (abi.withConsts inverseConsts)) := by
  refine Verified.of_correct inverse_correct inverse_ct
    { pre := fun _ h => inverse_pre h,post := ?_,pub := ?_,sat := ⟨inverseSat,inverse_sat⟩ }
  · intro s t _ h
    sig_post [montgomeryNttInvContract,inPlaceContract,inPlaceSig,abi,argRegs,Abi.withConsts,inverseConsts_eq]
    exact h
  · intro s t _ _ h
    exact inverse_pub h

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
