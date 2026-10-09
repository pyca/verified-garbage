import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductSat
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemoryCorrect
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

theorem productRaw_correct (s : State) (hp : productRawK.pre s) :
    ∃ trace t, Exec isa (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true) s trace t ∧
      abiPreserved s t ∧ productRawK.post s t := by
  obtain ⟨htr,har,hbr,hw,hsep,ha,hb,ht,hpa,hpb⟩ := hp
  obtain ⟨tr,t,he,hk,_,_,hm⟩ := productStatic_words_ok true ht htr har hbr hw hsep ha hb
  have hv := productRawInverse_contract_field (p := s.gpr .x0) hpa hpb
  change RawPolyIs (multiplyInverseMem true s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)) _ _ at hv
  rw [← hm] at hv
  exact ⟨tr,t,he,productCoreKeep_abi hk,hv⟩

/-- Exact measured raw helper, with explicit signed bounds and secret coefficients. -/
theorem productRaw_verified : Verified target
    (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true)
    (multiplyInverseRawContract (abi.withConsts inverseConsts)) := by
  refine Verified.of_correct productRaw_correct productRaw_ct
    { pre := fun _ h => productRaw_pre h,post := ?_,pub := ?_,sat := ⟨productSat,productRaw_sat⟩ }
  · intro s t _ h
    sig_post [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq]
    exact h
  · intro s t _ _ h
    exact productRaw_pub h

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
