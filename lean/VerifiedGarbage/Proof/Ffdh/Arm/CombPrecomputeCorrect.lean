module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeFn
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeData
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedBoundInstance
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputePost
import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import Init.Core
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract

/-! Native public precomputation satisfies the reviewed immutable-context contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

theorem combPrecompute_correct (backend : MontBackend) (s : State)
    (pre : (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.CombPrecompute.code
      (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul) VettedBound.code) s tr t ∧
      abiPreserved s t ∧
      (Spec.Ffdh.generationPrecomputeContract (abi.withConsts tableConsts) 176).post s t := by
  obtain ⟨p,_base,output,domain,count,_capacity,domainBytes,ctxLen,_private,_public,_entropy,input⟩ :=
    combPrecompute_data s pre
  obtain ⟨tr,t,run,preserved,status,result⟩ := combPrecomputeFn_ok backend s input
  exact ⟨tr,t,run,preserved,post_consts.mpr
    (combPrecompute_post s t output domain count domainBytes ctxLen status result)⟩

end VG.Proof.Ffdh.Arm
