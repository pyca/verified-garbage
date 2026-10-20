module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateData
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGeneratePost
import VerifiedGarbage.Proof.Ffdh.Arm.CachedSamplePolicy
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedKeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentTailLaw

/-! The complete cached attempt implements its reviewed immutable-context contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem cachedKeyGenerate_correct (prepare sample tail : Prog isa)
    (prep : EnvironmentPrepareLaw cachedGenerationEnvironment prepare)
    (sampler : EnvironmentSampleLaw cachedGenerationEnvironment ScalarLayout.vetted sample)
    (law : EnvironmentTailLaw cachedGenerationEnvironment ScalarLayout.vetted tail)
    (s : State) (pre : (Spec.Ffdh.cachedGenerateKeyContract abi 176).pre s) :
    ∃tr t,Exec isa (VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample tail) s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.cachedGenerateKeyContract abi 176).post s t := by
  obtain ⟨p,rb,_,privateValue,publicValue,domain,count,_,entropy,domainBytes,entropyBytes,input,cached,valid,_cache,_words⟩ :=
    cachedKeyGenerate_data s pre
  have modValid := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modValid
  obtain ⟨tr,t,run,preserved,result⟩ := cachedKeyGenerateFn_ok prepare sample tail cachedGenerationEnvironment
    ScalarLayout.vetted prep sampler law CachedSample.layoutBound s input cached modValid
  refine ⟨tr,t,run,preserved,?_⟩
  have randLength : (stackArg s 4).toNat=(stackArg s 2).toNat := by
    sig_pre [Spec.Ffdh.cachedGenerateKeyContract,Spec.Ffdh.cachedGenerateKeySig,Spec.Ffdh.generateKeySig,
      abi,argRegs,reduceClassify,Loc.val,State.addr] at pre
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rLen,_,_,_⟩ := pre
    exact rLen
  exact cachedKeyGenerate_post s t privateValue publicValue domain count entropy domainBytes entropyBytes
    randLength input.input.size valid result

end VG.Proof.Ffdh.Arm
