module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateFn
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateContractCT
import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyGenerateSat
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedKeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPrepareLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentTailLaw

/-! Functional correctness, timing and a real canonical-context witness certify cached attempts. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem cachedKeyGenerate_verified (prepare sample tail : Prog isa)
    (prep : EnvironmentPrepareLaw cachedGenerationEnvironment prepare)
    (sampler : EnvironmentSampleLaw cachedGenerationEnvironment ScalarLayout.vetted sample)
    (law : EnvironmentTailLaw cachedGenerationEnvironment ScalarLayout.vetted tail) :
    Verified target (VG.Impl.Ffdh.Arm.CachedKeyGenerate.code prepare sample tail)
      (Spec.Ffdh.cachedGenerateKeyContract abi 176) :=
  ⟨cachedKeyGenerate_correct prepare sample tail prep sampler law,
    cachedKeyGenerate_contract_ct prepare sample tail prep sampler law,cachedKeyGenerate_sat⟩

end VG.Proof.Ffdh.Arm
