module

import VerifiedGarbage.Proof.Ffdh.Arm.VettedKeyGenerateCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.SampleKeyGenerateContractCT
import VerifiedGarbage.Proof.Ffdh.Arm.VettedKeyGenerateSat
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleTailLaw
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGenerationContract

/-! Vetted attempts combine the reviewed functional and timing policies. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts tableSym)

theorem vettedKeyGenerate_verified (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env ScalarLayout.vetted sample)
    (law : SampleTailLaw tail)
    (makeEnvironment : ∀ (s : State),
      (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s →
      ∀ {p : Inputs} {rb : List Byte}, KeyGenerateFnInput p rb s → env.holds p (entered s))
    (publicEnvironment : ∀ (s t : State), s.syms tableSym = t.syms tableSym → env.publicRel s t) :
    Verified target (VG.Impl.Ffdh.Arm.SampleKeyGenerate.code prepare sample tail)
      (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176) :=
  ⟨vettedKeyGenerate_correct prepare sample tail env prep sampler law makeEnvironment,
    vettedKeyGenerate_contract_ct prepare sample tail env prep sampler law makeEnvironment publicEnvironment,
    vettedKeyGenerate_sat⟩

end VG.Proof.Ffdh.Arm
