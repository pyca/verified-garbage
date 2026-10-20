module

import VerifiedGarbage.Proof.Ffdh.Arm.SampleKeyGenerateFn
import VerifiedGarbage.Proof.Ffdh.Arm.VettedKeyGenerateInput
import VerifiedGarbage.Proof.Ffdh.Arm.VettedKeyGeneratePost
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleKeyGenerate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleTailLaw
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGenerateFn
public import VerifiedGarbage.Spec.Ffdh.VettedKeyGenerationContract

/-! The callable attempt implements the reviewed vetted scalar distribution. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Impl.Ffdh.Arm.VettedGroups (tableConsts)

theorem vettedKeyGenerate_correct (prepare sample tail : Prog isa) (env : SampleEnvironment)
    (prep : KeyPrepareLaw prepare) (sampler : SampleLaw env ScalarLayout.vetted sample)
    (law : SampleTailLaw tail)
    (makeEnvironment : ∀ (s : State),
      (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s →
      ∀ {p : Inputs} {rb : List Byte}, KeyGenerateFnInput p rb s → env.holds p (entered s))
    (s : State) (pre : (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.SampleKeyGenerate.code prepare sample tail) s tr t ∧
      abiPreserved s t ∧
      (Spec.Ffdh.vettedGenerateKeyContract (abi.withConsts tableConsts) 176).post s t := by
  obtain ⟨p, rb, _, privateValue, publicValue, domain, count, _, entropy, domainBytes, entropyBytes, input⟩ :=
    vettedKeyGenerate_data_base s pre
  obtain ⟨tr, t, run, preserved, result⟩ := sampleKeyGenerateFn_ok prepare sample tail env
    ScalarLayout.vetted prep sampler law s input (makeEnvironment s pre input)
  refine ⟨tr, t, run, preserved, post_consts.mpr ?_⟩
  have randLength : (stackArg s 4).toNat = (stackArg s 2).toNat := by
    have old := (vettedKeyGenerate_pre pre).1
    sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi,
      argRegs, reduceClassify, Loc.val, State.addr] at old
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _⟩ := old
    exact length
  exact vettedKeyGenerate_post (stripConsts tableConsts s) t privateValue publicValue
    domain count entropy domainBytes entropyBytes randLength input.size result

end VG.Proof.Ffdh.Arm
