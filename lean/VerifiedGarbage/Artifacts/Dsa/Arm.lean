module

public import VerifiedGarbage.Proof.Dsa.Arm.Verified
public import VerifiedGarbage.Proof.Dsa.Arm.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.Arm.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Verified
public import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Init
public import VerifiedGarbage.Proof.Dsa.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Instances

/-! # DSA (FIPS 186-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Dsa.Arm

open VG Proof.Dsa.Arm.Gen

def artifacts : List Artifact :=
  [Spec.Dsa.parameterInitApi.artifact Arm.target Proof.Dsa.Arm.Scrub.parameterInitReg] ++
  (VG.Proof.Variants.DsaArithmetic.Arm.variants.flatMap fun (v : Proof.Variants.DsaArithmetic.Arm.Variant) => [
    Spec.Dsa.randomSignPrevalidatedApi.artifact Arm.target
      (Proof.Dsa.Arm.Scrub.randomSignPrevalidatedReg v.umaal v.suffix),
    Spec.Dsa.validatePrivateKeyApi.artifact Arm.target
      (Proof.Dsa.Arm.Scrub.validatePrivateKeyReg v.umaal v.suffix),
    Spec.Dsa.deriveKeyApi.artifact Arm.target (Proof.Dsa.Arm.Scrub.deriveKeyReg v.umaal v.suffix),
    Spec.Dsa.generateKeyApi.artifact Arm.target (Proof.Dsa.Arm.Scrub.generateKeyReg v.umaal v.suffix),
    Spec.Dsa.validatePublicKeyApi.artifact Arm.target
      (Proof.Dsa.Arm.Scrub.validatePublicKeyReg v.umaal v.suffix),
    Spec.Dsa.verifyPrevalidatedApi.artifact Arm.target
      (Proof.Dsa.Arm.Scrub.verifyPrevalidatedReg v.umaal v.suffix)]) ++
  (searchPairs.flatMap fun (p : Proof.Variants.DsaArithmetic.Arm.Variant × Proof.MillerRabin.Arm.RoundImpl) => [
    Spec.Dsa.parameterSearchApi.artifact Arm.target {
      suffix := p.1.suffix
      code := Impl.Dsa.Arm.Generation.code (geo1 p.1.umaal p.2) (geo2 p.1.umaal p.2) (geo3 p.1.umaal p.2)
      verified := .unscrubbed (search_params p.2) }])

end VG.Artifacts.Dsa.Arm
