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
public import VerifiedGarbage.Proof.Variants.MillerRabin.Arm

/-! # DSA (FIPS 186-4) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Dsa.Arm

open VG Proof.Dsa.Arm.Gen

def artifacts : List Artifact := [
  Spec.Dsa.randomSignPrevalidatedApi.artifact Arm.target Proof.Dsa.Arm.Scrub.randomSignPrevalidatedReg,
  Spec.Dsa.validatePrivateKeyApi.artifact Arm.target Proof.Dsa.Arm.Scrub.validatePrivateKeyReg,
  Spec.Dsa.deriveKeyApi.artifact Arm.target Proof.Dsa.Arm.Scrub.deriveKeyReg,
  Spec.Dsa.generateKeyApi.artifact Arm.target Proof.Dsa.Arm.Scrub.generateKeyReg,
  Spec.Dsa.validatePublicKeyApi.artifact Arm.target Proof.Dsa.Arm.Scrub.validatePublicKeyReg,
  Spec.Dsa.verifyPrevalidatedApi.artifact Arm.target Proof.Dsa.Arm.Scrub.verifyPrevalidatedReg,
  Spec.Dsa.parameterInitApi.artifact Arm.target Proof.Dsa.Arm.Scrub.parameterInitReg] ++
  (VG.Proof.Variants.MillerRabin.Arm.variants.flatMap fun (v : Proof.MillerRabin.Arm.RoundImpl) => [
    Spec.Dsa.parameterSearchApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Dsa.Arm.Generation.code (geo1 v) (geo2 v) (geo3 v)
      verified := search_params v }])

end VG.Artifacts.Dsa.Arm
