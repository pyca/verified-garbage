module

public import VerifiedGarbage.Proof.Dsa.Arm.Verified
public import VerifiedGarbage.Proof.Dsa.Arm.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.Arm.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Verified
public import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Init
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Dsa.Arm.Leaves

/-! # DSA on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Dsa.Arm

def artifacts : List Artifact := [
  Spec.Dsa.randomSignPrevalidatedApi.artifact Arm.target {
    code := Impl.Dsa.Arm.RandomSign.code "vg_dsa_sign_prevalidated" Impl.Dsa.Arm.PrevalidatedSign.sign
    verified := Proof.Dsa.Arm.randomSigningPrevalidated_verified
    stack := 144 },
  Spec.Dsa.validatePrivateKeyApi.artifact Arm.target {
    code := Impl.Dsa.Arm.PrevalidatedSign.validate
    verified := Proof.Dsa.Arm.validating_private_verified },
  Spec.Dsa.deriveKeyApi.artifact Arm.target {
    code := Impl.Dsa.Arm.Generate.deriveKey
    verified := Proof.Dsa.Arm.derive_verified },
  Spec.Dsa.generateKeyApi.artifact Arm.target {
    code := Impl.Dsa.Arm.GenerateKey.code "vg_dsa_check_parameters" "vg_dsa_derive_key_checked"
      Impl.Dsa.Arm.Generate.checkParameters Impl.Dsa.Arm.Generate.deriveChecked
    verified := Proof.Dsa.Arm.Key.generating_verified
    stack := 144 },
  Spec.Dsa.validatePublicKeyApi.artifact Arm.target {
    code := Impl.Dsa.Arm.Prevalidated.validate
    verified := Proof.Dsa.Arm.validate_verified },
  Spec.Dsa.verifyPrevalidatedApi.artifact Arm.target {
    code := Impl.Dsa.Arm.Prevalidated.verify
    verified := Proof.Dsa.Arm.prevalidated_verified },
  Spec.Dsa.parameterInitApi.artifact Arm.target {
    code := Impl.Dsa.Arm.Generation.init
    verified := Proof.Dsa.Arm.Gen.Init.init_verified }]

end VG.Artifacts.Dsa.Arm
