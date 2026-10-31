module

public import VerifiedGarbage.Proof.Dsa.Arm.Verified
public import VerifiedGarbage.Proof.Dsa.Arm.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Dsa.Arm.Leaves

/-! DSA signing with a supplied or a sampled nonce, verification, domain checks, key derivation
and key generation, on ARMv7. -/

@[expose] public section

namespace VG.Artifacts.Dsa.Arm

def artifacts : List Artifact := [
  Spec.Dsa.randomSignApi.artifact Arm.target {
    code := Impl.Dsa.Arm.RandomSign.code Spec.Dsa.signApi.name (Impl.Dsa.Arm.Entry.operation true)
    verified := Proof.Dsa.Arm.randomSigning_verified
    stack := 144 },
  Spec.Dsa.signApi.artifact Arm.target {
    code := Impl.Dsa.Arm.Entry.operation true
    verified := Proof.Dsa.Arm.sign_verified },
  Spec.Dsa.verifyApi.artifact Arm.target {
    code := Impl.Dsa.Arm.Entry.operation false
    verified := Proof.Dsa.Arm.verify_verified },
  Spec.Dsa.checkParametersApi.artifact Arm.target {
    code := Impl.Dsa.Arm.Generate.checkParameters
    verified := Proof.Dsa.Arm.check_verified },
  Spec.Dsa.deriveKeyApi.artifact Arm.target {
    code := Impl.Dsa.Arm.Generate.deriveKey
    verified := Proof.Dsa.Arm.derive_verified },
  Spec.Dsa.generateKeyApi.artifact Arm.target {
    code := Impl.Dsa.Arm.GenerateKey.code Spec.Dsa.checkParametersApi.name Spec.Dsa.deriveKeyApi.name
      Impl.Dsa.Arm.Generate.checkParameters Impl.Dsa.Arm.Generate.deriveKey
    verified := Proof.Dsa.Arm.Key.generating_verified
    stack := 144 }]

end VG.Artifacts.Dsa.Arm
