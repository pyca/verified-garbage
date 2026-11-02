module

public import VerifiedGarbage.Proof.Dsa.Arm.Verified
public import VerifiedGarbage.Proof.Dsa.Arm.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Dsa.Arm.Leaves

/-! # DSA on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Dsa.Arm

def artifacts : List Artifact := [
  Spec.Dsa.randomSignApi.artifact Arm.target {
    code := Impl.Dsa.Arm.RandomSign.code "vg_dsa_sign" (Impl.Dsa.Arm.Entry.operation true)
    verified := Proof.Dsa.Arm.randomSigning_verified
    stack := 144 },
  Spec.Dsa.verifyApi.artifact Arm.target {
    code := Impl.Dsa.Arm.Entry.operation false
    verified := Proof.Dsa.Arm.verify_verified },
  Spec.Dsa.deriveKeyApi.artifact Arm.target {
    code := Impl.Dsa.Arm.Generate.deriveKey
    verified := Proof.Dsa.Arm.derive_verified },
  Spec.Dsa.generateKeyApi.artifact Arm.target {
    code := Impl.Dsa.Arm.GenerateKey.code "vg_dsa_check_parameters" Spec.Dsa.deriveKeyApi.name
      Impl.Dsa.Arm.Generate.checkParameters Impl.Dsa.Arm.Generate.deriveKey
    verified := Proof.Dsa.Arm.Key.generating_verified
    stack := 144 }]

end VG.Artifacts.Dsa.Arm
