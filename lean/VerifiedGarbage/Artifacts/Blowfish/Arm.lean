module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Contract
import VerifiedGarbage.Proof.Blowfish.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish on ARMv7 -/

namespace VG.Artifacts.Blowfish.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Blowfish.expandKeyApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.expandKey
    verified := Proof.Blowfish.Arm.Fn.expandKey },
  Spec.Blowfish.ecbEncryptApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.ecbEncrypt
    verified := Proof.Blowfish.Arm.Fn.ecbEncrypt },
  Spec.Blowfish.ecbDecryptApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.ecbDecrypt
    verified := Proof.Blowfish.Arm.Fn.ecbDecrypt }]

spec_apis artifacts

end VG.Artifacts.Blowfish.Arm
