module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Contract
import VerifiedGarbage.Proof.Sm4.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4 on ARMv7 -/

namespace VG.Artifacts.Sm4.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Sm4.expandKeyApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.expandKey
    verified := Proof.Sm4.Arm.Fn.expandKey },
  Spec.Sm4.ecbEncryptApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.ecbEncrypt
    verified := Proof.Sm4.Arm.Fn.ecbEncrypt },
  Spec.Sm4.ecbDecryptApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.ecbDecrypt
    verified := Proof.Sm4.Arm.Fn.ecbDecrypt }]

spec_apis artifacts

end VG.Artifacts.Sm4.Arm
