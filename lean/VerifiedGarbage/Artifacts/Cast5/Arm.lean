module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.Proof.Cast5.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5 (RFC 2144) on ARMv7 -/

namespace VG.Artifacts.Cast5.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Cast5.expandKeyApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.expandKey
    verified := Proof.Cast5.Arm.Fn.expandKey },
  Spec.Cast5.ecbEncryptApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.ecbEncrypt
    verified := Proof.Cast5.Arm.Fn.ecbEncrypt },
  Spec.Cast5.ecbDecryptApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.ecbDecrypt
    verified := Proof.Cast5.Arm.Fn.ecbDecrypt }]

spec_apis artifacts

end VG.Artifacts.Cast5.Arm
