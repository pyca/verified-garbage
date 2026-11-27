module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.TripleDes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES on ARMv7 -/

namespace VG.Artifacts.TripleDes.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.TripleDes.expandKeyApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.expandKey
    verified := Proof.TripleDes.Arm.Fn.expandKey },
  Spec.TripleDes.ecbEncryptApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.ecbEncrypt
    verified := Proof.TripleDes.Arm.Fn.ecbEncrypt },
  Spec.TripleDes.ecbDecryptApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.ecbDecrypt
    verified := Proof.TripleDes.Arm.Fn.ecbDecrypt }]

spec_apis artifacts

end VG.Artifacts.TripleDes.Arm
