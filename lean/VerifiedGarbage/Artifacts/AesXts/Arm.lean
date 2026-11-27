module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Xts.Contract
import VerifiedGarbage.Proof.Aes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on ARMv7 -/

namespace VG.Artifacts.AesXts.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Xts.aesEncryptUnitApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.xtsEncrypt
    verified := Proof.Aes.Arm.Fn.xtsEncrypt },
  Spec.Xts.aesDecryptUnitApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.xtsDecrypt
    verified := Proof.Aes.Arm.Fn.xtsDecrypt }]

spec_apis artifacts

end VG.Artifacts.AesXts.Arm
