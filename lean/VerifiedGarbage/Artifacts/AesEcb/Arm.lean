module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.AesEcb.Contract
import VerifiedGarbage.Proof.Aes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-ECB (NIST SP 800-38A §6.1) on ARMv7 -/

namespace VG.Artifacts.AesEcb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.AesEcb.encryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.ecbEncrypt
    verified := Proof.Aes.Arm.Fn.ecbEncrypt
    publicOutOk := Proof.Aes.Arm.Fn.ecbEncrypt_public },
  Spec.AesEcb.decryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.ecbDecrypt
    verified := Proof.Aes.Arm.Fn.ecbDecrypt
    publicOutOk := Proof.Aes.Arm.Fn.ecbDecrypt_public }]

spec_apis artifacts

end VG.Artifacts.AesEcb.Arm
