module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cbc.Contract
import VerifiedGarbage.Proof.Aes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CBC (NIST SP 800-38A §6.2) on ARMv7 -/

namespace VG.Artifacts.AesCbc.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Cbc.aesEncryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cbcEncrypt
    verified := Proof.Aes.Arm.Fn.cbcEncrypt
    publicOutOk := Proof.Aes.Arm.Fn.cbcEncrypt_public },
  Spec.Cbc.aesDecryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cbcDecrypt
    verified := Proof.Aes.Arm.Fn.cbcDecrypt
    publicOutOk := Proof.Aes.Arm.Fn.cbcDecrypt_public }]

spec_apis artifacts

end VG.Artifacts.AesCbc.Arm
