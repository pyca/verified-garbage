module

public import VerifiedGarbage.Proof.Aes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Target

/-! # AES-CBC (NIST SP 800-38A §6.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCbc.Arm

def artifacts : List (Artifact Arm.target) := [
  Spec.Cbc.aesEncryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cbcEncrypt
    verified := Proof.Aes.Arm.Fn.cbcEncrypt
    publicOutOk := Proof.Aes.Arm.Fn.cbcEncrypt_public },
  Spec.Cbc.aesDecryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cbcDecrypt
    verified := Proof.Aes.Arm.Fn.cbcDecrypt
    publicOutOk := Proof.Aes.Arm.Fn.cbcDecrypt_public }]

end VG.Artifacts.AesCbc.Arm
