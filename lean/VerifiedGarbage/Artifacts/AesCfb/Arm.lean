module

public import VerifiedGarbage.Proof.Aes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCfb.Arm

def artifacts : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cfbEncrypt
    verified := Proof.Aes.Arm.Fn.cfbEncrypt },
  Spec.Cfb.aesDecryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cfbDecrypt
    verified := Proof.Aes.Arm.Fn.cfbDecrypt },
  Spec.Cfb.aesEncryptFinalApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cfbEncryptFinal
    verified := Proof.Aes.Arm.Fn.cfbEncryptFinal },
  Spec.Cfb.aesDecryptFinalApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cfbDecryptFinal
    verified := Proof.Aes.Arm.Fn.cfbDecryptFinal }]

end VG.Artifacts.AesCfb.Arm
