module

public import VerifiedGarbage.Proof.Aes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCfb8.Arm

def artifacts : List Artifact := [
  Spec.Cfb8.aesEncryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cfb8Encrypt
    verified := Proof.Aes.Arm.Fn.cfb8Encrypt },
  Spec.Cfb8.aesDecryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cfb8Decrypt
    verified := Proof.Aes.Arm.Fn.cfb8Decrypt }]

end VG.Artifacts.AesCfb8.Arm
