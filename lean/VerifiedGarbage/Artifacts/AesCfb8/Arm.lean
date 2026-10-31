module

public import VerifiedGarbage.Proof.AesCfb8.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CFB8 (NIST SP 800-38A §6.3, with 8-bit segments) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCfb8.Arm

open VG.Proof.AesCfb8.Arm

def artifacts : List Artifact := [
  Spec.Cfb8.aesEncryptApi.artifact Arm.target {
    code := Impl.AesCfb8.Arm.encrypt
    stack := 8
    verified := encrypt_verified },
  Spec.Cfb8.aesDecryptApi.artifact Arm.target {
    code := Impl.AesCfb8.Arm.decrypt
    stack := 8
    verified := decrypt_verified }]

end VG.Artifacts.AesCfb8.Arm
