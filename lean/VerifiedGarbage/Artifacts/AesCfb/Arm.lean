module

public import VerifiedGarbage.Proof.AesCfb.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCfb.Arm

open VG.Proof.AesCfb.Arm

def artifacts : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact Arm.target {
    code := Impl.AesCfb.Arm.encrypt
    stack := 8
    verified := encrypt_verified },
  Spec.Cfb.aesDecryptApi.artifact Arm.target {
    code := Impl.AesCfb.Arm.decrypt
    stack := 8
    verified := decrypt_verified }]

end VG.Artifacts.AesCfb.Arm
