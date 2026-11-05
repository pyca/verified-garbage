module

public import VerifiedGarbage.Proof.AesCfb.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCfb.Arm

open VG.Proof.AesCfb.Arm

def artifacts : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact Arm.target {
    code := Impl.AesCfb.Arm.encrypt
    stack := 8
    verified := Proof.AesCfb.encrypt_keyed encrypt_verified },
  Spec.Cfb.aesDecryptApi.artifact Arm.target {
    code := Impl.AesCfb.Arm.decrypt
    stack := 8
    verified := Proof.AesCfb.decrypt_keyed decrypt_verified }]

end VG.Artifacts.AesCfb.Arm
