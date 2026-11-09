module

public import VerifiedGarbage.Proof.AesCfb.Arm.Verified
public import VerifiedGarbage.Proof.AesCfb.Arm.Final
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
    verified := Proof.AesCfb.decrypt_keyed decrypt_verified },
  Spec.Cfb.aesEncryptFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.encryptFinal
    stack := 72
    verified := Proof.AesCfb.encryptFinal_keyed encryptFinal_framed },
  Spec.Cfb.aesDecryptFinalApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 Impl.AesCfb.Arm.decryptFinal
    stack := 72
    verified := Proof.AesCfb.decryptFinal_keyed decryptFinal_framed }]

end VG.Artifacts.AesCfb.Arm
