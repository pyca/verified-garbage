module

public import VerifiedGarbage.Proof.AesCfb.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesCfb.PPC64LE.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCfb.PPC64LE

open VG.Proof.AesCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact PPC64LE.target {
    code := Impl.AesCfb.PPC64LE.encrypt
    verified := Proof.AesCfb.encrypt_keyed encrypt_verified },
  Spec.Cfb.aesDecryptApi.artifact PPC64LE.target {
    code := Impl.AesCfb.PPC64LE.decrypt
    verified := Proof.AesCfb.decrypt_keyed decrypt_verified },
  Spec.Cfb.aesEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r9 8 Impl.AesCfb.PPC64LE.encryptFinal
    stack := 96
    verified := Proof.AesCfb.encryptFinal_keyed Final.encryptFinal_framed },
  Spec.Cfb.aesDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r9 8 Impl.AesCfb.PPC64LE.decryptFinal
    stack := 96
    verified := Proof.AesCfb.decryptFinal_keyed Final.decryptFinal_framed }]

end VG.Artifacts.AesCfb.PPC64LE
