module

public import VerifiedGarbage.Proof.AesCfb8.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCfb8.PPC64LE

open VG.Proof.AesCfb8.PPC64LE

def artifacts : List Artifact := [
  Spec.Cfb8.aesEncryptApi.artifact PPC64LE.target {
    code := Impl.AesCfb8.PPC64LE.encrypt
    verified := encrypt_verified },
  Spec.Cfb8.aesDecryptApi.artifact PPC64LE.target {
    code := Impl.AesCfb8.PPC64LE.decrypt
    verified := decrypt_verified }]

end VG.Artifacts.AesCfb8.PPC64LE
