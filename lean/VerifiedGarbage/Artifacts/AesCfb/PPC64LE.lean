module

public import VerifiedGarbage.Proof.AesCfb.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCfb.PPC64LE

open VG.Proof.AesCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact PPC64LE.target {
    code := Impl.AesCfb.PPC64LE.encrypt
    verified := encrypt_verified },
  Spec.Cfb.aesDecryptApi.artifact PPC64LE.target {
    code := Impl.AesCfb.PPC64LE.decrypt
    verified := decrypt_verified }]

end VG.Artifacts.AesCfb.PPC64LE
