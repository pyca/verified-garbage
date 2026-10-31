module

public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CBC (NIST SP 800-38A §6.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCbc.PPC64LE

open VG.Proof.AesCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact PPC64LE.target {
    code := Impl.AesCbc.PPC64LE.encrypt
    verified := encrypt_verified },
  Spec.Cbc.aesDecryptApi.artifact PPC64LE.target {
    code := Impl.AesCbc.PPC64LE.decrypt
    verified := decrypt_verified }]

end VG.Artifacts.AesCbc.PPC64LE
