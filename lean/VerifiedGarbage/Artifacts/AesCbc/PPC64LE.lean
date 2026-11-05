module

public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # AES-CBC (NIST SP 800-38A §6.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCbc.PPC64LE

open VG.Proof.AesCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact PPC64LE.target {
    code := Impl.AesCbc.PPC64LE.encrypt
    verified := Proof.AesCbc.encrypt_keyed encrypt_verified },
  Spec.Cbc.aesDecryptApi.artifact PPC64LE.target {
    code := Impl.AesCbc.PPC64LE.decrypt
    verified := Proof.AesCbc.decrypt_keyed decrypt_verified }]

end VG.Artifacts.AesCbc.PPC64LE
