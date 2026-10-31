module

public import VerifiedGarbage.Proof.AesCbc.X86.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCbc.X86.Body

/-! # AES-CBC (NIST SP 800-38A §6.2) on x86 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86.AesCbc

open VG.Proof.AesCbc.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesCbc.X86.encrypt v.enc
    stack := 24
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Cbc.aesDecryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesCbc.X86.decrypt v.dec
    stack := 24
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesCbc
