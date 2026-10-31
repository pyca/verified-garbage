module

public import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CBC (NIST SP 800-38A §6.2) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86_64.AesCbc

open VG.Proof.AesCbc.X86_64

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesCbc.X86_64.encrypt v.enc
    stack := 8
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Cbc.aesDecryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesCbc.X86_64.decrypt v.dec
    stack := 8
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86_64.AesCbc
