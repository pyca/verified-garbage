module

public import VerifiedGarbage.Proof.AesCfb8.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CFB8 (NIST SP 800-38A §6.3, with 8-bit segments) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86_64.AesCfb8

open VG.Proof.AesCfb8.X86_64

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  Spec.Cfb8.aesEncryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesCfb8.X86_64.encrypt v.enc
    stack := 8
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Cfb8.aesDecryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesCfb8.X86_64.decrypt v.enc
    stack := 8
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86_64.AesCfb8
