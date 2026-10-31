module

public import VerifiedGarbage.Proof.AesCfb.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86_64.AesCfb

open VG.Proof.AesCfb.X86_64

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesCfb.X86_64.encrypt v.enc
    stack := 8
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Cfb.aesDecryptApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesCfb.X86_64.decrypt v.enc
    stack := 8
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86_64.AesCfb
