module

public import VerifiedGarbage.Proof.AesCfb.X86.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on x86 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86.AesCfb

open VG.Proof.AesCfb.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Cfb.aesEncryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesCfb.X86.encrypt v.enc
    stack := 24
    verified := encrypt_verified v
    spSafe := encrypt_spSafe v
    features := v.features },
  Spec.Cfb.aesDecryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesCfb.X86.decrypt v.enc
    stack := 24
    verified := decrypt_verified v
    spSafe := decrypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesCfb
