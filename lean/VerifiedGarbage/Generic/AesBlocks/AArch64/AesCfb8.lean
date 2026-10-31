module

public import VerifiedGarbage.Proof.AesCfb8.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CFB8 (NIST SP 800-38A §6.3, with 8-bit segments) on AArch64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.AArch64.AesCfb8

open VG.Proof.AesCfb8.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  Spec.Cfb8.aesEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesCfb8.AArch64.encrypt v.enc
    verified := encrypt_verified v
    features := v.features },
  Spec.Cfb8.aesDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesCfb8.AArch64.decrypt v.enc
    verified := decrypt_verified v
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesCfb8
