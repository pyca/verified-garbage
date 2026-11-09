module

public import VerifiedGarbage.Proof.AesCfb8.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64

/-! # AES-CFB8 (NIST SP 800-38A §6.3, with 8-bit segments) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesCfb8.AArch64

open VG.Proof.AesCfb8.AArch64

def artifactsFor (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  Spec.Cfb8.aesEncryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesCfb8.AArch64.encrypt v.enc
    verified := Proof.AesCfb8.encrypt_keyed (encrypt_verified v)
    features := v.features },
  Spec.Cfb8.aesDecryptApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesCfb8.AArch64.decrypt v.enc
    verified := Proof.AesCfb8.decrypt_keyed (decrypt_verified v)
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesCfb8.AArch64
