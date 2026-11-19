module

public import VerifiedGarbage.Proof.AesCfb8.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.AArch64.ModesScrub
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesCfb8.AArch64

open VG.Proof.AesCfb8.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.AArch64.variants.attach.flatMap
      fun (v : { v : Proof.Aes.AArch64.BlocksImpl // v ∈ VG.Proof.Variants.AesBlocks.AArch64.variants }) => [
    Spec.Cfb8.aesEncryptApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.AesCfb8.AArch64.encrypt v.1.enc
      verified := Proof.AesCfb8.encrypt_keyed (encrypt_verified v.1) }
      (AArch64.ScrubAll.clearUnion Proof.Aes.AArch64.ModesScrub.cfb8EncryptOwn v.1.encClear)
      Proof.Aes.AArch64.ModesScrub.cfb8EncryptOk (Proof.Aes.AArch64.ModesScrub.cfb8EncryptSide v.1 v.2)),
    Spec.Cfb8.aesDecryptApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.AesCfb8.AArch64.decrypt v.1.enc
      verified := Proof.AesCfb8.decrypt_keyed (decrypt_verified v.1) }
      (AArch64.ScrubAll.clearUnion Proof.Aes.AArch64.ModesScrub.cfb8DecryptOwn v.1.encClear)
      Proof.Aes.AArch64.ModesScrub.cfb8DecryptOk (Proof.Aes.AArch64.ModesScrub.cfb8DecryptSide v.1 v.2))]

end VG.Artifacts.AesCfb8.AArch64
