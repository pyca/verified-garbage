module

public import VerifiedGarbage.Proof.AesCfb8.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesCfb8.AArch64

open VG.Proof.AesCfb8.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.BlocksImpl) => [
    Spec.Cfb8.aesEncryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb8.AArch64.Fn.encrypt v.enc
      verified := .scrubbed (encrypt_scrubbed v) },
    Spec.Cfb8.aesDecryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb8.AArch64.Fn.decrypt v.enc
      verified := .scrubbed (decrypt_scrubbed v) }]

end VG.Artifacts.AesCfb8.AArch64
