module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Proof.AesCfb8.AArch64.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on AArch64 -/

namespace VG.Artifacts.AesCfb8.AArch64

open VG.Proof.AesCfb8.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.AesBlocks.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.BlocksImpl) => [
    Spec.Cfb8.aesEncryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb8.AArch64.Fn.encrypt v.enc
      verified := Proof.AesCfb8.AArch64.encrypt_scrubbed v },
    Spec.Cfb8.aesDecryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCfb8.AArch64.Fn.decrypt v.enc
      verified := Proof.AesCfb8.AArch64.decrypt_scrubbed v }]

spec_apis artifacts

end VG.Artifacts.AesCfb8.AArch64
