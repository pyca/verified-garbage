module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Impl.AesOfb.X86_64.Fn
import VerifiedGarbage.Impl.AesCfb8.X86_64.Fn
import VerifiedGarbage.Impl.AesCfb.X86_64.Fn
import VerifiedGarbage.Proof.AesCfb8.X86_64.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on x86-64 -/

namespace VG.Artifacts.AesCfb8.X86_64


public def artifacts : List (Artifact X86_64.target) :=
  VG.Proof.Variants.AesBlocks.X86_64.variants.flatMap fun (v : Proof.Aes.X86_64.BlocksImpl) => [
    Spec.Cfb8.aesEncryptApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesCfb8.X86_64.Fn.cfb8Encrypt v.level v.enc
      verified := Proof.Aes.X86_64.ModesScrub.cfb8Encrypt_scrubbed v
      spSafe := Proof.Aes.X86_64.ModesScrub.cfb8Encrypt_spSafeFn v },
    Spec.Cfb8.aesDecryptApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesCfb8.X86_64.Fn.cfb8Decrypt v.level v.enc
      verified := Proof.Aes.X86_64.ModesScrub.cfb8Decrypt_scrubbed v
      spSafe := Proof.Aes.X86_64.ModesScrub.cfb8Decrypt_spSafeFn v }]

spec_apis artifacts

end VG.Artifacts.AesCfb8.X86_64
