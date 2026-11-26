module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Impl.AesCfb8.X86
import VerifiedGarbage.Proof.AesCfb8.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesBlocks.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on x86 -/

namespace VG.Artifacts.AesCfb8.X86

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Cfb8.aesEncryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCfb8.X86.Fn.encrypt v.enc
      verified := Proof.AesCfb8.X86.Scrub.encrypt_scrubbed v
      spSafe := Proof.AesCfb8.X86.Scrub.encrypt_fnSpSafe v },
    Spec.Cfb8.aesDecryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCfb8.X86.Fn.decrypt v.enc
      verified := Proof.AesCfb8.X86.Scrub.decrypt_scrubbed v
      spSafe := Proof.AesCfb8.X86.Scrub.decrypt_fnSpSafe v }]

spec_apis artifacts

end VG.Artifacts.AesCfb8.X86
