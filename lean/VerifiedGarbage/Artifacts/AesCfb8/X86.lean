module

public import VerifiedGarbage.Impl.AesCfb8.X86
public import VerifiedGarbage.Proof.AesCfb8.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCfb8.X86

def artifacts : List Artifact :=
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

end VG.Artifacts.AesCfb8.X86
