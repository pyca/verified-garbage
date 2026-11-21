module

public import VerifiedGarbage.Impl.AesCfb.X86.Final
public import VerifiedGarbage.Proof.AesCfb.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCfb.X86

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Cfb.aesEncryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCfb.X86.Fn.encrypt (Proof.AesCfb.X86.encryptCode v)
      verified := Proof.AesCfb.X86.Scrub.encrypt_scrubbed v
      spSafe := Proof.AesCfb.X86.Scrub.encrypt_fnSpSafe v },
    Spec.Cfb.aesDecryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCfb.X86.Fn.decrypt v.enc
      verified := Proof.AesCfb.X86.Scrub.decrypt_scrubbed v
      spSafe := Proof.AesCfb.X86.Scrub.decrypt_fnSpSafe v },
    Spec.Cfb.aesEncryptFinalApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCfb.X86.Fn.encryptFinal (Proof.AesCfb.X86.encryptCode v) v.enc v.suffix
      verified := Proof.AesCfb.X86.Scrub.encryptFinal_scrubbed v
      spSafe := Proof.AesCfb.X86.Scrub.encryptFinal_fnSpSafe v },
    Spec.Cfb.aesDecryptFinalApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCfb.X86.Fn.decryptFinal v.enc v.suffix
      verified := Proof.AesCfb.X86.Scrub.decryptFinal_scrubbed v
      spSafe := Proof.AesCfb.X86.Scrub.decryptFinal_fnSpSafe v }]

end VG.Artifacts.AesCfb.X86
