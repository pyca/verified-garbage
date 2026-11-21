module

public import VerifiedGarbage.Impl.AesOfb.X86_64.Fn
public import VerifiedGarbage.Impl.AesCfb8.X86_64.Fn
public import VerifiedGarbage.Impl.AesCfb.X86_64.Fn
public import VerifiedGarbage.Proof.AesCfb.X86_64.Verified
public import VerifiedGarbage.Proof.AesCfb.X86_64.Final
public import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub
public import VerifiedGarbage.Proof.Aes.X86_64.FinalScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86_64

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesCfb.X86_64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86_64.variants.flatMap fun (v : Proof.Aes.X86_64.BlocksImpl) => [
    Spec.Cfb.aesEncryptApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesCfb.X86_64.Fn.cfbEncrypt v.level v.enc
      verified := Proof.Aes.X86_64.ModesScrub.cfbEncrypt_scrubbed v
      spSafe := Proof.Aes.X86_64.ModesScrub.cfbEncrypt_spSafeFn v },
    Spec.Cfb.aesDecryptApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesCfb.X86_64.Fn.cfbDecrypt v.level v.enc
      verified := Proof.Aes.X86_64.ModesScrub.cfbDecrypt_scrubbed v
      spSafe := Proof.Aes.X86_64.ModesScrub.cfbDecrypt_spSafeFn v },
    Spec.Cfb.aesEncryptFinalApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesCfb.X86_64.Fn.cfbEncryptFinal v.level v.enc v.suffix
      verified := Proof.Aes.X86_64.FinalScrub.cfbEncryptFinal_scrubbed v
      spSafe := Proof.Aes.X86_64.FinalScrub.cfbEncryptFinal_spSafeFn v },
    Spec.Cfb.aesDecryptFinalApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesCfb.X86_64.Fn.cfbDecryptFinal v.level v.enc v.suffix
      verified := Proof.Aes.X86_64.FinalScrub.cfbDecryptFinal_scrubbed v
      spSafe := Proof.Aes.X86_64.FinalScrub.cfbDecryptFinal_spSafeFn v }]

end VG.Artifacts.AesCfb.X86_64
