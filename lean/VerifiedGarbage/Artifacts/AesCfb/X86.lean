module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cfb.Contract
public import VerifiedGarbage.Spec.Cfb.Final
import VerifiedGarbage.Impl.AesCfb.X86.Final
import VerifiedGarbage.Proof.AesCfb.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesBlocks.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on x86 -/

namespace VG.Artifacts.AesCfb.X86

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Cfb.aesEncryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCfb.X86.Fn.encrypt (Proof.AesCfb.X86.encryptCode v)
      verified := Proof.AesCfb.X86.Scrub.encrypt_scrubbed v
      spSafe := Proof.AesCfb.X86.Scrub.encrypt_fnSpSafe v },
    Spec.Cfb.aesDecryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCfb.X86.Fn.decrypt (Proof.AesCfb.X86.decryptCode v) (Proof.AesCbc.X86.Wiped.decStack v)
      verified := Proof.AesCfb.X86.Scrub.decrypt_scrubbed v
      spSafe := Proof.AesCfb.X86.Scrub.decrypt_fnSpSafe v },
    Spec.Cfb.aesEncryptFinalApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCfb.X86.Fn.encryptFinal (Proof.AesCfb.X86.encryptCode v) v.enc v.suffix
      verified := Proof.AesCfb.X86.Scrub.encryptFinal_scrubbed v
      spSafe := Proof.AesCfb.X86.Scrub.encryptFinal_fnSpSafe v },
    Spec.Cfb.aesDecryptFinalApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesCfb.X86.Fn.decryptFinal (Proof.AesCfb.X86.decryptCode v) v.enc v.suffix
        (Proof.AesCbc.X86.Wiped.decStack v)
      verified := Proof.AesCfb.X86.Scrub.decryptFinal_scrubbed v
      spSafe := Proof.AesCfb.X86.Scrub.decryptFinal_fnSpSafe v }]

spec_apis artifacts

end VG.Artifacts.AesCfb.X86
