module

public import VerifiedGarbage.Impl.AesXts.X86Unit
public import VerifiedGarbage.Proof.AesXts.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesXts.X86

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Xts.aesEncryptUnitApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesXts.X86Unit.Fn.encrypt (Proof.AesXts.X86.Unit.xtsE v)
      verified := Proof.AesXts.X86.Scrub.encryptUnit_scrubbed v
      spSafe := Proof.AesXts.X86.Scrub.encryptUnit_fnSpSafe v },
    Spec.Xts.aesDecryptUnitApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesXts.X86Unit.Fn.decrypt (Proof.AesXts.X86.Unit.xtsE v) (Proof.AesXts.X86.Unit.xtsD v)
      verified := Proof.AesXts.X86.Scrub.decryptUnit_scrubbed v
      spSafe := Proof.AesXts.X86.Scrub.decryptUnit_fnSpSafe v }]

end VG.Artifacts.AesXts.X86
