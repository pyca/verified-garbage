module

public import VerifiedGarbage.Impl.AesXts.X86Unit
public import VerifiedGarbage.Proof.AesXts.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Variants.AesXts.X86

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesXts.X86

def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.AesXts.X86.variants.flatMap fun (v : Proof.AesXts.X86.XtsImpl) => [
    Spec.Xts.aesEncryptUnitApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesXts.X86Unit.Fn.encrypt v.enc
      verified := Proof.AesXts.X86.Scrub.encryptUnit_scrubbed v
      spSafe := Proof.AesXts.X86.Scrub.encryptUnit_fnSpSafe v },
    Spec.Xts.aesDecryptUnitApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesXts.X86Unit.Fn.decrypt v.enc v.dec
      verified := Proof.AesXts.X86.Scrub.decryptUnit_scrubbed v
      spSafe := Proof.AesXts.X86.Scrub.decryptUnit_fnSpSafe v }]

end VG.Artifacts.AesXts.X86
