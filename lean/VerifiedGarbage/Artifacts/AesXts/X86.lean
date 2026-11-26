module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Xts.Contract
import VerifiedGarbage.Impl.AesXts.X86Unit
import VerifiedGarbage.Proof.AesXts.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesXts.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86 -/

namespace VG.Artifacts.AesXts.X86

public def artifacts : List (Artifact X86.target) :=
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

spec_apis artifacts

end VG.Artifacts.AesXts.X86
