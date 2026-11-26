module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Spec.Xts.OutOfPlace
import VerifiedGarbage.Impl.AesXts.X86_64Fn
import VerifiedGarbage.Proof.AesXts.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesXts.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86-64 -/

namespace VG.Artifacts.AesXts.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  VG.Proof.Variants.AesXts.X86_64.variants.flatMap fun (v : Proof.AesXts.X86_64.XtsImpl) => [
    Spec.Xts.aesEncryptUnitApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesXts.X86_64Unit.Fn.encrypt v.level v.xts
      verified := Proof.AesXts.X86_64.Scrub.encryptUnit_scrubbed v
      spSafe := Proof.AesXts.X86_64.Scrub.encryptUnit_spSafeFn v },
    Spec.Xts.aesDecryptUnitApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesXts.X86_64Unit.Fn.decrypt v.level v.xts
      verified := Proof.AesXts.X86_64.Scrub.decryptUnit_scrubbed v
      spSafe := Proof.AesXts.X86_64.Scrub.decryptUnit_spSafeFn v },
    Spec.Xts.aesEncryptUnitToApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesXts.X86_64UnitTo.Fn.encrypt v.level v.xts (Impl.AesXts.X86_64UnitTo.XtsTo.mk v.to.enc v.to.dec)
      verified := Proof.AesXts.X86_64.Scrub.encryptUnitTo_scrubbed v
      spSafe := Proof.AesXts.X86_64.Scrub.encryptUnitTo_spSafeFn v },
    Spec.Xts.aesDecryptUnitToApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesXts.X86_64UnitTo.Fn.decrypt v.level v.xts (Impl.AesXts.X86_64UnitTo.XtsTo.mk v.to.enc v.to.dec)
      verified := Proof.AesXts.X86_64.Scrub.decryptUnitTo_scrubbed v
      spSafe := Proof.AesXts.X86_64.Scrub.decryptUnitTo_spSafeFn v }]

spec_apis artifacts

end VG.Artifacts.AesXts.X86_64
