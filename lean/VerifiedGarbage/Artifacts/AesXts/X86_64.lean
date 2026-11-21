module

public import VerifiedGarbage.Impl.AesXts.X86_64Fn
public import VerifiedGarbage.Proof.AesXts.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesXts.X86_64

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesXts.X86_64

def artifacts : List Artifact :=
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
      code := Impl.AesXts.X86_64UnitTo.Fn.encrypt v.level v.xts ⟨v.to.enc, v.to.dec⟩
      verified := Proof.AesXts.X86_64.Scrub.encryptUnitTo_scrubbed v
      spSafe := Proof.AesXts.X86_64.Scrub.encryptUnitTo_spSafeFn v },
    Spec.Xts.aesDecryptUnitToApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.AesXts.X86_64UnitTo.Fn.decrypt v.level v.xts ⟨v.to.enc, v.to.dec⟩
      verified := Proof.AesXts.X86_64.Scrub.decryptUnitTo_scrubbed v
      spSafe := Proof.AesXts.X86_64.Scrub.decryptUnitTo_spSafeFn v }]

end VG.Artifacts.AesXts.X86_64
