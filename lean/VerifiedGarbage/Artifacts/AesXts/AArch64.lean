module

public import VerifiedGarbage.Proof.AesXts.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesXts.AArch64.Scrub
public import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Verified
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesXts.AArch64

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesXts.AArch64

open VG.Proof.AesXts.AArch64.Unit

open VG.Proof.AesXts.AArch64

def artifacts : List Artifact := [
  ] ++
  (VG.Proof.Variants.AesXts.AArch64.variants.attach.flatMap
      fun (v : { v : Proof.AesXts.AArch64.XtsImpl // v ∈ VG.Proof.Variants.AesXts.AArch64.variants }) => [
    Spec.Xts.aesEncryptUnitApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.AesXts.AArch64Unit.encrypt v.1.enc
      verified := encrypt_verified v.1 }
      (AArch64.ScrubAll.clearUnion Proof.AesXts.AArch64.Scrub.encryptOwn v.1.encClear)
      Proof.AesXts.AArch64.Scrub.encryptOk (Proof.AesXts.AArch64.Scrub.encryptSide v.1 v.2)),
    Spec.Xts.aesDecryptUnitApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.AesXts.AArch64Unit.decrypt v.1.enc v.1.dec
      verified := decrypt_verified v.1 }
      (AArch64.ScrubAll.clearUnion
        (AArch64.ScrubAll.clearUnion Proof.AesXts.AArch64.Scrub.decryptOwn v.1.encClear) v.1.decClear)
      Proof.AesXts.AArch64.Scrub.decryptOk (Proof.AesXts.AArch64.Scrub.decryptSide v.1 v.2))])

end VG.Artifacts.AesXts.AArch64
