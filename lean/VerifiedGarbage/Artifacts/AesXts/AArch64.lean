module

public import VerifiedGarbage.Proof.AesXts.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
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
  (VG.Proof.Variants.AesXts.AArch64.variants.flatMap fun (v : Proof.AesXts.AArch64.XtsImpl) => [
    Spec.Xts.aesEncryptUnitApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesXts.AArch64Unit.encrypt v.enc
      verified := encrypt_verified v },
    Spec.Xts.aesDecryptUnitApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesXts.AArch64Unit.decrypt v.enc v.dec
      verified := decrypt_verified v }])

end VG.Artifacts.AesXts.AArch64
