module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Xts.Contract
import VerifiedGarbage.Proof.AesXts.AArch64.Variant
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Verified
import VerifiedGarbage.Proof.Variants.AesXts.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on AArch64 -/

namespace VG.Artifacts.AesXts.AArch64

open VG.Proof.AesXts.AArch64.Unit

open VG.Proof.AesXts.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.AesXts.AArch64.variants.flatMap fun (v : Proof.AesXts.AArch64.XtsImpl) => [
    Spec.Xts.aesEncryptUnitApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesXts.AArch64Unit.Fn.encrypt v.enc
      verified := Proof.AesXts.AArch64.Unit.encrypt_scrubbed v },
    Spec.Xts.aesDecryptUnitApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesXts.AArch64Unit.Fn.decrypt v.enc v.dec
      verified := Proof.AesXts.AArch64.Unit.decrypt_scrubbed v }]

spec_apis artifacts

end VG.Artifacts.AesXts.AArch64
