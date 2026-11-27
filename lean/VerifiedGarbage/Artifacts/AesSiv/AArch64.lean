module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.AesSiv.AArch64.Frame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesCtr32.AArch64
import VerifiedGarbage.Proof.Variants.CmacAesUpdate.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-SIV (RFC 5297) on AArch64 -/

namespace VG.Artifacts.AesSiv.AArch64

open VG.Proof.AesSiv.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  (VG.Proof.Variants.AesCtr32.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.Ctr32Impl) => [
    Spec.Siv.initApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesSiv.AArch64.Fn.init v.expand v.callee v.suffix
      verified := Proof.AesSiv.AArch64.init_scrubbed v }]) ++
  (VG.Proof.Variants.CmacAesUpdate.AArch64.variants.flatMap fun (v : Proof.CmacAes.AArch64.UpdateImpl) => [
    Spec.Siv.encryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesSiv.AArch64.Fn.encrypt v.callee v.ctr.callee v.ctr.suffix
      verified := Proof.AesSiv.AArch64.encrypt_scrubbed v },
    Spec.Siv.decryptApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesSiv.AArch64.Fn.decrypt v.callee v.ctr.callee v.ctr.suffix
      verified := Proof.AesSiv.AArch64.decrypt_scrubbed v }])

spec_apis artifacts

end VG.Artifacts.AesSiv.AArch64
