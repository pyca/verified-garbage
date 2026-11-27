module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Frame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesCtr32.AArch64
import VerifiedGarbage.Proof.Variants.CmacAesUpdate.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CMAC (NIST SP 800-38B) on AArch64 -/

namespace VG.Artifacts.CmacAes.AArch64

open VG.Proof.CmacAes.Stream.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  (VG.Proof.Variants.CmacAesUpdate.AArch64.variants.map fun (v : Proof.CmacAes.AArch64.UpdateImpl) =>
    Spec.Cmac.aesAbsorbApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.AArch64.Fn.absorb v.callee
      verified := Proof.CmacAes.Stream.AArch64.absorb_scrubbed v }) ++
  (VG.Proof.Variants.AesCtr32.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.Ctr32Impl) => [
    Spec.Cmac.aesInitApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.AArch64.Fn.init v.expand v.callee v.suffix
      verified := Proof.CmacAes.Stream.AArch64.init_scrubbed v },
    Spec.Cmac.aesFinishApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.AArch64.Fn.finish v.callee v.suffix
      verified := Proof.CmacAes.Stream.AArch64.finish_scrubbed v }])

spec_apis artifacts

end VG.Artifacts.CmacAes.AArch64
