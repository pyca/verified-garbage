module

public import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.AArch64
public import VerifiedGarbage.Proof.Variants.CmacAesUpdate.AArch64

/-! # AES-CMAC (NIST SP 800-38B) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.CmacAes.AArch64

open VG.Proof.CmacAes.Stream.AArch64

def artifacts : List Artifact :=
  (VG.Proof.Variants.CmacAesUpdate.AArch64.variants.map fun (v : Proof.CmacAes.AArch64.UpdateImpl) =>
    Spec.Cmac.aesAbsorbApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.AArch64.Fn.absorb v.callee
      verified := absorb_scrubbed v }) ++
  (VG.Proof.Variants.AesCtr32.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.Ctr32Impl) => [
    Spec.Cmac.aesInitApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.AArch64.Fn.init v.expand v.callee v.suffix
      verified := init_scrubbed v },
    Spec.Cmac.aesFinishApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.CmacAes.Stream.AArch64.Fn.finish v.callee v.suffix
      verified := finish_scrubbed v }])

end VG.Artifacts.CmacAes.AArch64
