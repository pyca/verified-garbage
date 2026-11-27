module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.Proof.AesOcb.AArch64.Frame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-OCB (RFC 7253) on AArch64 -/

namespace VG.Artifacts.AesOcb.AArch64

open VG.Proof.AesOcb.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.AesBlocks.AArch64.variants.flatMap fun (v : Proof.Aes.AArch64.BlocksImpl) => [
    Spec.Ocb.initApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesOcb.AArch64.Fn.init (Proof.AesOcb.AArch64.callees v)
      verified := Proof.AesOcb.AArch64.init_scrubbed v },
    Spec.Ocb.sealApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesOcb.AArch64.Fn.seal (Proof.AesOcb.AArch64.callees v)
      verified := Proof.AesOcb.AArch64.seal_scrubbed v },
    Spec.Ocb.openApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesOcb.AArch64.Fn.open (Proof.AesOcb.AArch64.callees v)
      verified := Proof.AesOcb.AArch64.open_scrubbed v }]

spec_apis artifacts

end VG.Artifacts.AesOcb.AArch64
