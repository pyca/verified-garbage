module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.Proof.AesCcm.AArch64.Frame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.CmacAesUpdate.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CCM (NIST SP 800-38C) on AArch64 -/

namespace VG.Artifacts.AesCcm.AArch64

open VG.Proof.AesCcm.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.CmacAesUpdate.AArch64.variants.flatMap fun (v : Proof.CmacAes.AArch64.UpdateImpl) => [
    Spec.Ccm.sealApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCcm.AArch64.Fn.seal v.callee v.ctr.callee
      verified := Proof.AesCcm.AArch64.seal_scrubbed v },
    Spec.Ccm.openApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCcm.AArch64.Fn.open v.callee v.ctr.callee
      verified := Proof.AesCcm.AArch64.open_scrubbed v }]

spec_apis artifacts

end VG.Artifacts.AesCcm.AArch64
