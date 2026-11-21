module

public import VerifiedGarbage.Proof.AesCcm.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.CmacAesUpdate.AArch64

/-! # AES-CCM (NIST SP 800-38C) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesCcm.AArch64

open VG.Proof.AesCcm.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.CmacAesUpdate.AArch64.variants.flatMap fun (v : Proof.CmacAes.AArch64.UpdateImpl) => [
    Spec.Ccm.sealApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCcm.AArch64.Fn.seal v.callee v.ctr.callee
      verified := seal_scrubbed v },
    Spec.Ccm.openApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.AesCcm.AArch64.Fn.open v.callee v.ctr.callee
      verified := open_scrubbed v }]

end VG.Artifacts.AesCcm.AArch64
