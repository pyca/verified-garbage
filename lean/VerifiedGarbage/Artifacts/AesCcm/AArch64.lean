module

public import VerifiedGarbage.Proof.AesCcm.AArch64.Frame
public import VerifiedGarbage.Proof.AesCcm.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
public import VerifiedGarbage.Proof.AesCcm.AArch64.Crypt
public import VerifiedGarbage.Proof.AesCcm.AArch64.CtrCT
public import VerifiedGarbage.Proof.AesCcm.AArch64.Header
public import VerifiedGarbage.Proof.AesCcm.AArch64.Mac
public import VerifiedGarbage.Proof.AesCcm.AArch64.Open
public import VerifiedGarbage.Proof.AesCcm.AArch64.OpenCT
public import VerifiedGarbage.Proof.AesCcm.AArch64.Rel
public import VerifiedGarbage.Proof.AesCcm.AArch64.Seal
public import VerifiedGarbage.Proof.AesCcm.AArch64.Tag
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
public import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.CmacAesUpdate.AArch64

/-! # AES-CCM (NIST SP 800-38C) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesCcm.AArch64

open VG.Proof.AesCcm.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.CmacAesUpdate.AArch64.variants.flatMap fun (v : Proof.CmacAes.AArch64.UpdateImpl) => [
    Spec.Ccm.sealApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.suffix
      code := Impl.StackScratch.AArch64.withStackArgScratch (416 + v.scratch) 2
        (Impl.AesCcm.AArch64.seal v.callee v.ctr.callee)
      verified := Proof.AesCcm.seal_keyed (seal_framed v) } (Scrub.sealOk _)),
    Spec.Ccm.openApi.artifact AArch64.target (AArch64.ScrubAll.withScrubAll {
      suffix := v.suffix
      code := Impl.StackScratch.AArch64.withStackArgScratch (416 + v.scratch) 2
        (Impl.AesCcm.AArch64.open v.callee v.ctr.callee)
      verified := Proof.AesCcm.open_keyed (open_framed v) } (Scrub.openOk _))]

end VG.Artifacts.AesCcm.AArch64
