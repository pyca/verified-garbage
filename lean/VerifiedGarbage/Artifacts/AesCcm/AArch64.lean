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
  VG.Proof.Variants.CmacAesUpdate.AArch64.variants.attach.flatMap
      fun (v : { v : Proof.CmacAes.AArch64.UpdateImpl // v ∈ VG.Proof.Variants.CmacAesUpdate.AArch64.variants }) => [
    Spec.Ccm.sealApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.StackScratch.AArch64.withStackArgScratch (416 + v.1.scratch) 2
        (Impl.AesCcm.AArch64.seal v.1.callee v.1.ctr.callee)
      verified := Proof.AesCcm.seal_keyed (seal_framed v.1) }
      (AArch64.ScrubAll.clearUnion Scrub.sealOwn v.1.ctr.clear)
      (Scrub.sealOk _) (Scrub.sealSide v.1 v.2)),
    Spec.Ccm.openApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.StackScratch.AArch64.withStackArgScratch (416 + v.1.scratch) 2
        (Impl.AesCcm.AArch64.open v.1.callee v.1.ctr.callee)
      verified := Proof.AesCcm.open_keyed (open_framed v.1) }
      (AArch64.ScrubAll.clearUnion Scrub.openOwn v.1.ctr.clear)
      (Scrub.openOk _) (Scrub.openSide v.1 v.2))]

end VG.Artifacts.AesCcm.AArch64
