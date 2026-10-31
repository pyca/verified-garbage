module

public import VerifiedGarbage.Proof.AesCcm.AArch64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
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
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.AesCcm.AArch64.Crypt
import VerifiedGarbage.Proof.AesCcm.AArch64.CtrCT
import VerifiedGarbage.Proof.AesCcm.AArch64.Header
import VerifiedGarbage.Proof.AesCcm.AArch64.Mac
import VerifiedGarbage.Proof.AesCcm.AArch64.Open
import VerifiedGarbage.Proof.AesCcm.AArch64.OpenCT
import VerifiedGarbage.Proof.AesCcm.AArch64.Rel
import VerifiedGarbage.Proof.AesCcm.AArch64.Seal
import VerifiedGarbage.Proof.AesCcm.AArch64.Tag
import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel

/-! # AES-CCM (NIST SP 800-38C) on AArch64 -/

@[expose] public section

namespace VG.Generic.CmacAesUpdate.AArch64.AesCcm

open VG.Proof.AesCcm.AArch64

def artifacts (v : Proof.CmacAes.AArch64.UpdateImpl) : List Artifact := [
  Spec.Ccm.sealApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (Impl.AesCcm.AArch64.seal v.callee v.ctr.callee)
    stack := 2592
    verified := seal_framed v
    features := v.features },
  Spec.Ccm.openApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (Impl.AesCcm.AArch64.open v.callee v.ctr.callee)
    stack := 2592
    verified := open_framed v
    features := v.features }]

end VG.Generic.CmacAesUpdate.AArch64.AesCcm
