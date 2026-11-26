module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.Impl.EcKey.P192.AArch64
import VerifiedGarbage.Proof.EcKey.AArch64.P192.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P192
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Residue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P192.AArch64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-192 public keys (FIPS 186-5 §A.2) on AArch64 -/

namespace VG.Artifacts.EcP192.AArch64

open VG.Proof.P192.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressP192
    verified := Proof.EcKey.Compressed.AArch64.P192.scrubbed hasLaw.inv },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressP192
    verified := Proof.EcKey.Compressed.AArch64.Residue.P192.scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.P192.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeyP192
    verified := Proof.EcKey.AArch64.P192.pk_scrubbed hasLaw.law hasLaw.inv }]

spec_apis artifacts

end VG.Artifacts.EcP192.AArch64
