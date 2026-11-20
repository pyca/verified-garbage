module

public import VerifiedGarbage.Impl.EcKey.P192.AArch64
public import VerifiedGarbage.Proof.EcKey.AArch64.P192.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P192
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P192.AArch64.Law
public import VerifiedGarbage.Spec.EcKey.P192
public import VerifiedGarbage.TCB.AArch64.Print

/-! # P-192 public keys (FIPS 186-5 §A.2) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcP192.AArch64

open VG.Proof.P192.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressP192
    verified := .scrubbed (Proof.EcKey.Compressed.AArch64.P192.scrubbed hasLaw.inv) },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressP192
    verified := .scrubbed (Proof.EcKey.Compressed.AArch64.Residue.P192.scrubbed hasLaw.law hasLaw.inv) },
  Spec.EcKey.P192.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeyP192
    verified := .scrubbed (Proof.EcKey.AArch64.P192.pk_scrubbed hasLaw.law hasLaw.inv) }]

end VG.Artifacts.EcP192.AArch64
