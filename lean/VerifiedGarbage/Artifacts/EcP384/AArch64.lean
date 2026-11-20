module

public import VerifiedGarbage.Impl.EcKey.P384.AArch64
public import VerifiedGarbage.Proof.EcKey.AArch64.P384.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P384
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P384Decompress
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P384.AArch64.Law
public import VerifiedGarbage.Proof.P384.Comb7
public import VerifiedGarbage.Spec.EcKey.P384
public import VerifiedGarbage.TCB.AArch64.Print

/-! # P-384 public keys (FIPS 186-5 §A.2) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcP384.AArch64

open VG.Proof.P384.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressP384
    verified := .scrubbed (Proof.EcKey.Compressed.AArch64.P384.scrubbed hasLaw.inv) },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressP384
    verified := .scrubbed (Proof.EcKey.Compressed.AArch64.P384Decompress.scrubbed hasLaw.law hasLaw.inv) },
  Spec.EcKey.P384.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeyP384
    verified := .scrubbed (Proof.EcKey.AArch64.P384.pk_scrubbed hasLaw.law hasLaw.inv (Proof.P384.combOk7 hasLaw.law)) }]

end VG.Artifacts.EcP384.AArch64
