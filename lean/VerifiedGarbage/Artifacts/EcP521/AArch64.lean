module

public import VerifiedGarbage.Impl.EcKey.P521.AArch64
public import VerifiedGarbage.Proof.EcKey.AArch64.P521.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P521
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P521Decompress
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P521.AArch64.Law
public import VerifiedGarbage.Proof.P521.Comb7
public import VerifiedGarbage.Spec.EcKey.P521
public import VerifiedGarbage.TCB.AArch64.Print

/-! # P-521 public keys (FIPS 186-5 §A.2) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcP521.AArch64

open VG.Proof.P521.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressP521
    verified := Proof.EcKey.Compressed.AArch64.P521.scrubbed hasLaw.inv },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressP521
    verified := Proof.EcKey.Compressed.AArch64.P521Decompress.scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.P521.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeyP521
    verified := Proof.EcKey.AArch64.P521.pk_scrubbed hasLaw.law hasLaw.inv (Proof.P521.combOk7 hasLaw.law) }]

end VG.Artifacts.EcP521.AArch64
