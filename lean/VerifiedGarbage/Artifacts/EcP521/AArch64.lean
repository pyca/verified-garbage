module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Impl.EcKey.P521.AArch64
import VerifiedGarbage.Proof.EcKey.AArch64.P521.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P521
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P521Decompress
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P521.AArch64.Law
import VerifiedGarbage.Proof.P521.Comb7
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-521 public keys (FIPS 186-5 §A.2) on AArch64 -/

namespace VG.Artifacts.EcP521.AArch64

open VG.Proof.P521.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressP521
    verified := Proof.EcKey.Compressed.AArch64.P521.scrubbed hasLaw.inv },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressP521
    verified := Proof.EcKey.Compressed.AArch64.P521Decompress.scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.P521.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeyP521
    verified := Proof.EcKey.AArch64.P521.pk_scrubbed hasLaw.law hasLaw.inv (Proof.P521.combOk7 hasLaw.law) }]

spec_apis artifacts

end VG.Artifacts.EcP521.AArch64
