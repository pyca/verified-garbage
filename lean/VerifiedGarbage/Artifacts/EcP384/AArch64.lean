module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Impl.EcKey.P384.AArch64
import VerifiedGarbage.Proof.EcKey.AArch64.P384.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P384
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P384Decompress
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P384.AArch64.Law
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-384 public keys (FIPS 186-5 §A.2) on AArch64 -/

namespace VG.Artifacts.EcP384.AArch64

open VG.Proof.P384.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressP384
    verified := Proof.EcKey.Compressed.AArch64.P384.scrubbed hasLaw.inv },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressP384
    verified := Proof.EcKey.Compressed.AArch64.P384Decompress.scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.P384.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeyP384
    verified := Proof.EcKey.AArch64.P384.pk_scrubbed hasLaw.law hasLaw.inv (Proof.P384.combOk7 hasLaw.law) }]

spec_apis artifacts

end VG.Artifacts.EcP384.AArch64
