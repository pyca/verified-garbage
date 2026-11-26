module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Impl.EcKey.P224.AArch64
import VerifiedGarbage.Proof.EcKey.AArch64.P224.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P224
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P224Decompress
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P224.AArch64.Law
import VerifiedGarbage.Proof.P224.Comb7
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-224 public keys (FIPS 186-5 §A.2) on AArch64 -/

namespace VG.Artifacts.EcP224.AArch64

open VG.Proof.P224.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressP224
    verified := Proof.EcKey.Compressed.AArch64.P224.scrubbed hasLaw.inv },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressP224
    verified := Proof.EcKey.Compressed.AArch64.P224Decompress.scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.P224.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeyP224
    verified := Proof.EcKey.AArch64.P224.pk_scrubbed hasLaw.law hasLaw.inv (Proof.P224.combOk7 hasLaw.law) }]

spec_apis artifacts

end VG.Artifacts.EcP224.AArch64
