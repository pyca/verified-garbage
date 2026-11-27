module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Impl.EcKey.P256.AArch64
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P256
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Residue
import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P256.AArch64.Law
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-256 public keys (FIPS 186-5 §A.2) on AArch64 -/

namespace VG.Artifacts.EcP256.AArch64

open VG.Proof.P256.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressP256
    verified := Proof.EcKey.Compressed.AArch64.P256.scrubbed hasLaw.inv },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressP256
    verified := Proof.EcKey.Compressed.AArch64.Residue.P256.scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.P256.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeyP256
    verified := Proof.EcKey.AArch64.booth_pk_scrubbed hasLaw.law hasLaw.inv (Proof.P256.combOk7 hasLaw.law) }]

spec_apis artifacts

end VG.Artifacts.EcP256.AArch64
