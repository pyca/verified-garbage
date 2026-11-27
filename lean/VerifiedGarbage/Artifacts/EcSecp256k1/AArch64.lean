module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.Secp256k1
import VerifiedGarbage.Impl.EcKey.Secp256k1.AArch64
import VerifiedGarbage.Proof.EcKey.AArch64.Secp256k1.Verified
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Secp256k1
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Secp256k1Decompress
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Secp256k1.AArch64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on AArch64 -/

namespace VG.Artifacts.EcSecp256k1.AArch64

open VG.Proof.Secp256k1.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressSecp256k1
    verified := Proof.EcKey.Compressed.AArch64.Secp256k1.scrubbed hasLaw.inv },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressSecp256k1
    verified := Proof.EcKey.Compressed.AArch64.Secp256k1Decompress.scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.Secp256k1.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeySecp256k1
    verified := Proof.EcKey.AArch64.Secp256k1.pk_scrubbed hasLaw.law hasLaw.inv }]

spec_apis artifacts

end VG.Artifacts.EcSecp256k1.AArch64
