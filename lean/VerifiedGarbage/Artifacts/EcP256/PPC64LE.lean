module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P256.PPC64LE.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-256 public keys (FIPS 186-5 §A.2) on PPC64LE -/

namespace VG.Artifacts.EcP256.PPC64LE

open VG.Proof.P256.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p256Compress
    verified := Proof.EcKey.PPC64LE.Scrub.p256Compress_scrubbed },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p256Decompress
    verified := Proof.EcKey.PPC64LE.Scrub.p256Decompress_scrubbed hasLaw.law },
  Spec.EcKey.P256.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p256PublicKey
    verified := Proof.EcKey.PPC64LE.Scrub.p256PublicKey_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP256.PPC64LE
