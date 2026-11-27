module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P384.PPC64LE.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-384 public keys (FIPS 186-5 §A.2) on PPC64LE -/

namespace VG.Artifacts.EcP384.PPC64LE

open VG.Proof.P384.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p384Compress
    verified := Proof.EcKey.PPC64LE.Scrub.p384Compress_scrubbed },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p384Decompress
    verified := Proof.EcKey.PPC64LE.Scrub.p384Decompress_scrubbed hasLaw.law },
  Spec.EcKey.P384.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p384PublicKey
    verified := Proof.EcKey.PPC64LE.Scrub.p384PublicKey_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP384.PPC64LE
