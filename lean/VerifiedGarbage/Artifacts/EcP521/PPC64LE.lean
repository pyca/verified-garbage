module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P521.PPC64LE.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-521 public keys (FIPS 186-5 §A.2) on PPC64LE -/

namespace VG.Artifacts.EcP521.PPC64LE

open VG.Proof.P521.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p521Compress
    verified := Proof.EcKey.PPC64LE.Scrub.p521Compress_scrubbed },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p521Decompress
    verified := Proof.EcKey.PPC64LE.Scrub.p521Decompress_scrubbed hasLaw.law },
  Spec.EcKey.P521.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p521PublicKey
    verified := Proof.EcKey.PPC64LE.Scrub.p521PublicKey_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP521.PPC64LE
