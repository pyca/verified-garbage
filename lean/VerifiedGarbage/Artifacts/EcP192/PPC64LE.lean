module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P192.PPC64LE.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-192 public keys (FIPS 186-5 §A.2) on PPC64LE -/

namespace VG.Artifacts.EcP192.PPC64LE

open VG.Proof.P192.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p192Compress
    verified := Proof.EcKey.PPC64LE.Scrub.p192Compress_scrubbed },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p192Decompress
    verified := Proof.EcKey.PPC64LE.Scrub.p192Decompress_scrubbed hasLaw.law },
  Spec.EcKey.P192.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p192PublicKey
    verified := Proof.EcKey.PPC64LE.Scrub.p192PublicKey_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP192.PPC64LE
