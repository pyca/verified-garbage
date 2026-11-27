module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P224.PPC64LE.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # P-224 public keys (FIPS 186-5 §A.2) on PPC64LE -/

namespace VG.Artifacts.EcP224.PPC64LE

open VG.Proof.P224.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p224Compress
    verified := Proof.EcKey.PPC64LE.Scrub.p224Compress_scrubbed },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p224Decompress
    verified := Proof.EcKey.PPC64LE.Scrub.p224Decompress_scrubbed hasLaw.law },
  Spec.EcKey.P224.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p224PublicKey
    verified := Proof.EcKey.PPC64LE.Scrub.p224PublicKey_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcP224.PPC64LE
