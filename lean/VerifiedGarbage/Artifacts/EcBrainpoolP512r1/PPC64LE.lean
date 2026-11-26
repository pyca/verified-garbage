module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.BrainpoolP512r1.PPC64LE.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # brainpoolP512r1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

namespace VG.Artifacts.EcBrainpoolP512r1.PPC64LE

open VG.Proof.BrainpoolP512r1.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.EcKey.BrainpoolP512r1.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.brainpoolp512r1PublicKey
    verified := Proof.EcKey.PPC64LE.Scrub.brainpoolp512r1PublicKey_scrubbed hasLaw.law },
  Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.brainpoolp512r1Compress
    verified := Proof.EcKey.PPC64LE.Scrub.brainpoolp512r1Compress_scrubbed },
  Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.brainpoolp512r1Decompress
    verified := Proof.EcKey.PPC64LE.Scrub.brainpoolp512r1Decompress_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcBrainpoolP512r1.PPC64LE
