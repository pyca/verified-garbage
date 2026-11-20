module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.BrainpoolP384r1.PPC64LE.Law

/-! # brainpoolP384r1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcBrainpoolP384r1.PPC64LE

open VG.Proof.BrainpoolP384r1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.brainpoolp384r1PublicKey
    verified := .scrubbed (Proof.EcKey.PPC64LE.Scrub.brainpoolp384r1PublicKey_scrubbed hasLaw.law) },
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.brainpoolp384r1Compress
    verified := .scrubbed Proof.EcKey.PPC64LE.Scrub.brainpoolp384r1Compress_scrubbed },
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.brainpoolp384r1Decompress
    verified := .scrubbed (Proof.EcKey.PPC64LE.Scrub.brainpoolp384r1Decompress_scrubbed hasLaw.law) }]

end VG.Artifacts.EcBrainpoolP384r1.PPC64LE
