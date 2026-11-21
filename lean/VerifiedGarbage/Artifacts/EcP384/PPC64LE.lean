module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.P384.PPC64LE.Law

/-! # P-384 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP384.PPC64LE

open VG.Proof.P384.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p384Compress
    verified := .scrubbed Proof.EcKey.PPC64LE.Scrub.p384Compress_scrubbed },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p384Decompress
    verified := .scrubbed (Proof.EcKey.PPC64LE.Scrub.p384Decompress_scrubbed hasLaw.law) },
  Spec.EcKey.P384.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p384PublicKey
    verified := .scrubbed (Proof.EcKey.PPC64LE.Scrub.p384PublicKey_scrubbed hasLaw.law) }]

end VG.Artifacts.EcP384.PPC64LE
