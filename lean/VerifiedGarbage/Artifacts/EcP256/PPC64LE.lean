module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.P256.PPC64LE.Law

/-! # P-256 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP256.PPC64LE

open VG.Proof.P256.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p256Compress
    verified := .scrubbed Proof.EcKey.PPC64LE.Scrub.p256Compress_scrubbed },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p256Decompress
    verified := .scrubbed (Proof.EcKey.PPC64LE.Scrub.p256Decompress_scrubbed hasLaw.law) },
  Spec.EcKey.P256.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p256PublicKey
    verified := .scrubbed (Proof.EcKey.PPC64LE.Scrub.p256PublicKey_scrubbed hasLaw.law) }]

end VG.Artifacts.EcP256.PPC64LE
