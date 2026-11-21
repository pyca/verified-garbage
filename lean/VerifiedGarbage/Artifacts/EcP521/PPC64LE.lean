module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.P521.PPC64LE.Law

/-! # P-521 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP521.PPC64LE

open VG.Proof.P521.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p521Compress
    verified := .scrubbed Proof.EcKey.PPC64LE.Scrub.p521Compress_scrubbed },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p521Decompress
    verified := .scrubbed (Proof.EcKey.PPC64LE.Scrub.p521Decompress_scrubbed hasLaw.law) },
  Spec.EcKey.P521.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p521PublicKey
    verified := .scrubbed (Proof.EcKey.PPC64LE.Scrub.p521PublicKey_scrubbed hasLaw.law) }]

end VG.Artifacts.EcP521.PPC64LE
