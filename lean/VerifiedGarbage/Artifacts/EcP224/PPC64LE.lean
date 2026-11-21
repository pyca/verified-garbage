module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.P224.PPC64LE.Law

/-! # P-224 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcP224.PPC64LE

open VG.Proof.P224.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p224Compress
    verified := Proof.EcKey.PPC64LE.Scrub.p224Compress_scrubbed },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p224Decompress
    verified := Proof.EcKey.PPC64LE.Scrub.p224Decompress_scrubbed hasLaw.law },
  Spec.EcKey.P224.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.p224PublicKey
    verified := Proof.EcKey.PPC64LE.Scrub.p224PublicKey_scrubbed hasLaw.law }]

end VG.Artifacts.EcP224.PPC64LE
