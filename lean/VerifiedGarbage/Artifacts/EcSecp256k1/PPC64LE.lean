module

public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Secp256k1.PPC64LE.Law

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcSecp256k1.PPC64LE

open VG.Proof.Secp256k1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.secp256k1Compress
    verified := Proof.EcKey.PPC64LE.Scrub.secp256k1Compress_scrubbed },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.secp256k1Decompress
    verified := Proof.EcKey.PPC64LE.Scrub.secp256k1Decompress_scrubbed hasLaw.law },
  Spec.EcKey.Secp256k1.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.secp256k1PublicKey
    verified := Proof.EcKey.PPC64LE.Scrub.secp256k1PublicKey_scrubbed hasLaw.law }]

end VG.Artifacts.EcSecp256k1.PPC64LE
