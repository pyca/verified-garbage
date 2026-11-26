module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Spec.EcKey.Secp256k1
import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Secp256k1.PPC64LE.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on PPC64LE -/

namespace VG.Artifacts.EcSecp256k1.PPC64LE

open VG.Proof.Secp256k1.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.secp256k1Compress
    verified := Proof.EcKey.PPC64LE.Scrub.secp256k1Compress_scrubbed },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.secp256k1Decompress
    verified := Proof.EcKey.PPC64LE.Scrub.secp256k1Decompress_scrubbed hasLaw.law },
  Spec.EcKey.Secp256k1.publicKeyApi.artifact PPC64LE.target {
    code := Impl.EcKey.PPC64LE.Fn.secp256k1PublicKey
    verified := Proof.EcKey.PPC64LE.Scrub.secp256k1PublicKey_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcSecp256k1.PPC64LE
