module

public import VerifiedGarbage.Impl.EcKey.Secp256k1.AArch64
public import VerifiedGarbage.Proof.EcKey.AArch64.Secp256k1.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Secp256k1
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Secp256k1Decompress
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Secp256k1.AArch64.Law
public import VerifiedGarbage.Spec.EcKey.Secp256k1
public import VerifiedGarbage.TCB.AArch64.Print

/-! # secp256k1 public keys (FIPS 186-5 §A.2) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcSecp256k1.AArch64

open VG.Proof.Secp256k1.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.compressSecp256k1
    verified := Proof.EcKey.Compressed.AArch64.Secp256k1.scrubbed hasLaw.inv },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.decompressSecp256k1
    verified := Proof.EcKey.Compressed.AArch64.Secp256k1Decompress.scrubbed hasLaw.law hasLaw.inv },
  Spec.EcKey.Secp256k1.publicKeyApi.artifact AArch64.target {
    code := Impl.EcKey.AArch64.Fn.publicKeySecp256k1
    verified := Proof.EcKey.AArch64.Secp256k1.pk_scrubbed hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcSecp256k1.AArch64
