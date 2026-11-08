module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Secp256k1
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Secp256k1Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Secp256k1.AArch64.Law

/-! # SEC 1 point conversion with Secp256k1's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedSecp256k1.AArch64

open VG.Proof.Secp256k1.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.Secp256k1.code
    verified := Proof.EcKey.Compressed.AArch64.Secp256k1.verified hasLaw.inv },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.Secp256k1Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.Secp256k1Decompress.verified hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcCompressedSecp256k1.AArch64
