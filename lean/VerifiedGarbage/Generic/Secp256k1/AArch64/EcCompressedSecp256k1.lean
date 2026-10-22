module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Secp256k1
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Secp256k1Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with Secp256k1's existing field backend -/

@[expose] public section

namespace VG.Generic.Secp256k1.AArch64.EcCompressedSecp256k1

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.Secp256k1.code
    verified := Proof.EcKey.Compressed.AArch64.Secp256k1.verified h.inv },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.Secp256k1Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.Secp256k1Decompress.verified h.law h.inv }]

end VG.Generic.Secp256k1.AArch64.EcCompressedSecp256k1
