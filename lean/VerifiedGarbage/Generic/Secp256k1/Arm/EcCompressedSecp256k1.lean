module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Secp256k1
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Secp256k1Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with Secp256k1's existing field backend -/

@[expose] public section

namespace VG.Generic.Secp256k1.Arm.EcCompressedSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.Secp256k1.code
    verified := Proof.EcKey.Compressed.Arm.Secp256k1.verified },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.Secp256k1Decompress.code
    verified := Proof.EcKey.Compressed.Arm.Secp256k1Decompress.verified h.law }]

end VG.Generic.Secp256k1.Arm.EcCompressedSecp256k1
