module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Secp256k1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Secp256k1Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with Secp256k1's existing field backend -/

@[expose] public section

namespace VG.Generic.Secp256k1.X86.EcCompressedSecp256k1

def artifacts (h : Proof.Weierstrass.X86.Inv.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.Secp256k1.code
    verified := Proof.EcKey.Compressed.X86.Secp256k1.verified h.inv },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.Secp256k1Decompress.code
    verified := Proof.EcKey.Compressed.X86.Secp256k1Decompress.verified h.law h.inv }]

end VG.Generic.Secp256k1.X86.EcCompressedSecp256k1
