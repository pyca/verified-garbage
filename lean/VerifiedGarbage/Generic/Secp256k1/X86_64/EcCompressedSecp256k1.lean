module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Secp256k1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Secp256k1Decompress
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Standalone Secp256k1 public-point compression on x86-64 -/

@[expose] public section

namespace VG.Generic.Secp256k1.X86_64.EcCompressedSecp256k1

open VG.Proof.EcKey.Compressed.X86_64.Secp256k1

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.Secp256k1.curve) : List Artifact :=
  [Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified h.inv false
    stack := 8 },
    Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact X86_64.target {
      code := Proof.EcKey.Compressed.X86_64.Secp256k1Decompress.code false
      verified := Proof.EcKey.Compressed.X86_64.Secp256k1Decompress.verified h.law h.inv false
      stack := 8 }]

end VG.Generic.Secp256k1.X86_64.EcCompressedSecp256k1
