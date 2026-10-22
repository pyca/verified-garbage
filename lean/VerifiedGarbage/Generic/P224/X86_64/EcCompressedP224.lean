module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P224Decompress
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Standalone P224 public-point compression on x86-64 -/

@[expose] public section

namespace VG.Generic.P224.X86_64.EcCompressedP224

open VG.Proof.EcKey.Compressed.X86_64.P224

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) : List Artifact :=
  [Spec.EcKey.P224.inst.compressPublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified h.inv false
    stack := 8 },
    Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact X86_64.target {
      code := Proof.EcKey.Compressed.X86_64.P224Decompress.code false
      verified := Proof.EcKey.Compressed.X86_64.P224Decompress.verified h.law h.inv false
      stack := 8 }]

end VG.Generic.P224.X86_64.EcCompressedP224
