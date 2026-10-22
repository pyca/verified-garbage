module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P192
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.P192Decompress
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Standalone P192 public-point compression on x86-64 -/

@[expose] public section

namespace VG.Generic.P192.X86_64.EcCompressedP192

open VG.Proof.EcKey.Compressed.X86_64.P192

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P192.curve) : List Artifact :=
  [Spec.EcKey.P192.inst.compressPublicKeyApi.artifact X86_64.target {
    code := code false
    verified := verified h.inv false
    stack := 8 },
    Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact X86_64.target {
      code := Proof.EcKey.Compressed.X86_64.P192Decompress.code false
      verified := Proof.EcKey.Compressed.X86_64.P192Decompress.verified h.law h.inv false
      stack := 8 }]

end VG.Generic.P192.X86_64.EcCompressedP192
