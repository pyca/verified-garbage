module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P224Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with P224's existing field backend -/

@[expose] public section

namespace VG.Generic.P224.X86.EcCompressedP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P224.code
    verified := Proof.EcKey.Compressed.X86.P224.verified },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P224Decompress.code
    verified := Proof.EcKey.Compressed.X86.P224Decompress.verified h.law }]

end VG.Generic.P224.X86.EcCompressedP224
