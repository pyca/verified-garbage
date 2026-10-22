module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P384
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P384Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with P384's existing field backend -/

@[expose] public section

namespace VG.Generic.P384.X86.EcCompressedP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P384.code
    verified := Proof.EcKey.Compressed.X86.P384.verified },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P384Decompress.code
    verified := Proof.EcKey.Compressed.X86.P384Decompress.verified h.law }]

end VG.Generic.P384.X86.EcCompressedP384
