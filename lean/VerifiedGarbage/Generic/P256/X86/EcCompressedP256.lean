module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P256
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P256Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with P256's existing field backend -/

@[expose] public section

namespace VG.Generic.P256.X86.EcCompressedP256

def artifacts (h : Proof.Weierstrass.X86.Inv.HasLawInvOrd Spec.P256.curve) : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P256.code
    verified := Proof.EcKey.Compressed.X86.P256.verified h.inv },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact X86.target {
    stack := 28
    code := Proof.EcKey.Compressed.X86.P256Decompress.code
    verified := Proof.EcKey.Compressed.X86.P256Decompress.verified h.law h.inv }]

end VG.Generic.P256.X86.EcCompressedP256
