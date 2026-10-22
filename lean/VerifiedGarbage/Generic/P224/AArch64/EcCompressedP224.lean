module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P224Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with P224's existing field backend -/

@[expose] public section

namespace VG.Generic.P224.AArch64.EcCompressedP224

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve) : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P224.code
    verified := Proof.EcKey.Compressed.AArch64.P224.verified h.inv },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P224Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.P224Decompress.verified h.law h.inv }]

end VG.Generic.P224.AArch64.EcCompressedP224
