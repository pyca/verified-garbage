module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P192
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P192Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with P192's existing field backend -/

@[expose] public section

namespace VG.Generic.P192.AArch64.EcCompressedP192

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P192.curve) : List Artifact := [
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P192.code
    verified := Proof.EcKey.Compressed.AArch64.P192.verified h.inv },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P192Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.P192Decompress.verified h.law h.inv }]

end VG.Generic.P192.AArch64.EcCompressedP192
