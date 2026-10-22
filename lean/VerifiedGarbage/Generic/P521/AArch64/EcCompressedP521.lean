module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P521
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P521Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with P521's existing field backend -/

@[expose] public section

namespace VG.Generic.P521.AArch64.EcCompressedP521

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P521.curve) : List Artifact := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P521.code
    verified := Proof.EcKey.Compressed.AArch64.P521.verified h.inv },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P521Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.P521Decompress.verified h.law h.inv }]

end VG.Generic.P521.AArch64.EcCompressedP521
