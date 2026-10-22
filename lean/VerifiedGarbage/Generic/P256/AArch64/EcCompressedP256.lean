module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P256
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P256Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with P256's existing field backend -/

@[expose] public section

namespace VG.Generic.P256.AArch64.EcCompressedP256

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvToMOrd Spec.P256.curve) : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P256.code
    verified := Proof.EcKey.Compressed.AArch64.P256.verified h.inv },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P256Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.P256Decompress.verified h.law h.inv }]

end VG.Generic.P256.AArch64.EcCompressedP256
