module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P384
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.P384Decompress
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with P384's existing field backend -/

@[expose] public section

namespace VG.Generic.P384.AArch64.EcCompressedP384

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P384.curve) : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P384.code
    verified := Proof.EcKey.Compressed.AArch64.P384.verified h.inv },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact AArch64.target {
    code := Proof.EcKey.Compressed.AArch64.P384Decompress.code
    verified := Proof.EcKey.Compressed.AArch64.P384Decompress.verified h.law h.inv }]

end VG.Generic.P384.AArch64.EcCompressedP384
