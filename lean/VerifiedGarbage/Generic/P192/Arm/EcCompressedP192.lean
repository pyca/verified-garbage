module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P192
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P192Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with P192's existing field backend -/

@[expose] public section

namespace VG.Generic.P192.Arm.EcCompressedP192

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P192.code
    verified := Proof.EcKey.Compressed.Arm.P192.verified },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P192Decompress.code
    verified := Proof.EcKey.Compressed.Arm.P192Decompress.verified h.law }]

end VG.Generic.P192.Arm.EcCompressedP192
