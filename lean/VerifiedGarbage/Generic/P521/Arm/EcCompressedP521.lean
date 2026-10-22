module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P521
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P521Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with P521's existing field backend -/

@[expose] public section

namespace VG.Generic.P521.Arm.EcCompressedP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P521.code
    verified := Proof.EcKey.Compressed.Arm.P521.verified },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P521Decompress.code
    verified := Proof.EcKey.Compressed.Arm.P521Decompress.verified h.law }]

end VG.Generic.P521.Arm.EcCompressedP521
