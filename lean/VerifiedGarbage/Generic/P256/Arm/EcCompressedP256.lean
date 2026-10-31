module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P256
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P256Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration

/-! # SEC 1 point conversion with P256's existing field backend -/

@[expose] public section

namespace VG.Generic.P256.Arm.EcCompressedP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P256.code
    verified := Proof.EcKey.Compressed.Arm.P256.verified },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P256Decompress.code
    verified := Proof.EcKey.Compressed.Arm.P256Decompress.verified h.law },
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P256.codeU
    verified := Proof.EcKey.Compressed.Arm.P256.verifiedU
    features := ["umaal"] },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P256Decompress.codeU
    verified := Proof.EcKey.Compressed.Arm.P256Decompress.verifiedU h.law
    features := ["umaal"] }]

end VG.Generic.P256.Arm.EcCompressedP256
