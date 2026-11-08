module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P256
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P256Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P256.Arm.Law

/-! # SEC 1 point conversion with P256's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP256.Arm

open VG.Proof.P256.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P256.code
    verified := Proof.EcKey.Compressed.Arm.P256.verified },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P256Decompress.code
    verified := Proof.EcKey.Compressed.Arm.P256Decompress.verified hasLaw.law },
  Spec.EcKey.P256.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P256.codeU
    verified := Proof.EcKey.Compressed.Arm.P256.verifiedU
    features := ["umaal"] },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P256Decompress.codeU
    verified := Proof.EcKey.Compressed.Arm.P256Decompress.verifiedU hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcCompressedP256.Arm
