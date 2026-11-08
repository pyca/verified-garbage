module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P224.Arm.Law

/-! # SEC 1 point conversion with P224's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP224.Arm

open VG.Proof.P224.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P224.code
    verified := Proof.EcKey.Compressed.Arm.P224.verified },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P224Decompress.code
    verified := Proof.EcKey.Compressed.Arm.P224Decompress.verified hasLaw.law },
  Spec.EcKey.P224.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P224.codeU
    verified := Proof.EcKey.Compressed.Arm.P224.verifiedU
    features := ["umaal"] },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P224Decompress.codeU
    verified := Proof.EcKey.Compressed.Arm.P224Decompress.verifiedU hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcCompressedP224.Arm
