module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P521
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P521Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P521.Arm.Law

/-! # SEC 1 point conversion with P521's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedP521.Arm

open VG.Proof.P521.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P521.code
    verified := Proof.EcKey.Compressed.Arm.P521.verified },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P521Decompress.code
    verified := Proof.EcKey.Compressed.Arm.P521Decompress.verified hasLaw.law }]

end VG.Artifacts.EcCompressedP521.Arm
