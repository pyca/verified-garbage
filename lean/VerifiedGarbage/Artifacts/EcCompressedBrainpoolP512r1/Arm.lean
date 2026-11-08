module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP512r1
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP512r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP512r1.Arm.Law

/-! # SEC 1 point conversion with BrainpoolP512r1's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedBrainpoolP512r1.Arm

open VG.Proof.BrainpoolP512r1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.BrainpoolP512r1.code
    verified := Proof.EcKey.Compressed.Arm.BrainpoolP512r1.verified },
  Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.BrainpoolP512r1Decompress.code
    verified := Proof.EcKey.Compressed.Arm.BrainpoolP512r1Decompress.verified hasLaw.law },
  Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.BrainpoolP512r1.codeU
    verified := Proof.EcKey.Compressed.Arm.BrainpoolP512r1.verifiedU
    features := ["umaal"] },
  Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.BrainpoolP512r1Decompress.codeU
    verified := Proof.EcKey.Compressed.Arm.BrainpoolP512r1Decompress.verifiedU hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcCompressedBrainpoolP512r1.Arm
