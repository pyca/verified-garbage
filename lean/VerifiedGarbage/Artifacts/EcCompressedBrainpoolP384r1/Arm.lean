module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP384r1
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP384r1Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP384r1.Arm.Law

/-! # SEC 1 point conversion with BrainpoolP384r1's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedBrainpoolP384r1.Arm

open VG.Proof.BrainpoolP384r1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.BrainpoolP384r1.code
    verified := Proof.EcKey.Compressed.Arm.BrainpoolP384r1.verified },
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.BrainpoolP384r1Decompress.code
    verified := Proof.EcKey.Compressed.Arm.BrainpoolP384r1Decompress.verified hasLaw.law },
  Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.BrainpoolP384r1.codeU
    verified := Proof.EcKey.Compressed.Arm.BrainpoolP384r1.verifiedU
    features := ["umaal"] },
  Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.BrainpoolP384r1Decompress.codeU
    verified := Proof.EcKey.Compressed.Arm.BrainpoolP384r1Decompress.verifiedU hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcCompressedBrainpoolP384r1.Arm
