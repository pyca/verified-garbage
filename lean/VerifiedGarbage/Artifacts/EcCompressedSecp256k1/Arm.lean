module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Secp256k1
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Secp256k1Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Secp256k1.Arm.Law

/-! # SEC 1 point conversion with Secp256k1's existing field backend -/

@[expose] public section

namespace VG.Artifacts.EcCompressedSecp256k1.Arm

open VG.Proof.Secp256k1.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.Secp256k1.code
    verified := Proof.EcKey.Compressed.Arm.Secp256k1.verified },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.Secp256k1Decompress.code
    verified := Proof.EcKey.Compressed.Arm.Secp256k1Decompress.verified hasLaw.law },
  Spec.EcKey.Secp256k1.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.Secp256k1.codeU
    verified := Proof.EcKey.Compressed.Arm.Secp256k1.verifiedU
    features := ["umaal"] },
  Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.Secp256k1Decompress.codeU
    verified := Proof.EcKey.Compressed.Arm.Secp256k1Decompress.verifiedU hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcCompressedSecp256k1.Arm
