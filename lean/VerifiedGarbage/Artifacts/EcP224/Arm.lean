module

public import VerifiedGarbage.Proof.EcKey.Arm.P224.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P224.Arm.Law
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # P-224 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP224.Arm

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
    verified := Proof.EcKey.Compressed.Arm.P224.verifiedU },
  Spec.EcKey.P224.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P224Decompress.codeU
    verified := Proof.EcKey.Compressed.Arm.P224Decompress.verifiedU hasLaw.law },
  Spec.EcKey.P224.publicKeyApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.publicKeyP224Comb
    verified := Proof.EcKey.Arm.P224.combPk_verified hasLaw.law },
  Spec.EcKey.P224.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.publicKeyP224CombU
    verified := Proof.EcKey.Arm.P224.combPkU_verified hasLaw.law }]

end VG.Artifacts.EcP224.Arm
