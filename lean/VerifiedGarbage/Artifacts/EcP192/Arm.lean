module

public import VerifiedGarbage.Proof.EcKey.Arm.P192.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P192.Arm.Law
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P192
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P192Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # P-192 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP192.Arm

open VG.Proof.P192.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P192.publicKeyApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.publicKeyP192Comb
    verified := .unscrubbed (Proof.EcKey.Arm.P192.combPk_verified hasLaw.law) },
  Spec.EcKey.P192.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.publicKeyP192CombU
    verified := .unscrubbed (Proof.EcKey.Arm.P192.combPkU_verified hasLaw.law) },
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P192.code
    verified := .unscrubbed Proof.EcKey.Compressed.Arm.P192.verified },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P192Decompress.code
    verified := .unscrubbed (Proof.EcKey.Compressed.Arm.P192Decompress.verified hasLaw.law) },
  Spec.EcKey.P192.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P192.codeU
    verified := .unscrubbed Proof.EcKey.Compressed.Arm.P192.verifiedU },
  Spec.EcKey.P192.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P192Decompress.codeU
    verified := .unscrubbed (Proof.EcKey.Compressed.Arm.P192Decompress.verifiedU hasLaw.law) }]

end VG.Artifacts.EcP192.Arm
