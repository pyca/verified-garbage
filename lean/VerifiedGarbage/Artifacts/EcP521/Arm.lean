module

public import VerifiedGarbage.Proof.EcKey.Arm.P521.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P521.Arm.Law
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P521
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P521Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # P-521 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP521.Arm

open VG.Proof.P521.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P521.code
    verified := Proof.EcKey.Compressed.Arm.P521.verified },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P521Decompress.code
    verified := Proof.EcKey.Compressed.Arm.P521Decompress.verified hasLaw.law },
  Spec.EcKey.P521.publicKeyApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.publicKeyP521Comb
    verified := Proof.EcKey.Arm.P521.combPk_verified hasLaw.law },
  Spec.EcKey.P521.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P521.codeU
    verified := Proof.EcKey.Compressed.Arm.P521.verifiedU },
  Spec.EcKey.P521.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P521Decompress.codeU
    verified := Proof.EcKey.Compressed.Arm.P521Decompress.verifiedU hasLaw.law },
  Spec.EcKey.P521.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.publicKeyP521CombU
    verified := Proof.EcKey.Arm.P521.combPkU_verified hasLaw.law }]

end VG.Artifacts.EcP521.Arm
