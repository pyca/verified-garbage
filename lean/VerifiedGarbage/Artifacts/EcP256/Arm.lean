module

public import VerifiedGarbage.Proof.EcKey.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P256.Arm.Law
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P256
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P256Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # P-256 public keys (FIPS 186-5 §A.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcP256.Arm

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
    verified := Proof.EcKey.Compressed.Arm.P256.verifiedU },
  Spec.EcKey.P256.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P256Decompress.codeU
    verified := Proof.EcKey.Compressed.Arm.P256Decompress.verifiedU hasLaw.law },
  Spec.EcKey.P256.publicKeyApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.publicKeyP256Comb
    verified := Proof.EcKey.Arm.P256.combPk_verified hasLaw.law },
  Spec.EcKey.P256.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.publicKeyP256CombU
    verified := Proof.EcKey.Arm.P256.combPkU_verified hasLaw.law }]

end VG.Artifacts.EcP256.Arm
