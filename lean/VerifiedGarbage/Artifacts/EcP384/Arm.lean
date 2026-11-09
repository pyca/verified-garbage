module

public import VerifiedGarbage.Proof.EcKey.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P384.Arm.Law
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P384
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P384Decompress
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! # P-384 public keys (FIPS 186-5 §A.2) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.EcP384.Arm

open VG.Proof.P384.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P384.code
    verified := Proof.EcKey.Compressed.Arm.P384.verified },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact Arm.target {
    code := Proof.EcKey.Compressed.Arm.P384Decompress.code
    verified := Proof.EcKey.Compressed.Arm.P384Decompress.verified hasLaw.law },
  Spec.EcKey.P384.inst.compressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P384.codeU
    verified := Proof.EcKey.Compressed.Arm.P384.verifiedU },
  Spec.EcKey.P384.inst.decompressPublicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Proof.EcKey.Compressed.Arm.P384Decompress.codeU
    verified := Proof.EcKey.Compressed.Arm.P384Decompress.verifiedU hasLaw.law },
  Spec.EcKey.P384.publicKeyApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.publicKeyP384Comb
    verified := Proof.EcKey.Arm.P384.combPk_verified hasLaw.law },
  Spec.EcKey.P384.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.publicKeyP384CombU
    verified := Proof.EcKey.Arm.P384.combPkU_verified hasLaw.law }]

end VG.Artifacts.EcP384.Arm
