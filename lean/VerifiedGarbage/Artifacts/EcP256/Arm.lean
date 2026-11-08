module

public import VerifiedGarbage.Proof.EcKey.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P256.Arm.Law

/-! # P-256 public keys (FIPS 186-5 §A.2) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.EcP256.Arm

open VG.Proof.P256.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P256.publicKeyApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.publicKeyP256Comb
    verified := Proof.EcKey.Arm.P256.combPk_verified hasLaw.law },
  Spec.EcKey.P256.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.publicKeyP256CombU
    verified := Proof.EcKey.Arm.P256.combPkU_verified hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcP256.Arm
