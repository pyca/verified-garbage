module

public import VerifiedGarbage.Proof.EcKey.Arm.P224.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P224.Arm.Law

/-! # P-224 public keys (FIPS 186-5 §A.2) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.EcP224.Arm

open VG.Proof.P224.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.EcKey.P224.publicKeyApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.publicKeyP224Comb
    verified := Proof.EcKey.Arm.P224.combPk_verified hasLaw.law },
  Spec.EcKey.P224.publicKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.publicKeyP224CombU
    verified := Proof.EcKey.Arm.P224.combPkU_verified hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcP224.Arm
