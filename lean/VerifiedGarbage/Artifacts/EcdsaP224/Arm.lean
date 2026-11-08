module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P224.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P224.Arm.Law

/-! # ECDSA over P-224 (FIPS 186-5) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.EcdsaP224.Arm

open VG.Proof.P224.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P224.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP224Comb
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.P224.verifyHash_verified hasLaw.law },
  Spec.Ecdsa.P224.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP224CombU
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.P224.verifyHashU_verified hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcdsaP224.Arm
