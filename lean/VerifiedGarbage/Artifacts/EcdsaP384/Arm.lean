module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P384.Arm.Law

/-! # ECDSA over P-384 (FIPS 186-5) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.EcdsaP384.Arm

open VG.Proof.P384.Arm (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdsa.P384.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP384Comb
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.P384.verifyHash_verified hasLaw.law },
  Spec.Ecdsa.P384.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP384CombU
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.P384.verifyHashU_verified hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcdsaP384.Arm
