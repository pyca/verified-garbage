module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P224.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print

/-! # ECDSA over P-224 (FIPS 186-5) on 32-bit ARM -/

@[expose] public section

namespace VG.Generic.P224.Arm.EcdsaP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Ecdsa.P224.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP224Comb
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.P224.verifyHash_verified h.law },
  Spec.Ecdsa.P224.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false
      Impl.Ecdsa.Arm.verifyP224CombU
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.P224.verifyHashU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P224.Arm.EcdsaP224
