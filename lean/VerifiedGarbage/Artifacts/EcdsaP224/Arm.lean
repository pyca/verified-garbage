module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P224.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P224.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P224Comb

/-! # ECDSA over P-224 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaP224.Arm

open VG.Proof.P224.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT p224CombCurve p224T_verified p224CombCurveU p224UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

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
    verified := Proof.Ecdsa.Verify.Arm.P224.verifyHashU_verified hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (p224CombCurve hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p224.tries vars
    stack := stackT
    verified := p224T_verified hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (p224CombCurveU hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p224.tries vars
    stack := stackT
    verified := p224UT_verified hasLaw.law }]

end VG.Artifacts.EcdsaP224.Arm
