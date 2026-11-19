module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P521.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P521.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P521Comb

/-! # ECDSA over P-521 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaP521.Arm

open VG.Proof.P521.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT p521CombCurve p521T_verified p521CombCurveU p521UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts : List Artifact := [
  Spec.Ecdsa.P521.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
      Impl.Ecdsa.Arm.verifyP521Comb
    verified := .unscrubbed (Proof.Ecdsa.Verify.Arm.P521.verifyHash_verified hasLaw.law) },
  Spec.Ecdsa.P521.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
      Impl.Ecdsa.Arm.verifyP521CombU
    verified := .unscrubbed (Proof.Ecdsa.Verify.Arm.P521.verifyHashU_verified hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (p521CombCurve hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p521.tries vars
    verified := .unscrubbed (p521T_verified hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (p521CombCurveU hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p521.tries vars
    verified := .unscrubbed (p521UT_verified hasLaw.law) }]

end VG.Artifacts.EcdsaP521.Arm
