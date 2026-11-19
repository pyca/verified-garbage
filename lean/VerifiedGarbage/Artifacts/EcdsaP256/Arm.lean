module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P256.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P256.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P256Comb

/-! # ECDSA over P-256 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaP256.Arm

open VG.Proof.P256.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT p256CombCurve p256T_verified p256CombCurveU p256UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts : List Artifact := [
  Spec.Ecdsa.P256.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.P256.Scrub.verifyReg hasLaw.law),
  Spec.Ecdsa.P256.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.P256.Scrub.verifyUReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (p256CombCurve hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p256.tries vars
    verified := .unscrubbed (p256T_verified hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (p256CombCurveU hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p256.tries vars
    verified := .unscrubbed (p256UT_verified hasLaw.law) }]

end VG.Artifacts.EcdsaP256.Arm
