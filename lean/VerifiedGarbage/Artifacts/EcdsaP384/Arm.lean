module

public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P384.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P384.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P384Comb

/-! # ECDSA over P-384 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaP384.Arm

open VG.Proof.P384.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT p384CombCurve p384T_verified p384CombCurveU p384UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts : List Artifact := [
  Spec.Ecdsa.P384.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.P384.Scrub.verifyReg hasLaw.law),
  Spec.Ecdsa.P384.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.P384.Scrub.verifyUReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (p384CombCurve hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p384.tries vars
    verified := .unscrubbed (p384T_verified hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (p384CombCurveU hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p384.tries vars
    verified := .unscrubbed (p384UT_verified hasLaw.law) }]

end VG.Artifacts.EcdsaP384.Arm
