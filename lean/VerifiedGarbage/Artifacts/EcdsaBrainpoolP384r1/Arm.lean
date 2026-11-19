module

public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP384r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.Scrub
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP384r1.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP384r1Comb

/-! # ECDSA over brainpoolP384r1 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP384r1.Arm

open VG.Proof.BrainpoolP384r1.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT brainpoolp384r1CombCurve brainpoolp384r1T_verified brainpoolp384r1CombCurveU brainpoolp384r1UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP384r1.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.BrainpoolP384r1.Scrub.verifyReg hasLaw.law),
  Spec.Ecdsa.BrainpoolP384r1.verifyHashApi.artifact Arm.target (Proof.Ecdsa.Arm.BrainpoolP384r1.Scrub.verifyUReg hasLaw.law),
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (brainpoolp384r1CombCurve hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vars
    verified := .unscrubbed (brainpoolp384r1T_verified hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (brainpoolp384r1CombCurveU hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vars
    verified := .unscrubbed (brainpoolp384r1UT_verified hasLaw.law) }]

end VG.Artifacts.EcdsaBrainpoolP384r1.Arm
