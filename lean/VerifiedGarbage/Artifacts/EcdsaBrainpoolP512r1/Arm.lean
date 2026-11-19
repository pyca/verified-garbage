module

public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP512r1
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP512r1.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP512r1Comb

/-! # ECDSA over brainpoolP512r1 (FIPS 186-5) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP512r1.Arm

open VG.Proof.BrainpoolP512r1.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT brainpoolp512r1CombCurve brainpoolp512r1T_verified brainpoolp512r1CombCurveU brainpoolp512r1UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP512r1.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false
      Impl.Ecdsa.Arm.verifyBrainpoolP512r1Comb
    verified := .unscrubbed (Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.verifyHash_verified hasLaw.law) },
  Spec.Ecdsa.BrainpoolP512r1.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false
      Impl.Ecdsa.Arm.verifyBrainpoolP512r1CombU
    verified := .unscrubbed (Proof.Ecdsa.Verify.Arm.BrainpoolP512r1.verifyHashU_verified hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (brainpoolp512r1CombCurve hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vars
    verified := .unscrubbed (brainpoolp512r1T_verified hasLaw.law) },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (brainpoolp512r1CombCurveU hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vars
    verified := .unscrubbed (brainpoolp512r1UT_verified hasLaw.law) }]

end VG.Artifacts.EcdsaBrainpoolP512r1.Arm
