module

public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP256r1.Comb -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP256r1Comb

/-! # ECDSA over brainpoolP256r1 (FIPS 186-5) on 32-bit ARM -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP256r1.Arm

open VG.Proof.BrainpoolP256r1.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT brainpoolp256r1CombCurve brainpoolp256r1T_verified brainpoolp256r1CombCurveU brainpoolp256r1UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts : List Artifact := [
  Spec.Ecdsa.BrainpoolP256r1.verifyHashApi.artifact Arm.target {
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP256r1.inst.curve.len false
      Impl.Ecdsa.Arm.verifyBrainpoolP256r1Comb
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.BrainpoolP256r1.verifyHash_verified hasLaw.law },
  Spec.Ecdsa.BrainpoolP256r1.verifyHashApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP256r1.inst.curve.len false
      Impl.Ecdsa.Arm.verifyBrainpoolP256r1CombU
    stack := 96
    verified := Proof.Ecdsa.Verify.Arm.BrainpoolP256r1.verifyHashU_verified hasLaw.law
    features := ["umaal"] },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (brainpoolp256r1CombCurve hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vars
    stack := stackT
    verified := brainpoolp256r1T_verified hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (brainpoolp256r1CombCurveU hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vars
    stack := stackT
    verified := brainpoolp256r1UT_verified hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcdsaBrainpoolP256r1.Arm
