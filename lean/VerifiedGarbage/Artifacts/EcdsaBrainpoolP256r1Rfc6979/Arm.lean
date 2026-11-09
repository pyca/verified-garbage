module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP256r1Comb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.Law

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on ARMv7, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaBrainpoolP256r1Rfc6979.Arm

open VG.Proof.BrainpoolP256r1.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT brainpoolp256r1CombCurve brainpoolp256r1T_verified brainpoolp256r1CombCurveU brainpoolp256r1UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts : List Artifact := [
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

end VG.Artifacts.EcdsaBrainpoolP256r1Rfc6979.Arm
