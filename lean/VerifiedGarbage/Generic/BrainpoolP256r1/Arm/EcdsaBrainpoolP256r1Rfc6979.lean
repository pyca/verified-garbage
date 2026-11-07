module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP256r1Comb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on ARMv7, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.Arm.EcdsaBrainpoolP256r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT brainpoolp256r1CombCurve brainpoolp256r1T_verified brainpoolp256r1CombCurveU brainpoolp256r1UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (brainpoolp256r1CombCurve h.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vars
    stack := stackT
    verified := brainpoolp256r1T_verified h.law },
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (brainpoolp256r1CombCurveU h.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vars
    stack := stackT
    verified := brainpoolp256r1UT_verified h.law
    features := ["umaal"] }]

end VG.Generic.BrainpoolP256r1.Arm.EcdsaBrainpoolP256r1Rfc6979
