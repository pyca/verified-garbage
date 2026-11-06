module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P256Comb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Deterministic ECDSA (RFC 6979) over P-256 on ARMv7, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P256.Arm.EcdsaP256Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT p256CombCurve p256T_verified p256CombCurveU p256UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (p256CombCurve h.law) Spec.Ecdsa.Rfc6979.Curves.p256.tries vars
    stack := stackT
    verified := p256T_verified h.law },
  Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (p256CombCurveU h.law) Spec.Ecdsa.Rfc6979.Curves.p256.tries vars
    stack := stackT
    verified := p256UT_verified h.law
    features := ["umaal"] }]

end VG.Generic.P256.Arm.EcdsaP256Rfc6979
