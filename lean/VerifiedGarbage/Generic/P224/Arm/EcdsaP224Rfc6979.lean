module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P224Comb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Deterministic ECDSA (RFC 6979) over P-224 on ARMv7, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P224.Arm.EcdsaP224Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT p224CombCurve p224T_verified p224CombCurveU p224UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (p224CombCurve h.law) Spec.Ecdsa.Rfc6979.Curves.p224.tries vars
    stack := stackT
    verified := p224T_verified h.law },
  Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (p224CombCurveU h.law) Spec.Ecdsa.Rfc6979.Curves.p224.tries vars
    stack := stackT
    verified := p224UT_verified h.law
    features := ["umaal"] }]

end VG.Generic.P224.Arm.EcdsaP224Rfc6979
