module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P384Comb
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-384 on ARMv7, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P384.Arm.EcdsaP384Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT p384CombCurve p384T_verified p384CombCurveU p384UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (p384CombCurve h.law) Spec.Ecdsa.Rfc6979.Curves.p384.tries vars
    consts := Impl.Weierstrass.Arm.p384CombConsts
    stack := stackT
    verified := p384T_verified h.law },
  Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (p384CombCurveU h.law) Spec.Ecdsa.Rfc6979.Curves.p384.tries vars
    consts := Impl.Weierstrass.Arm.p384CombConsts
    stack := stackT
    verified := p384UT_verified h.law
    features := ["umaal"] }]

end VG.Generic.P384.Arm.EcdsaP384Rfc6979
