module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P384Comb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.P384.Arm.Law

/-! # Deterministic ECDSA (RFC 6979) over P-384 on ARMv7, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaP384Rfc6979.Arm

open VG.Proof.P384.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT p384CombCurve p384T_verified p384CombCurveU p384UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (p384CombCurve hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p384.tries vars
    stack := stackT
    verified := p384T_verified hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (p384CombCurveU hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.p384.tries vars
    stack := stackT
    verified := p384UT_verified hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcdsaP384Rfc6979.Arm
