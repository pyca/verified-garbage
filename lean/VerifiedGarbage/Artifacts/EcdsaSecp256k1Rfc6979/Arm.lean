module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Secp256k1Comb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Secp256k1.Arm.Law

/-! # Deterministic ECDSA (RFC 6979) over secp256k1 on ARMv7, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaSecp256k1Rfc6979.Arm

open VG.Proof.Secp256k1.Arm (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT secp256k1CombCurve secp256k1T_verified secp256k1CombCurveU secp256k1UT_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (secp256k1CombCurve hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vars
    stack := stackT
    verified := secp256k1T_verified hasLaw.law },
  Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact Arm.target {
    suffix := "_umaal"
    tables := [("hmac", tables vars)]
    code := signCodeT (secp256k1CombCurveU hasLaw.law) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vars
    stack := stackT
    verified := secp256k1UT_verified hasLaw.law
    features := ["umaal"] }]

end VG.Artifacts.EcdsaSecp256k1Rfc6979.Arm
