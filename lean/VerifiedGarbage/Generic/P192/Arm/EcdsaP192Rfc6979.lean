module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P192
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Deterministic ECDSA (RFC 6979) over P-192 on ARMv7, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P192.Arm.EcdsaP192Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT p192 p192T_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (p192 h.law) Spec.Ecdsa.Rfc6979.Curves.p192.tries vars
    stack := stackT
    verified := p192T_verified h.law }]

end VG.Generic.P192.Arm.EcdsaP192Rfc6979
