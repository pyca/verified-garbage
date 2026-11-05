module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P521
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-521 on ARMv7, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P521.Arm.EcdsaP521Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCodeT stackT p521 p521T_verified)
open VG.Proof.HmacTable.Arm (tables vars)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact Arm.target {
    tables := [("hmac", tables vars)]
    code := signCodeT (p521 h.law) Spec.Ecdsa.Rfc6979.Curves.p521.tries vars
    stack := stackT
    verified := p521T_verified h.law }]

end VG.Generic.P521.Arm.EcdsaP521Rfc6979
