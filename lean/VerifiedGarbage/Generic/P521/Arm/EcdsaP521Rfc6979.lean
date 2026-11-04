module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P521
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-521 on ARMv7, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P521.Arm.EcdsaP521Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCode stackT OK p521 p521T_verified)
open VG.Proof.HashTable.Arm (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact Arm.target {
      tables := [("hash", tables vars)]
      code := signCode (p521 h.law) Spec.Ecdsa.Rfc6979.Curves.p521.tries vars
      stack := stackT
      verified := p521T_verified h.law vars hv }]
  else []

end VG.Generic.P521.Arm.EcdsaP521Rfc6979
