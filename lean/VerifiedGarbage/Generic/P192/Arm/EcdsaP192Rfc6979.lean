module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P192
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-192 on ARMv7, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P192.Arm.EcdsaP192Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCode stackT OK p192 p192T_verified)
open VG.Proof.HashTable.Arm (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact Arm.target {
      tables := [("hash", tables vars)]
      code := signCode (p192 h.law) Spec.Ecdsa.Rfc6979.Curves.p192.tries vars
      stack := stackT
      verified := p192T_verified h.law vars hv }]
  else []

end VG.Generic.P192.Arm.EcdsaP192Rfc6979
