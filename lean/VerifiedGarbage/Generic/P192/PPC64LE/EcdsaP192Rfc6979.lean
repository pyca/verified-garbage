module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P192
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-192 on PPC64LE, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P192.PPC64LE.EcdsaP192Rfc6979

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCode stackT OK p192C p192_verified)
open VG.Proof.HashTable.PPC64LE (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact PPC64LE.target {
      tables := [("hash", tables vars)]
      code := signCode (p192C h.law) Spec.Ecdsa.Rfc6979.Curves.p192.tries vars
      stack := stackT
      verified := p192_verified h.law vars hv }]
  else []

end VG.Generic.P192.PPC64LE.EcdsaP192Rfc6979
