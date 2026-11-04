module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P224
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-224 on PPC64LE, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P224.PPC64LE.EcdsaP224Rfc6979

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCode stackT OK p224C p224_verified)
open VG.Proof.HashTable.PPC64LE (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact PPC64LE.target {
      tables := [("hash", tables vars)]
      code := signCode (p224C h.law) Spec.Ecdsa.Rfc6979.Curves.p224.tries vars
      stack := stackT
      verified := p224_verified h.law vars hv }]
  else []

end VG.Generic.P224.PPC64LE.EcdsaP224Rfc6979
