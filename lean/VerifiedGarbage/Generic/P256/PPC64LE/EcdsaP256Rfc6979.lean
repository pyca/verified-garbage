module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-256 on PPC64LE, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P256.PPC64LE.EcdsaP256Rfc6979

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCode stackT OK p256C p256_verified)
open VG.Proof.HashTable.PPC64LE (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact PPC64LE.target {
      tables := [("hash", tables vars)]
      code := signCode (p256C h.law) Spec.Ecdsa.Rfc6979.Curves.p256.tries vars
      stack := stackT
      verified := p256_verified h.law vars hv }]
  else []

end VG.Generic.P256.PPC64LE.EcdsaP256Rfc6979
