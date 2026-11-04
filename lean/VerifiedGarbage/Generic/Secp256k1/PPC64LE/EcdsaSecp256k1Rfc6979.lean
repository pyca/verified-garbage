module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Secp256k1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over secp256k1 on PPC64LE, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.Secp256k1.PPC64LE.EcdsaSecp256k1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCode stackT OK secp256k1C secp256k1_verified)
open VG.Proof.HashTable.PPC64LE (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact PPC64LE.target {
      tables := [("hash", tables vars)]
      code := signCode (secp256k1C h.law) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vars
      stack := stackT
      verified := secp256k1_verified h.law vars hv }]
  else []

end VG.Generic.Secp256k1.PPC64LE.EcdsaSecp256k1Rfc6979
