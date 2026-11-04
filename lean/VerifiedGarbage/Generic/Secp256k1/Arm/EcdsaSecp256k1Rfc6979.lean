module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Secp256k1Comb
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over secp256k1 on ARMv7, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.Secp256k1.Arm.EcdsaSecp256k1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCode stackT OK secp256k1Of secp256k1T_verified)
open VG.Proof.HashTable.Arm (vars tables names)

/-- The signature with secp256k1's multiplication with UMAAL (`umaal`, `_umaal`) or not, and the
tables of `vars`. -/
def withMul (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) (hv : OK vars ∧ ∀ c ∈ Impl.Weierstrass.Arm.secp256k1CombConsts, c.1 ∉ names vars) (u : Bool) : Artifact :=
  Spec.Ecdsa.Rfc6979.Curves.secp256k1SignApi.artifact Arm.target {
    suffix := if u then "_umaal" else ""
    tables := [("hash", tables vars)]
    code := signCode (secp256k1Of u h.law) Spec.Ecdsa.Rfc6979.Curves.secp256k1.tries vars
    consts := Impl.Weierstrass.Arm.secp256k1CombConsts
    stack := stackT
    verified := secp256k1T_verified u h.law vars hv
    features := if u then ["umaal"] else [] }

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact :=
  if hv : OK vars ∧ ∀ c ∈ Impl.Weierstrass.Arm.secp256k1CombConsts, c.1 ∉ names vars then [withMul h hv false, withMul h hv true] else []

end VG.Generic.Secp256k1.Arm.EcdsaSecp256k1Rfc6979
