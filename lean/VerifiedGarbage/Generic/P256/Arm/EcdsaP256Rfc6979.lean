module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P256Comb
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-256 on ARMv7, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P256.Arm.EcdsaP256Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCode stackT OK p256Of p256T_verified)
open VG.Proof.HashTable.Arm (vars tables names)

/-- The signature with P-256's multiplication with UMAAL (`umaal`, `_umaal`) or not, and the
tables of `vars`. -/
def withMul (h : Proof.Weierstrass.HasLaw Spec.P256.curve) (hv : OK vars ∧ ∀ c ∈ Impl.Weierstrass.Arm.p256CombConsts, c.1 ∉ names vars) (u : Bool) : Artifact :=
  Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact Arm.target {
    suffix := if u then "_umaal" else ""
    tables := [("hash", tables vars)]
    code := signCode (p256Of u h.law) Spec.Ecdsa.Rfc6979.Curves.p256.tries vars
    consts := Impl.Weierstrass.Arm.p256CombConsts
    stack := stackT
    verified := p256T_verified u h.law vars hv
    features := if u then ["umaal"] else [] }

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact :=
  if hv : OK vars ∧ ∀ c ∈ Impl.Weierstrass.Arm.p256CombConsts, c.1 ∉ names vars then [withMul h hv false, withMul h hv true] else []

end VG.Generic.P256.Arm.EcdsaP256Rfc6979
