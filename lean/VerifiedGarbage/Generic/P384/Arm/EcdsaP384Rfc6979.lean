module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P384Comb
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-384 on ARMv7, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P384.Arm.EcdsaP384Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCode stackT OK p384Of p384T_verified)
open VG.Proof.HashTable.Arm (vars tables names)

/-- The signature with P-384's multiplication with UMAAL (`umaal`, `_umaal`) or not, and the
tables of `vars`. -/
def withMul (h : Proof.Weierstrass.HasLaw Spec.P384.curve) (hv : OK vars ∧ ∀ c ∈ Impl.Weierstrass.Arm.p384CombConsts, c.1 ∉ names vars) (u : Bool) : Artifact :=
  Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact Arm.target {
    suffix := if u then "_umaal" else ""
    tables := [("hash", tables vars)]
    code := signCode (p384Of u h.law) Spec.Ecdsa.Rfc6979.Curves.p384.tries vars
    consts := Impl.Weierstrass.Arm.p384CombConsts
    stack := stackT
    verified := p384T_verified u h.law vars hv
    features := if u then ["umaal"] else [] }

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact :=
  if hv : OK vars ∧ ∀ c ∈ Impl.Weierstrass.Arm.p384CombConsts, c.1 ∉ names vars then [withMul h hv false, withMul h hv true] else []

end VG.Generic.P384.Arm.EcdsaP384Rfc6979
