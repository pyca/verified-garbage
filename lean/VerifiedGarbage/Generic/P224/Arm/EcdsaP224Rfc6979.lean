module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P224Comb
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-224 on ARMv7, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.P224.Arm.EcdsaP224Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCode stackT OK p224Of p224T_verified)
open VG.Proof.HashTable.Arm (vars tables names)

/-- The signature with P-224's multiplication with UMAAL (`umaal`, `_umaal`) or not, and the
tables of `vars`. -/
def withMul (h : Proof.Weierstrass.HasLaw Spec.P224.curve) (hv : OK vars ∧ ∀ c ∈ Impl.Weierstrass.Arm.p224CombConsts, c.1 ∉ names vars) (u : Bool) : Artifact :=
  Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact Arm.target {
    suffix := if u then "_umaal" else ""
    tables := [("hash", tables vars)]
    code := signCode (p224Of u h.law) Spec.Ecdsa.Rfc6979.Curves.p224.tries vars
    consts := Impl.Weierstrass.Arm.p224CombConsts
    stack := stackT
    verified := p224T_verified u h.law vars hv
    features := if u then ["umaal"] else [] }

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact :=
  if hv : OK vars ∧ ∀ c ∈ Impl.Weierstrass.Arm.p224CombConsts, c.1 ∉ names vars then [withMul h hv false, withMul h hv true] else []

end VG.Generic.P224.Arm.EcdsaP224Rfc6979
