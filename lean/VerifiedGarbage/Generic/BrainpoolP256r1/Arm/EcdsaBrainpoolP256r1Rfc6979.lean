module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP256r1Comb
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on ARMv7, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.Arm.EcdsaBrainpoolP256r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCode stackT OK brainpoolp256r1Of brainpoolp256r1T_verified)
open VG.Proof.HashTable.Arm (vars tables names)

/-- The signature with brainpoolP256r1's multiplication with UMAAL (`umaal`, `_umaal`) or not, and the
tables of `vars`. -/
def withMul (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) (hv : OK vars ∧ ∀ c ∈ Impl.Weierstrass.Arm.brainpoolp256r1CombConsts, c.1 ∉ names vars) (u : Bool) : Artifact :=
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact Arm.target {
    suffix := if u then "_umaal" else ""
    tables := [("hash", tables vars)]
    code := signCode (brainpoolp256r1Of u h.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vars
    consts := Impl.Weierstrass.Arm.brainpoolp256r1CombConsts
    stack := stackT
    verified := brainpoolp256r1T_verified u h.law vars hv
    features := if u then ["umaal"] else [] }

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact :=
  if hv : OK vars ∧ ∀ c ∈ Impl.Weierstrass.Arm.brainpoolp256r1CombConsts, c.1 ∉ names vars then [withMul h hv false, withMul h hv true] else []

end VG.Generic.BrainpoolP256r1.Arm.EcdsaBrainpoolP256r1Rfc6979
