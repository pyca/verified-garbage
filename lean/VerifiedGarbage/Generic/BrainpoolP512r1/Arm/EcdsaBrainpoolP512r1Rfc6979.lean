module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP512r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP512r1 on ARMv7, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.Arm.EcdsaBrainpoolP512r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCode stackT OK brainpoolp512r1Of brainpoolp512r1T_verified)
open VG.Proof.HashTable.Arm (vars tables)

/-- The signature with brainpoolP512r1's multiplication with UMAAL (`umaal`, `_umaal`) or not, and the
tables of `vars`. -/
def withMul (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) (hv : OK vars) (u : Bool) : Artifact :=
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1SignApi.artifact Arm.target {
    suffix := if u then "_umaal" else ""
    tables := [("hash", tables vars)]
    code := signCode (brainpoolp512r1Of u h.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries vars
    stack := stackT
    verified := brainpoolp512r1T_verified u h.law vars hv
    features := if u then ["umaal"] else [] }

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact :=
  if hv : OK vars then [withMul h hv false, withMul h hv true] else []

end VG.Generic.BrainpoolP512r1.Arm.EcdsaBrainpoolP512r1Rfc6979
