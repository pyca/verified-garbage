module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP384r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP384r1 on ARMv7, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.Arm.EcdsaBrainpoolP384r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (signCode stackT OK brainpoolp384r1Of brainpoolp384r1T_verified)
open VG.Proof.HashTable.Arm (vars tables)

/-- The signature with brainpoolP384r1's multiplication with UMAAL (`umaal`, `_umaal`) or not, and the
tables of `vars`. -/
def withMul (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) (hv : OK vars) (u : Bool) : Artifact :=
  Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact Arm.target {
    suffix := if u then "_umaal" else ""
    tables := [("hash", tables vars)]
    code := signCode (brainpoolp384r1Of u h.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vars
    stack := stackT
    verified := brainpoolp384r1T_verified u h.law vars hv
    features := if u then ["umaal"] else [] }

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact :=
  if hv : OK vars then [withMul h hv false, withMul h hv true] else []

end VG.Generic.BrainpoolP384r1.Arm.EcdsaBrainpoolP384r1Rfc6979
