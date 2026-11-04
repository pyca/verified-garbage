module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP384r1
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP384r1 on PPC64LE, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.PPC64LE.EcdsaBrainpoolP384r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCode stackT OK brainpoolp384r1C brainpoolp384r1_verified)
open VG.Proof.HashTable.PPC64LE (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1SignApi.artifact PPC64LE.target {
      tables := [("hash", tables vars)]
      code := signCode (brainpoolp384r1C h.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp384r1.tries vars
      stack := stackT
      verified := brainpoolp384r1_verified h.law vars hv }]
  else []

end VG.Generic.BrainpoolP384r1.PPC64LE.EcdsaBrainpoolP384r1Rfc6979
