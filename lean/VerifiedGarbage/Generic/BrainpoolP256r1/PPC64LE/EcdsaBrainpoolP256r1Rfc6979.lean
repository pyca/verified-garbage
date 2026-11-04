module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on PPC64LE, with the hash function as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.PPC64LE.EcdsaBrainpoolP256r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCode stackT OK brainpoolp256r1C brainpoolp256r1_verified)
open VG.Proof.HashTable.PPC64LE (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact PPC64LE.target {
      tables := [("hash", tables vars)]
      code := signCode (brainpoolp256r1C h.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vars
      stack := stackT
      verified := brainpoolp256r1_verified h.law vars hv }]
  else []

end VG.Generic.BrainpoolP256r1.PPC64LE.EcdsaBrainpoolP256r1Rfc6979
