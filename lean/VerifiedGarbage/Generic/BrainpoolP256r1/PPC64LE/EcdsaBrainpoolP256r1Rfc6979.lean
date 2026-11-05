module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP256r1
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 on PPC64LE, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.PPC64LE.EcdsaBrainpoolP256r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCodeT stackT OK brainpoolp256r1R brainpoolp256r1T_verified)
open VG.Proof.HmacTable.PPC64LE (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := signCodeT (brainpoolp256r1R h.law) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vars
      stack := stackT
      verified := brainpoolp256r1T_verified h.law vars hv }]
  else []

end VG.Generic.BrainpoolP256r1.PPC64LE.EcdsaBrainpoolP256r1Rfc6979
