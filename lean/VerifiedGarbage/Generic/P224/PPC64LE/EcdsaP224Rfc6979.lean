module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P224
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Deterministic ECDSA (RFC 6979) over P-224 on PPC64LE, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P224.PPC64LE.EcdsaP224Rfc6979

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCodeT stackT OK p224R p224T_verified)
open VG.Proof.HmacTable.PPC64LE (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := signCodeT (p224R h.law) Spec.Ecdsa.Rfc6979.Curves.p224.tries vars
      stack := stackT
      verified := p224T_verified h.law vars hv }]
  else []

end VG.Generic.P224.PPC64LE.EcdsaP224Rfc6979
