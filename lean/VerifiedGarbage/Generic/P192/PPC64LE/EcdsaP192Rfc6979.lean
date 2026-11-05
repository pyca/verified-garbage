module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P192
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars

/-! # Deterministic ECDSA (RFC 6979) over P-192 on PPC64LE, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P192.PPC64LE.EcdsaP192Rfc6979

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCodeT stackT OK p192R p192T_verified)
open VG.Proof.HmacTable.PPC64LE (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.p192SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := signCodeT (p192R h.law) Spec.Ecdsa.Rfc6979.Curves.p192.tries vars
      stack := stackT
      verified := p192T_verified h.law vars hv }]
  else []

end VG.Generic.P192.PPC64LE.EcdsaP192Rfc6979
