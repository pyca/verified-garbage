module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P256
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-256 on PPC64LE, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P256.PPC64LE.EcdsaP256Rfc6979

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCodeT stackT OK p256R p256T_verified)
open VG.Proof.HmacTable.PPC64LE (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := signCodeT (p256R h.law) Spec.Ecdsa.Rfc6979.Curves.p256.tries vars
      stack := stackT
      verified := p256T_verified h.law vars hv }]
  else []

end VG.Generic.P256.PPC64LE.EcdsaP256Rfc6979
