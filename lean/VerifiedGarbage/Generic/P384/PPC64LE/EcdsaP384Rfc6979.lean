module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P384
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.HmacTable.PPC64LE.Vars
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # Deterministic ECDSA (RFC 6979) over P-384 on PPC64LE, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P384.PPC64LE.EcdsaP384Rfc6979

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signCodeT stackT OK p384R p384T_verified)
open VG.Proof.HmacTable.PPC64LE (vars tables)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact :=
  if hv : OK vars then [
    Spec.Ecdsa.Rfc6979.Curves.p384SignApi.artifact PPC64LE.target {
      tables := [("hmac", tables vars)]
      code := signCodeT (p384R h.law) Spec.Ecdsa.Rfc6979.Curves.p384.tries vars
      stack := stackT
      verified := p384T_verified h.law vars hv }]
  else []

end VG.Generic.P384.PPC64LE.EcdsaP384Rfc6979
