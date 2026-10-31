module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P384Sha384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-384 with HMAC-SHA-384 on PPC64LE -/

@[expose] public section

namespace VG.Generic.P384.PPC64LE.EcdsaP384Sha384

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (sha384K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.P384Sha384 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P384Sha384.signApi.artifact PPC64LE.target {
    code := (pack h.law).c.sign
    stack := 400
    verified := sign_verified h.law }]

end VG.Generic.P384.PPC64LE.EcdsaP384Sha384
