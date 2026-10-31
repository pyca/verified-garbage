module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P256Sha384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-384 on PPC64LE -/

@[expose] public section

namespace VG.Generic.P256.PPC64LE.EcdsaP256Sha384

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (sha384K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.P256Sha384 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P256Sha384.signApi.artifact PPC64LE.target {
    code := (pack h.law).c.sign
    stack := 400
    verified := sign_verified h.law }]

end VG.Generic.P256.PPC64LE.EcdsaP256Sha384
