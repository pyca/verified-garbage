module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P192Sha256
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-192 with HMAC-SHA-256 on PPC64LE -/

@[expose] public section

namespace VG.Generic.P192.PPC64LE.EcdsaP192Sha256

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (sha256K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.P192Sha256 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P192Sha256.signApi.artifact PPC64LE.target {
    code := (pack h.law).c.sign
    stack := 400
    verified := sign_verified h.law }]

end VG.Generic.P192.PPC64LE.EcdsaP192Sha256
