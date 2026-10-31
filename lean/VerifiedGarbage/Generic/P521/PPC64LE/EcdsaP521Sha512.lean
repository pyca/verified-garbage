module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P521Sha512
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-521 with HMAC-SHA-512 on PPC64LE -/

@[expose] public section

namespace VG.Generic.P521.PPC64LE.EcdsaP521Sha512

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (sha512K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.P521Sha512 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P521Sha512.signApi.artifact PPC64LE.target {
    code := (pack h.law).c.sign
    stack := 544
    verified := sign_verified h.law }]

end VG.Generic.P521.PPC64LE.EcdsaP521Sha512
