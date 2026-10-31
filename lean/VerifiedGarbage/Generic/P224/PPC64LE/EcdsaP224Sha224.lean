module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P224Sha224
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-224 with HMAC-SHA-224 on PPC64LE -/

@[expose] public section

namespace VG.Generic.P224.PPC64LE.EcdsaP224Sha224

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (sha224K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.P224Sha224 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P224Sha224.signApi.artifact PPC64LE.target {
    code := (pack h.law).c.sign
    stack := 400
    verified := sign_verified h.law }]

end VG.Generic.P224.PPC64LE.EcdsaP224Sha224
