module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P521Sha512
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-521 with HMAC-SHA-512 on ARMv7 -/

@[expose] public section

namespace VG.Generic.P521.Arm.EcdsaP521Sha512

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.Arm.P521Sha512 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P521Sha512.signApi.artifact Arm.target {
    code := (cfgOf (pack h.law)).sign
    stack := 384
    verified := sign_verified h.law }]

end VG.Generic.P521.Arm.EcdsaP521Sha512
