module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P192Sha256
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-192 with HMAC-SHA-256 on ARMv7 -/

@[expose] public section

namespace VG.Generic.P192.Arm.EcdsaP192Sha256

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.Arm.P192Sha256 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P192.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P192Sha256.signApi.artifact Arm.target {
    code := (cfgOf (pack h.law)).sign
    stack := 240
    verified := sign_verified h.law }]

end VG.Generic.P192.Arm.EcdsaP192Sha256
