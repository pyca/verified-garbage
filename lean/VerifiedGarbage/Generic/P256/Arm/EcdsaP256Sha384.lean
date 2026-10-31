module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P256Sha384Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-384 on ARMv7 -/

@[expose] public section

namespace VG.Generic.P256.Arm.EcdsaP256Sha384

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.Arm.P256Sha384Comb (pack packU sign_verified signU_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P256Sha384.signApi.artifact Arm.target {
    code := (cfgOf (pack h.law)).sign
    consts := Impl.Weierstrass.Arm.p256CombConsts
    stack := 240
    verified := sign_verified h.law },
  Spec.Ecdsa.Rfc6979.P256Sha384.signApi.artifact Arm.target {
    suffix := "_umaal"
    code := (cfgOf (packU h.law)).sign
    consts := Impl.Weierstrass.Arm.p256CombConsts
    stack := 240
    verified := signU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P256.Arm.EcdsaP256Sha384
