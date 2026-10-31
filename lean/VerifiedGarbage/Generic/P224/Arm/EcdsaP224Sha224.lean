module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P224Sha224Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-224 with HMAC-SHA-224 on ARMv7 -/

@[expose] public section

namespace VG.Generic.P224.Arm.EcdsaP224Sha224

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.Arm.P224Sha224Comb (pack packU sign_verified signU_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P224Sha224.signApi.artifact Arm.target {
    code := (cfgOf (pack h.law)).sign
    consts := Impl.Weierstrass.Arm.p224CombConsts
    stack := 240
    verified := sign_verified h.law },
  Spec.Ecdsa.Rfc6979.P224Sha224.signApi.artifact Arm.target {
    suffix := "_umaal"
    code := (cfgOf (packU h.law)).sign
    consts := Impl.Weierstrass.Arm.p224CombConsts
    stack := 240
    verified := signU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P224.Arm.EcdsaP224Sha224
