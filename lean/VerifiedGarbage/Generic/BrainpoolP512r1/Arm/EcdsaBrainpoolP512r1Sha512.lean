module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP512r1Sha512
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP512r1 with HMAC-SHA-512 on ARMv7 -/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.Arm.EcdsaBrainpoolP512r1Sha512

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP512r1Sha512 (pack packU sign_verified signU_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.signApi.artifact Arm.target {
    code := (cfgOf (pack h.law)).sign
    stack := 304
    verified := sign_verified h.law },
  Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.signApi.artifact Arm.target {
    suffix := "_umaal"
    code := (cfgOf (packU h.law)).sign
    stack := 304
    verified := signU_verified h.law
    features := ["umaal"] }]

end VG.Generic.BrainpoolP512r1.Arm.EcdsaBrainpoolP512r1Sha512
