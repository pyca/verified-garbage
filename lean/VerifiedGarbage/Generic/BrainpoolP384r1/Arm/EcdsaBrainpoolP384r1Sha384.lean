module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP384r1Sha384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP384r1 with HMAC-SHA-384 on ARMv7 -/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.Arm.EcdsaBrainpoolP384r1Sha384

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP384r1Sha384 (pack packU sign_verified signU_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.signApi.artifact Arm.target {
    code := (cfgOf (pack h.law)).sign
    stack := 240
    verified := sign_verified h.law },
  Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.signApi.artifact Arm.target {
    suffix := "_umaal"
    code := (cfgOf (packU h.law)).sign
    stack := 240
    verified := signU_verified h.law
    features := ["umaal"] }]

end VG.Generic.BrainpoolP384r1.Arm.EcdsaBrainpoolP384r1Sha384
