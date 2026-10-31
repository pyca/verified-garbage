module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP256r1Sha256Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 with HMAC-SHA-256 on ARMv7 -/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.Arm.EcdsaBrainpoolP256r1Sha256

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP256r1Sha256Comb (pack packU sign_verified signU_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.signApi.artifact Arm.target {
    code := (cfgOf (pack h.law)).sign
    consts := Impl.Weierstrass.Arm.brainpoolp256r1CombConsts
    stack := 240
    verified := sign_verified h.law },
  Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.signApi.artifact Arm.target {
    suffix := "_umaal"
    code := (cfgOf (packU h.law)).sign
    consts := Impl.Weierstrass.Arm.brainpoolp256r1CombConsts
    stack := 240
    verified := signU_verified h.law
    features := ["umaal"] }]

end VG.Generic.BrainpoolP256r1.Arm.EcdsaBrainpoolP256r1Sha256
