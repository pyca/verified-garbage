module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P256Sha256Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-256 on ARMv7

`vg_ecdsa_p256_sha256_sign`, calling HMAC-SHA-256's `init` and `finalize`,
SHA-256's streaming `update`, and `vg_ecdsa_p256_sign`. The stack is 240
bytes: a 216-byte frame, and the 24 bytes below it that the calls use (a
call's 8 or 16 bytes of stack arguments, and the stack of the function it
calls below them).

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.Arm.EcdsaP256Sha256

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf signNotes)
open VG.Proof.Ecdsa.Rfc6979.Arm.P256Sha256Comb (pack packU sign_verified signU_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P256Sha256.signApi.artifact Arm.target {
    notes := [signNotes
      Proof.Pbkdf2.Whole.Arm.sha256F.hiN Proof.Pbkdf2.Whole.Arm.sha256F.H.updN
      Proof.Pbkdf2.Whole.Arm.sha256F.hfN 32 Spec.Ecdsa.P256.signApi.name]
    code := (cfgOf (pack h.law)).sign
    consts := Impl.Weierstrass.Arm.p256CombConsts
    stack := 240
    verified := sign_verified h.law },
  Spec.Ecdsa.Rfc6979.P256Sha256.signApi.artifact Arm.target {
    suffix := "_umaal"
    notes := [signNotes
      Proof.Pbkdf2.Whole.Arm.sha256F.hiN Proof.Pbkdf2.Whole.Arm.sha256F.H.updN
      Proof.Pbkdf2.Whole.Arm.sha256F.hfN 32 (Spec.Ecdsa.P256.signApi.name ++ "_umaal")]
    code := (cfgOf (packU h.law)).sign
    consts := Impl.Weierstrass.Arm.p256CombConsts
    stack := 240
    verified := signU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P256.Arm.EcdsaP256Sha256
