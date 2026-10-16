module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Sha384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-384 on ARMv7

`vg_ecdsa_p256_sha384_sign`, calling HMAC-SHA-384's `init` and `finalize`,
SHA-384's streaming `update`, and `vg_ecdsa_p256_sign`. The stack is 240
bytes: a 216-byte frame, and the 24 bytes below it that the calls use (a
call's 8 or 16 bytes of stack arguments, and the stack of the function it
calls below them).

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.Arm.EcdsaP256Sha384

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf signNotes)
open VG.Proof.Ecdsa.Rfc6979.Arm.Sha384 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P256Sha384.signApi.artifact Arm.target {
    notes := [signNotes
      Proof.Pbkdf2.Whole.Arm.sha384F.hiN Proof.Pbkdf2.Whole.Arm.sha384F.H.updN
      Proof.Pbkdf2.Whole.Arm.sha384F.hfN 32 Spec.Ecdsa.P256.signApi.name]
    code := (cfgOf (pack h.law)).sign
    stack := 240
    verified := sign_verified h.law }]

end VG.Generic.P256.Arm.EcdsaP256Sha384
