module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P256
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-256 on ARMv7, with the hash function as an argument

`vg_ecdsa_p256_rfc6979_sign`, calling HMAC's `init` and `finalize` and the
streaming `update` of the hash function `hash` names (SHA-1 or a SHA-2
function), and `vg_ecdsa_p256_sign`. The stack is 456 bytes: a 432-byte
frame, and the 24 bytes below it that the calls use (a call's 8 or 16 bytes
of stack arguments, and the stack of the function it calls below them).

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.Arm.EcdsaP256Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgR hsArm p256 signNotes sign_verified p256_implies)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P256Sha256.inst.signAnyApi.artifact Arm.target {
    notes := [signNotes 32 false 256 Spec.Ecdsa.P256.signApi.name]
    code := (cfgR (p256 h.law) hsArm).sign
    stack := 456
    verified := sign_verified (p256 h.law) p256_implies }]

end VG.Generic.P256.Arm.EcdsaP256Rfc6979
