module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P521
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-521 on ARMv7, with the hash function as an argument

`vg_ecdsa_p521_rfc6979_sign`, calling HMAC's `init` and `finalize` and the
streaming `update` of the hash function `hash` names (SHA-1 or a SHA-2
function), and `vg_ecdsa_p521_sign`. The stack is 456 bytes: a 432-byte
frame, and the 24 bytes below it that the calls use (a call's 8 or 16 bytes
of stack arguments, and the stack of the function it calls below them).

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.Arm.EcdsaP521Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgR hsArm p521 signNotes sign_verified p521_implies)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P521Sha512.inst.signAnyApi.artifact Arm.target {
    notes := [signNotes 66 true 521 Spec.Ecdsa.P521.signApi.name]
    code := (cfgR (p521 h.law) hsArm).sign
    stack := 456
    verified := sign_verified (p521 h.law) p521_implies }]

end VG.Generic.P521.Arm.EcdsaP521Rfc6979
