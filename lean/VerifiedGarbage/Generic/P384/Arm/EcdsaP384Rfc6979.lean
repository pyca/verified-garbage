module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P384
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-384 on ARMv7, with the hash function as an argument

`vg_ecdsa_p384_rfc6979_sign`, calling HMAC's `init` and `finalize` and the
streaming `update` of the hash function `hash` names (SHA-1 or a SHA-2
function), and `vg_ecdsa_p384_sign`. The stack is 456 bytes: a 432-byte
frame, and the 24 bytes below it that the calls use (a call's 8 or 16 bytes
of stack arguments, and the stack of the function it calls below them).

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.Arm.EcdsaP384Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgR hsArm p384 signNotes sign_verified p384_implies)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P384Sha384.inst.signAnyApi.artifact Arm.target {
    notes := [signNotes 48 false 384 Spec.Ecdsa.P384.signApi.name]
    code := (cfgR (p384 h.law) hsArm).sign
    stack := 456
    verified := sign_verified (p384 h.law) p384_implies }]

end VG.Generic.P384.Arm.EcdsaP384Rfc6979
