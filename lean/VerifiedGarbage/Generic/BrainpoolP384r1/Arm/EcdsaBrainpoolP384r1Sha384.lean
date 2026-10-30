module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP384r1Sha384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP384r1 with HMAC-SHA-384 on ARMv7

`vg_ecdsa_brainpoolp384r1_sha384_sign`, calling HMAC-SHA-384's `init` and `finalize`,
SHA-384's streaming `update`, and `vg_ecdsa_brainpoolp384r1_sign`. The stack is 240
bytes: a 216-byte frame, and the 24 bytes below it that the calls use (a
call's 8 or 16 bytes of stack arguments, and the stack of the function it
calls below them).

A generic file (see `TCB/Emit.lean`) over brainpoolP384r1's group law `h`, the variant
`Variants/BrainpoolP384r1/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.Arm.EcdsaBrainpoolP384r1Sha384

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP384r1Sha384 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.signApi.artifact Arm.target {
    code := (cfgOf (pack h.law)).sign
    stack := 240
    verified := sign_verified h.law }]

end VG.Generic.BrainpoolP384r1.Arm.EcdsaBrainpoolP384r1Sha384
