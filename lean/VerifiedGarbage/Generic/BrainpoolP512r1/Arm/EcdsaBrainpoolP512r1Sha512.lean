module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP512r1Sha512
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP512r1 with HMAC-SHA-512 on ARMv7

`vg_ecdsa_brainpoolp512r1_sha512_sign`, calling HMAC-SHA-512's `init` and `finalize`,
SHA-512's streaming `update`, and `vg_ecdsa_brainpoolp512r1_sign`. The stack is 304
bytes: a 280-byte frame (P-384's 216 bytes, and `h` in the 64 at its top),
and the 24 bytes below it that the calls use (a call's 8 or 16 bytes of
stack arguments, and the stack of the function it calls below them).

A generic file (see `TCB/Emit.lean`) over brainpoolP512r1's group law `h`, the variant
`Variants/BrainpoolP512r1/Arm/Law.lean`.
-/

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
