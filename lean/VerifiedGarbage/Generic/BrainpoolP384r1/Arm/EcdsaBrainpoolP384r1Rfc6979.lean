module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP384r1
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP384r1 on ARMv7, with the hash function as an argument

`vg_ecdsa_brainpoolp384r1_rfc6979_sign`, calling HMAC's `init` and `finalize` and the
streaming `update` of the hash function `hash` names (SHA-1 or a SHA-2
function), and `vg_ecdsa_brainpoolp384r1_sign`. The stack is 456 bytes: a 432-byte
frame, and the 24 bytes below it that the calls use (a call's 8 or 16 bytes
of stack arguments, and the stack of the function it calls below them).

A generic file (see `TCB/Emit.lean`) over brainpoolP384r1's group law `h`, the variant
`Variants/BrainpoolP384r1/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.Arm.EcdsaBrainpoolP384r1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgR hsArm brainpoolp384r1 signNotes sign_verified brainpoolp384r1_implies)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst.signAnyApi.artifact Arm.target {
    notes := [signNotes 48 false 384 Spec.Ecdsa.BrainpoolP384r1.signApi.name]
    code := (cfgR (brainpoolp384r1 h.law) hsArm).sign
    stack := 456
    verified := sign_verified (brainpoolp384r1 h.law) brainpoolp384r1_implies }]

end VG.Generic.BrainpoolP384r1.Arm.EcdsaBrainpoolP384r1Rfc6979
