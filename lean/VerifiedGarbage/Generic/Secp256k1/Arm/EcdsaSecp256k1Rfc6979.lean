module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Secp256k1
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over secp256k1 on ARMv7, with the hash function as an argument

`vg_ecdsa_secp256k1_rfc6979_sign`, calling HMAC's `init` and `finalize` and the
streaming `update` of the hash function `hash` names (SHA-1 or a SHA-2
function), and `vg_ecdsa_secp256k1_sign`. The stack is 456 bytes: a 432-byte
frame, and the 24 bytes below it that the calls use (a call's 8 or 16 bytes
of stack arguments, and the stack of the function it calls below them).

A generic file (see `TCB/Emit.lean`) over secp256k1's group law `h`, the variant
`Variants/Secp256k1/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.Arm.EcdsaSecp256k1Rfc6979

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgR hsArm secp256k1 signNotes sign_verified secp256k1_implies)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.Secp256k1Sha256.inst.signAnyApi.artifact Arm.target {
    notes := [signNotes 32 false 256 Spec.Ecdsa.Secp256k1.signApi.name]
    code := (cfgR (secp256k1 h.law) hsArm).sign
    stack := 456
    verified := sign_verified (secp256k1 h.law) secp256k1_implies }]

end VG.Generic.Secp256k1.Arm.EcdsaSecp256k1Rfc6979
