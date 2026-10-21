module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Secp256k1Sha256Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over secp256k1 with HMAC-SHA-256 on ARMv7

`vg_ecdsa_secp256k1_sha256_sign`, calling HMAC-SHA-256's `init` and `finalize`,
SHA-256's streaming `update`, and `vg_ecdsa_secp256k1_sign`. The stack is 240
bytes: a 216-byte frame, and the 24 bytes below it that the calls use (a
call's 8 or 16 bytes of stack arguments, and the stack of the function it
calls below them).

A generic file (see `TCB/Emit.lean`) over secp256k1's group law `h`, the variant
`Variants/Secp256k1/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.Arm.EcdsaSecp256k1Sha256

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf signNotes)
open VG.Proof.Ecdsa.Rfc6979.Arm.Secp256k1Sha256Comb (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.Secp256k1Sha256.signApi.artifact Arm.target {
    notes := [signNotes
      Proof.Pbkdf2.Whole.Arm.sha256F.hiN Proof.Pbkdf2.Whole.Arm.sha256F.H.updN
      Proof.Pbkdf2.Whole.Arm.sha256F.hfN 32 Spec.Ecdsa.Secp256k1.signApi.name]
    code := (cfgOf (pack h.law)).sign
    consts := Impl.Weierstrass.Arm.secp256k1CombConsts
    stack := 240
    verified := sign_verified h.law }]

end VG.Generic.Secp256k1.Arm.EcdsaSecp256k1Sha256
