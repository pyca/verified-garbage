module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P224Sha224Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-224 with HMAC-SHA-224 on ARMv7

`vg_ecdsa_p224_sha224_sign`, calling HMAC-SHA-224's `init` and `finalize`,
SHA-256's streaming `update`, and `vg_ecdsa_p224_sign`. The stack is 240
bytes: a 216-byte frame, and the 24 bytes below it that the calls use (a
call's 8 or 16 bytes of stack arguments, and the stack of the function it
calls below them).

A generic file (see `TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P224.Arm.EcdsaP224Sha224

open VG.Proof.Ecdsa.Rfc6979.Arm (cfgOf signNotes)
open VG.Proof.Ecdsa.Rfc6979.Arm.P224Sha224Comb (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P224Sha224.signApi.artifact Arm.target {
    notes := [signNotes
      Proof.Pbkdf2.Whole.Arm.sha224F.hiN Proof.Pbkdf2.Whole.Arm.sha224F.H.updN
      Proof.Pbkdf2.Whole.Arm.sha224F.hfN 28 Spec.Ecdsa.P224.signApi.name]
    code := (cfgOf (pack h.law)).sign
    consts := Impl.Weierstrass.Arm.p224CombConsts
    stack := 240
    verified := sign_verified h.law }]

end VG.Generic.P224.Arm.EcdsaP224Sha224
