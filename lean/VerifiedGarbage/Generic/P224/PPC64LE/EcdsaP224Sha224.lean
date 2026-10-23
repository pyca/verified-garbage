module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P224Sha224
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-224 with HMAC-SHA-224 on PPC64LE

`vg_ecdsa_p224_sha224_sign`, calling HMAC-SHA-224's `init` and `finalize`,
SHA-224's streaming `update`, and `vg_ecdsa_p224_sign`. The stack is 400
bytes: the 48-byte frame saving the link register, a 256-byte frame, and the
96 bytes below it that the calls use.

A generic file (see `TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P224.PPC64LE.EcdsaP224Sha224

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signNotes sha224K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.P224Sha224 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P224Sha224.signApi.artifact PPC64LE.target {
    notes := [signNotes Spec.Hmac.sha224I.initScratchApi.name sha224K.H.updN
      Spec.Hmac.sha224I.finalizeScratchApi.name 28 Spec.Ecdsa.P224.signApi.name]
    code := (pack h.law).c.sign
    stack := 400
    verified := sign_verified h.law }]

end VG.Generic.P224.PPC64LE.EcdsaP224Sha224
