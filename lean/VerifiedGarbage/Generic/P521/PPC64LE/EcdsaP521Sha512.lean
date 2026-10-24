module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P521Sha512
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-521 with HMAC-SHA-512 on PPC64LE

`vg_ecdsa_p521_sha512_sign`, calling HMAC-SHA-512's `init` and `finalize`,
SHA-512's streaming `update`, and `vg_ecdsa_p521_sign`. The stack is 544
bytes: the 48-byte frame saving the link register, a 400-byte frame (the
candidate and the shifted digest in its top 144 bytes), and the 96 bytes
below it that the calls use.

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.PPC64LE.EcdsaP521Sha512

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signNotesWide sha512K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.P521Sha512 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P521Sha512.signApi.artifact PPC64LE.target {
    notes := [signNotesWide Spec.Hmac.sha512I.initScratchApi.name sha512K.H.updN
      Spec.Hmac.sha512I.finalizeScratchApi.name 66 521 64 Spec.Ecdsa.P521.signApi.name]
    code := (pack h.law).c.sign
    stack := 544
    verified := sign_verified h.law }]

end VG.Generic.P521.PPC64LE.EcdsaP521Sha512
