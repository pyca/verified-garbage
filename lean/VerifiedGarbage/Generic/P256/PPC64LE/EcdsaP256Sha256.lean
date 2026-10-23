module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.P256Sha256
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-256 on PPC64LE

`vg_ecdsa_p256_sha256_sign`, calling HMAC-SHA-256's `init` and `finalize`,
SHA-256's streaming `update`, and `vg_ecdsa_p256_sign`. The stack is 400
bytes: the 48-byte frame saving the link register, a 256-byte frame, and the
96 bytes below it that the calls use.

A generic file (see `TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.PPC64LE.EcdsaP256Sha256

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signNotes sha256K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.P256Sha256 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P256Sha256.signApi.artifact PPC64LE.target {
    notes := [signNotes Spec.Hmac.sha256I.initScratchApi.name sha256K.H.updN
      Spec.Hmac.sha256I.finalizeScratchApi.name 32 Spec.Ecdsa.P256.signApi.name]
    code := (pack h.law).c.sign
    stack := 400
    verified := sign_verified h.law }]

end VG.Generic.P256.PPC64LE.EcdsaP256Sha256
