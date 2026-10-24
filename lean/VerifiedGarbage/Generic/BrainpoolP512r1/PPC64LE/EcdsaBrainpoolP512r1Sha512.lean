module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP512r1Sha512
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP512r1 with HMAC-SHA-512 on PPC64LE

`vg_ecdsa_brainpoolp512r1_sha512_sign`, calling HMAC-SHA-512's `init` and `finalize`,
SHA-512's streaming `update`, and `vg_ecdsa_brainpoolp512r1_sign`. The stack is 464
bytes: the 48-byte frame saving the link register, a 320-byte frame (`h`'s 64
bytes at its top), and the 96 bytes below it that the calls use.

A generic file (see `TCB/Emit.lean`) over brainpoolP512r1's group law `h`, the variant
`Variants/BrainpoolP512r1/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.PPC64LE.EcdsaBrainpoolP512r1Sha512

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (signNotes sha512K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP512r1Sha512 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.signApi.artifact PPC64LE.target {
    notes := [signNotes Spec.Hmac.sha512I.initScratchApi.name sha512K.H.updN
      Spec.Hmac.sha512I.finalizeScratchApi.name 64 Spec.Ecdsa.BrainpoolP512r1.signApi.name true]
    code := (pack h.law).c.sign
    stack := 464
    verified := sign_verified h.law }]

end VG.Generic.BrainpoolP512r1.PPC64LE.EcdsaBrainpoolP512r1Sha512
