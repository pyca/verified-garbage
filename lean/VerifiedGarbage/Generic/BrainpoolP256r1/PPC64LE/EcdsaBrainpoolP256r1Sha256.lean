module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP256r1Sha256
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP256r1 with HMAC-SHA-256 on PPC64LE

`vg_ecdsa_brainpoolp256r1_sha256_sign`, calling HMAC-SHA-256's `init` and `finalize`,
SHA-256's streaming `update`, and `vg_ecdsa_brainpoolp256r1_sign`. The stack is 400
bytes: the 48-byte frame saving the link register, a 256-byte frame, and the
96 bytes below it that the calls use.

A generic file (see `TCB/Emit.lean`) over brainpoolP256r1's group law `h`, the variant
`Variants/BrainpoolP256r1/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP256r1.PPC64LE.EcdsaBrainpoolP256r1Sha256

open VG.Proof.Ecdsa.Rfc6979.PPC64LE (sha256K)
open VG.Proof.Ecdsa.Rfc6979.PPC64LE.BrainpoolP256r1Sha256 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP256r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.signApi.artifact PPC64LE.target {
    code := (pack h.law).c.sign
    stack := 400
    verified := sign_verified h.law }]

end VG.Generic.BrainpoolP256r1.PPC64LE.EcdsaBrainpoolP256r1Sha256
