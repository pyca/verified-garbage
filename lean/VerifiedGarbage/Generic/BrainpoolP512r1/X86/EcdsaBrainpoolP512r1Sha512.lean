module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.BrainpoolP512r1Sha512
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over brainpoolP512r1 with HMAC-SHA-512 on x86 (32-bit)

`vg_ecdsa_brainpoolp512r1_sha512_sign`, calling HMAC-SHA-512's `init` and `finalize`,
SHA-512's streaming `update`, and `vg_ecdsa_brainpoolp512r1_sign`. The stack is 336
bytes: a 260-byte frame (P-384's 196 bytes, and `h` in the 64 at its top),
and the 76 bytes below it that the calls use (up to 24 bytes of arguments
and the return address, and 48 bytes of stack for HMAC's functions).

A generic file (see `TCB/Emit.lean`) over brainpoolP512r1's group law `h`, the variant
`Variants/BrainpoolP512r1/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.X86.EcdsaBrainpoolP512r1Sha512

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe)
open VG.Proof.Ecdsa.Rfc6979.X86.BrainpoolP512r1Sha512 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.signApi.artifact X86.target {
    code := (cfgOf (pack h.law)).sign
    stack := 336
    verified := sign_verified h.law
    spSafe := sign_spSafe (pack h.law) }]

end VG.Generic.BrainpoolP512r1.X86.EcdsaBrainpoolP512r1Sha512
