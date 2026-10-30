module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P384Sha384
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-384 with HMAC-SHA-384 on x86 (32-bit)

`vg_ecdsa_p384_sha384_sign`, calling HMAC-SHA-384's `init` and `finalize`,
SHA-384's streaming `update`, and `vg_ecdsa_p384_sign`. The stack is 272
bytes: a 196-byte frame, and the 76 bytes below it that the calls use (up
to 24 bytes of arguments and the return address, and 48 bytes of stack for
HMAC's functions).

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.X86.EcdsaP384Sha384

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe)
open VG.Proof.Ecdsa.Rfc6979.X86.P384Sha384 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P384Sha384.signApi.artifact X86.target {
    code := (cfgOf (pack h.law)).sign
    stack := 272
    verified := sign_verified h.law
    spSafe := sign_spSafe (pack h.law) }]

end VG.Generic.P384.X86.EcdsaP384Sha384
