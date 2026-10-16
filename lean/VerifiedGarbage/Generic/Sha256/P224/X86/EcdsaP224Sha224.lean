module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P224Sha224
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Deterministic ECDSA (RFC 6979) over P-224 with HMAC-SHA-224 on x86, for every x86 SHA-256 backend

`vg_ecdsa_p224_sha224_sign`, calling HMAC-SHA-224's `init` and `finalize`
and SHA-256's streaming `update` made with the backend's compression
function, and `vg_ecdsa_p224_sign`, is emitted for every backend, named with
its suffix (e.g. `vg_ecdsa_p224_sha224_sign_shani`), and needs its CPU
features.

The stack is 272 bytes: a 196-byte frame, and the 76 bytes below it that the
calls use (up to 24 bytes of arguments and the return address, and 48 bytes
of stack for HMAC's functions).

It is generic over P-224's group law `h` too, the variant
`Variants/P224/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.Sha256.P224.X86.EcdsaP224Sha224

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe signNotes)
open VG.Proof.Ecdsa.Rfc6979.X86.P224Sha224 (pack sign_verified)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) (h : Proof.Weierstrass.HasLaw Spec.P224.curve) :
    List Artifact := [
  Spec.Ecdsa.Rfc6979.P224Sha224.signApi.artifact X86.target {
    suffix := v.suffix
    notes := [signNotes v.F224.hiN v.F224.H.updN v.F224.hfN 28
      Spec.Ecdsa.P224.signApi.name]
    code := (cfgOf (pack h.law v)).sign
    stack := 272
    verified := sign_verified h.law v
    spSafe := sign_spSafe (pack h.law v)
    features := v.features }]

end VG.Generic.Sha256.P224.X86.EcdsaP224Sha224
