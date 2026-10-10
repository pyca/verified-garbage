import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.P192Sha256

/-!
# Deterministic ECDSA (RFC 6979) over P-192 with HMAC-SHA-256 on x86, for every x86 SHA-256 backend

`vg_ecdsa_p192_sha256_sign`, calling HMAC-SHA-256's `init` and `finalize`
and SHA-256's streaming `update` made with the backend's compression
function, and `vg_ecdsa_p192_sign`, is emitted for every backend, named with
its suffix (e.g. `vg_ecdsa_p192_sha256_sign_shani`), and needs its CPU
features.

The stack is 272 bytes: a 196-byte frame, and the 76 bytes below it that the
calls use (up to 24 bytes of arguments and the return address, and 48 bytes
of stack for HMAC's functions).

It is generic over P-192's group law `h` too, the variant
`Variants/P192/X86/Law.lean`.
-/

namespace VG.Generic.Sha256.P192.X86.EcdsaP192Sha256

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe signNotes)
open VG.Proof.Ecdsa.Rfc6979.X86.P192Sha256 (pack sign_verified)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) (h : Proof.Weierstrass.HasLaw Spec.P192.curve) :
    List Artifact := [
  { Spec.Ecdsa.Rfc6979.P192Sha256.signApi with
    name := Spec.Ecdsa.Rfc6979.P192Sha256.signApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Ecdsa.Rfc6979.P192Sha256.signApi.doc (notes := [signNotes v.F.hiN v.F.H.updN v.F.hfN 32
      Spec.Ecdsa.P192.signApi.name])
    code := (cfgOf (pack h.law v)).sign
    contract := Spec.Ecdsa.Rfc6979.P192Sha256.inst.signContract X86.abi 272
    stack := 272
    verified := sign_verified h.law v
    spSafe := sign_spSafe (pack h.law v)
    features := v.features }]

end VG.Generic.Sha256.P192.X86.EcdsaP192Sha256
