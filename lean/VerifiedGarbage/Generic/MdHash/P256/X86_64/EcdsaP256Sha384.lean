import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Sha384

/-!
# Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-384 on x86-64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_p256_sha384_sign`, calling
HMAC-SHA-384's `init` and `finalize` and SHA-512's streaming `update` made
with the variant's SHA-512 compression function, and `vg_ecdsa_p256_sign`,
is emitted for every SHA-384 variant carried by `MdHash.sha384`, named with
its suffix (e.g. `vg_ecdsa_p256_sha384_sign_avx2`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 240 bytes: a 216-byte frame, and the 24 bytes below it that the
calls use (`vg_ecdsa_p256_sign` only its return address).

It is generic over P-256's group law `h` too, the variant
`Variants/P256/X86_64/Law.lean`.
-/

namespace VG.Generic.MdHash.P256.X86_64.EcdsaP256Sha384

open VG.Proof.Ecdsa.Rfc6979.X86_64 (cfgOf sign_spSafe signNotes)
open VG.Proof.Ecdsa.Rfc6979.X86_64.Sha384 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (h : Proof.Weierstrass.HasLaw Spec.P256.curve) :
    List Artifact :=
  match v.sha384 with
  | none => []
  | some c => [
    { Spec.Ecdsa.Rfc6979.P256Sha384.signApi with
      name := Spec.Ecdsa.Rfc6979.P256Sha384.signApi.name ++ c.suffix
      target := X86_64.target
      doc := Spec.Ecdsa.Rfc6979.P256Sha384.signApi.doc
        (notes := [signNotes (cfgOf (pack h.law c)).H 32 Spec.Ecdsa.P256.signApi.name])
      code := (cfgOf (pack h.law c)).sign
      contract := Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract X86_64.abi 240
      stack := 240
      verified := sign_verified h.law c
      spSafe := sign_spSafe (pack h.law c)
      features := c.features }]

end VG.Generic.MdHash.P256.X86_64.EcdsaP256Sha384
