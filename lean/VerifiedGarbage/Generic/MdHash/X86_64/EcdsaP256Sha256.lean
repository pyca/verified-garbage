import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Sha256

/-!
# Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-256 on x86-64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_p256_sha256_sign`, calling
HMAC-SHA-256's `init` and `finalize` and SHA-256's streaming `update` made
with the variant's SHA-256 compression function, and `vg_ecdsa_p256_sign`,
is emitted for every SHA-256 variant carried by `MdHash.sha256`, named with
its suffix (e.g. `vg_ecdsa_p256_sha256_sign_shani`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 224 bytes: a 200-byte frame, and the 24 bytes below it that the
calls use (`vg_ecdsa_p256_sign` only its return address).
-/

namespace VG.Generic.MdHash.X86_64.EcdsaP256Sha256

open VG.Proof.Ecdsa.Rfc6979.X86_64 (cfgOf sign_spSafe signNotes)
open VG.Proof.Ecdsa.Rfc6979.X86_64.Sha256 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  match v.sha256 with
  | none => []
  | some c => [
    { Spec.Ecdsa.Rfc6979.P256Sha256.signApi with
      name := Spec.Ecdsa.Rfc6979.P256Sha256.signApi.name ++ c.suffix
      target := X86_64.target
      doc := Spec.Ecdsa.Rfc6979.P256Sha256.signApi.doc (notes := [signNotes (cfgOf (pack Proof.P256.law c)).H])
      code := (cfgOf (pack Proof.P256.law c)).sign
      contract := Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract X86_64.abi 224
      stack := 224
      verified := sign_verified Proof.P256.law c
      spSafe := sign_spSafe (pack Proof.P256.law c)
      features := c.features }]

end VG.Generic.MdHash.X86_64.EcdsaP256Sha256
