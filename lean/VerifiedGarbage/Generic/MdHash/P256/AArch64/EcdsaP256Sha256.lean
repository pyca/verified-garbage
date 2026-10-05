import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.HasLaw
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Sha256

/-!
# Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-256 on AArch64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_p256_sha256_sign`, calling
HMAC-SHA-256's `init` and `finalize` and SHA-256's streaming `update` made
with the variant's SHA-256 compression function, and `vg_ecdsa_p256_sign`,
is emitted for every SHA-256 variant carried by `MdHash.sha256`, named with
its suffix (e.g. `vg_ecdsa_p256_sha256_sign_sha2`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 256 bytes: 16 saving `x30`, a 224-byte frame, and the 16 bytes
below it that HMAC's functions use (`vg_ecdsa_p256_sign` uses none).

It is generic over P-256's group law `h` too, the variant
`Variants/P256/AArch64/Law.lean`.
-/

namespace VG.Generic.MdHash.P256.AArch64.EcdsaP256Sha256

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf signNotes)
open VG.Proof.Ecdsa.Rfc6979.AArch64.Sha256 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (h : Proof.Weierstrass.HasLaw Spec.P256.curve) :
    List Artifact :=
  match v.sha256 with
  | none => []
  | some c => [
    { Spec.Ecdsa.Rfc6979.P256Sha256.signApi with
      name := Spec.Ecdsa.Rfc6979.P256Sha256.signApi.name ++ c.suffix
      target := AArch64.target
      doc := Spec.Ecdsa.Rfc6979.P256Sha256.signApi.doc
        (notes := [signNotes (cfgOf (pack h.law h.inv (Proof.P256.combOk7 h.law) c)).H 32 Spec.Ecdsa.P256.signApi.name])
      code := (cfgOf (pack h.law h.inv (Proof.P256.combOk7 h.law) c)).sign
      consts := Impl.Ecdsa.AArch64.p256.combConsts
      contract := Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract
        (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts) 256
      stack := 256
      verified := sign_verified h.law h.inv (Proof.P256.combOk7 h.law) c
      spSafe := Code.all_of_forall (fun _ => rfl) _
      features := c.features }]

end VG.Generic.MdHash.P256.AArch64.EcdsaP256Sha256
