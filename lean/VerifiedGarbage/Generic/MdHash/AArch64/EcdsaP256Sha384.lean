import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.P256.Curve
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Sha384

/-!
# Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-384 on AArch64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_p256_sha384_sign`, calling
HMAC-SHA-384's `init` and `finalize` and SHA-512's streaming `update` made
with the variant's SHA-512 compression function, and `vg_ecdsa_p256_sign`,
is emitted for every SHA-384 variant carried by `MdHash.sha384`, named with
its suffix (e.g. `vg_ecdsa_p256_sha384_sign_sha3`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 256 bytes: 16 saving `x30`, a 224-byte frame, and the 16 bytes
below it that HMAC's functions use (`vg_ecdsa_p256_sign` uses none).
-/

namespace VG.Generic.MdHash.AArch64.EcdsaP256Sha384

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf signNotes)
open VG.Proof.Ecdsa.Rfc6979.AArch64.Sha384 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  match v.sha384 with
  | none => []
  | some c => [
    { Spec.Ecdsa.Rfc6979.P256Sha384.signApi with
      name := Spec.Ecdsa.Rfc6979.P256Sha384.signApi.name ++ c.suffix
      target := AArch64.target
      doc := Spec.Ecdsa.Rfc6979.P256Sha384.signApi.doc
        (notes := [signNotes (cfgOf (pack Proof.P256.law Proof.P256.combOk7 c)).H 32 Spec.Ecdsa.P256.signApi.name])
      code := (cfgOf (pack Proof.P256.law Proof.P256.combOk7 c)).sign
      consts := Impl.Ecdsa.AArch64.p256.combConsts
      contract := Spec.Ecdsa.Rfc6979.P256Sha384.inst.signContract
        (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts) 256
      stack := 256
      verified := sign_verified Proof.P256.law Proof.P256.combOk7 c
      spSafe := Code.all_of_forall (fun _ => rfl) _
      features := c.features }]

end VG.Generic.MdHash.AArch64.EcdsaP256Sha384
