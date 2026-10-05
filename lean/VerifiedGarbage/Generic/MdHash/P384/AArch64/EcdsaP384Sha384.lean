import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.HasLaw
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P384Sha384

/-!
# Deterministic ECDSA (RFC 6979) over P-384 with HMAC-SHA-384 on AArch64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_p384_sha384_sign`, calling
HMAC-SHA-384's `init` and `finalize` and SHA-512's streaming `update` made
with the variant's SHA-512 compression function, and `vg_ecdsa_p384_sign`,
is emitted for every SHA-384 variant carried by `MdHash.sha384`, named with
its suffix (e.g. `vg_ecdsa_p384_sha384_sign_sha3`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 256 bytes: 16 saving `x30`, a 224-byte frame, and the 16 bytes
below it that HMAC's functions use (`vg_ecdsa_p384_sign` uses none).

It is generic over P-384's group law `h` too, the variant
`Variants/P384/AArch64/Law.lean`.
-/

namespace VG.Generic.MdHash.P384.AArch64.EcdsaP384Sha384

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf signNotes)
open VG.Proof.Ecdsa.Rfc6979.AArch64.P384Sha384 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (h : Proof.Weierstrass.HasLaw Spec.P384.curve) :
    List Artifact :=
  match v.sha384 with
  | none => []
  | some c => [
    { Spec.Ecdsa.Rfc6979.P384Sha384.signApi with
      name := Spec.Ecdsa.Rfc6979.P384Sha384.signApi.name ++ c.suffix
      target := AArch64.target
      doc := Spec.Ecdsa.Rfc6979.P384Sha384.signApi.doc
        (notes := [signNotes (cfgOf (pack h.law h.inv (Proof.P384.combOk7 h.law) c)).H 48 Spec.Ecdsa.P384.signApi.name])
      code := (cfgOf (pack h.law h.inv (Proof.P384.combOk7 h.law) c)).sign
      consts := Impl.Ecdsa.AArch64.p384.combConsts
      contract := Spec.Ecdsa.Rfc6979.P384Sha384.inst.signContract
        (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p384.combConsts) 256
      stack := 256
      verified := sign_verified h.law h.inv (Proof.P384.combOk7 h.law) c
      spSafe := Code.all_of_forall (fun _ => rfl) _
      features := c.features }]

end VG.Generic.MdHash.P384.AArch64.EcdsaP384Sha384
