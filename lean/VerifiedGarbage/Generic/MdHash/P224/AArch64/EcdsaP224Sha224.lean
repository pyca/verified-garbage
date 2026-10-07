import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.P224.Comb7
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P224Sha224

/-!
# Deterministic ECDSA (RFC 6979) over P-224 with HMAC-SHA-224 on AArch64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_p224_sha224_sign`, calling
HMAC-SHA-224's `init` and `finalize` and SHA-256's streaming `update` made
with the variant's SHA-256 compression function, and `vg_ecdsa_p224_sign`,
is emitted for every SHA-224 variant carried by `MdHash.sha224`, named with
its suffix (e.g. `vg_ecdsa_p224_sha224_sign_sha2`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 256 bytes: 16 saving `x30`, a 224-byte frame, and the 16 bytes
below it that HMAC's functions use (`vg_ecdsa_p224_sign` uses none).

It is generic over P-224's group law and inversions `h` too, the variant
`Variants/P224/AArch64/Law.lean`.
-/

namespace VG.Generic.MdHash.P224.AArch64.EcdsaP224Sha224

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf signNotes)
open VG.Proof.Ecdsa.Rfc6979.AArch64.P224Sha224 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve) :
    List Artifact :=
  match v.sha224 with
  | none => []
  | some c => [
    { Spec.Ecdsa.Rfc6979.P224Sha224.signApi with
      name := Spec.Ecdsa.Rfc6979.P224Sha224.signApi.name ++ c.suffix
      target := AArch64.target
      doc := Spec.Ecdsa.Rfc6979.P224Sha224.signApi.doc
        (notes := [signNotes (cfgOf (pack h.law h.inv (Proof.P224.combOk7 h.law) c)).H 28 Spec.Ecdsa.P224.signApi.name])
      code := (cfgOf (pack h.law h.inv (Proof.P224.combOk7 h.law) c)).sign
      consts := Impl.Ecdsa.AArch64.p224.combConsts
      contract := Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract
        (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p224.combConsts) 256
      stack := 256
      verified := sign_verified h.law h.inv (Proof.P224.combOk7 h.law) c
      spSafe := Code.all_of_forall (fun _ => rfl) _
      features := c.features }]

end VG.Generic.MdHash.P224.AArch64.EcdsaP224Sha224
