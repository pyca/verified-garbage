import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.P521.Comb7
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P521Sha512

/-!
# Deterministic ECDSA (RFC 6979) over P-521 with HMAC-SHA-512 on AArch64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_p521_sha512_sign`, calling
HMAC-SHA-512's `init` and `finalize` and SHA-512's streaming `update` made
with the variant's SHA-512 compression function, and `vg_ecdsa_p521_sign`,
is emitted for every SHA-512 variant carried by `MdHash.sha512`, named with
its suffix (e.g. `vg_ecdsa_p521_sha512_sign_sha3`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 400 bytes: 16 saving `x30`, a 368-byte frame (P-384's 224
bytes, and 144 for the candidate and the digest shifted into 66 bytes), and
the 16 bytes below it that HMAC's functions use (`vg_ecdsa_p521_sign` uses
none).

It is generic over P-521's group law `h` too, the variant
`Variants/P521/AArch64/Law.lean`.
-/

namespace VG.Generic.MdHash.P521.AArch64.EcdsaP521Sha512

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf signNotesWide)
open VG.Proof.Ecdsa.Rfc6979.AArch64.P521Sha512 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P521.curve) :
    List Artifact :=
  match v.sha512 with
  | none => []
  | some c => [
    { Spec.Ecdsa.Rfc6979.P521Sha512.signApi with
      name := Spec.Ecdsa.Rfc6979.P521Sha512.signApi.name ++ c.suffix
      target := AArch64.target
      doc := Spec.Ecdsa.Rfc6979.P521Sha512.signApi.doc
        (notes := [signNotesWide (cfgOf (pack h.law h.inv (Proof.P521.combOk7 h.law) c)).H 66 521 64
          Spec.Ecdsa.P521.signApi.name])
      code := (cfgOf (pack h.law h.inv (Proof.P521.combOk7 h.law) c)).sign
      consts := Impl.Ecdsa.AArch64.p521.combConsts
      contract := Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract
        (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p521.combConsts) 400
      stack := 400
      verified := sign_verified h.law h.inv (Proof.P521.combOk7 h.law) c
      spSafe := Code.all_of_forall (fun _ => rfl) _
      features := c.features }]

end VG.Generic.MdHash.P521.AArch64.EcdsaP521Sha512
