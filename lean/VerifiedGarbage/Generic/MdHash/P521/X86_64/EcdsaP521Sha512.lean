import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.P521.Comb7
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P521Sha512

/-!
# Deterministic ECDSA (RFC 6979) over P-521 with HMAC-SHA-512 on x86-64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_p521_sha512_sign`, calling
HMAC-SHA-512's `init` and `finalize` and SHA-512's streaming `update` made
with the variant's SHA-512 compression function, and `vg_ecdsa_p521_sign`,
is emitted for every SHA-512 variant carried by `MdHash.sha512`, named with
its suffix (e.g. `vg_ecdsa_p521_sha512_sign_avx2`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 384 bytes: a 360-byte frame (P-384's 216 bytes, and 144 for
the candidate and the digest shifted into 66 bytes), and the 24 bytes below
it that the calls use (`vg_ecdsa_p521_sign` only its return address).

It reads the comb's tables of `vg_ecdsa_p521_sign`, the static `VG_P521_COMB`.
It is generic over P-521's group law and inversions `h` too, the variant
`Variants/P521/X86_64/Law.lean`.
-/

namespace VG.Generic.MdHash.P521.X86_64.EcdsaP521Sha512

open VG.Proof.Ecdsa.Rfc6979.X86_64 (cfgOf sign_spSafe signNotesWide)
open VG.Proof.Ecdsa.Rfc6979.X86_64.P521Sha512 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P521.curve) :
    List Artifact :=
  match v.sha512 with
  | none => []
  | some c => [
    { Spec.Ecdsa.Rfc6979.P521Sha512.signApi with
      name := Spec.Ecdsa.Rfc6979.P521Sha512.signApi.name ++ c.suffix
      target := X86_64.target
      doc := Spec.Ecdsa.Rfc6979.P521Sha512.signApi.doc
        (notes := [signNotesWide (cfgOf (pack h.law (Proof.P521.combOk7 h.law) h.inv c)).H 66 521 64
          Spec.Ecdsa.P521.signApi.name])
      code := (cfgOf (pack h.law (Proof.P521.combOk7 h.law) h.inv c)).sign
      consts := Impl.Ecdsa.X86_64.p521.combConsts
      contract := Spec.Ecdsa.Rfc6979.P521Sha512.inst.signContract
        (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p521.combConsts) 384
      stack := 384
      verified := sign_verified h.law (Proof.P521.combOk7 h.law) h.inv c
      spSafe := sign_spSafe (pack h.law (Proof.P521.combOk7 h.law) h.inv c)
      features := c.features }]

end VG.Generic.MdHash.P521.X86_64.EcdsaP521Sha512
