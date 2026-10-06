import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Sha256

/-!
# Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-256 on x86-64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_p256_sha256_sign`, calling
HMAC-SHA-256's `init` and `finalize` and SHA-256's streaming `update` made
with the variant's SHA-256 compression function, and `vg_ecdsa_p256_sign`,
is emitted for every SHA-256 variant carried by `MdHash.sha256`, named with
its suffix (e.g. `vg_ecdsa_p256_sha256_sign_shani`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 240 bytes: a 216-byte frame, and the 24 bytes below it that the
calls use (`vg_ecdsa_p256_sign` only its return address).

It reads the comb's tables of `vg_ecdsa_p256_sign`, the static `VG_P256_COMB`.
It is generic over P-256's group law and inversions `h` too, the variant
`Variants/P256/X86_64/Law.lean`; and is emitted for each multiplication of
`vg_ecdsa_p256_sign`: the baseline's, and BMI2's and ADX's
(`vg_ecdsa_p256_sign_adx`, which the instance with the suffix `_adx` calls).
-/

namespace VG.Generic.MdHash.P256.X86_64.EcdsaP256Sha256

open VG.Proof.Ecdsa.Rfc6979.X86_64 (cfgOf sign_spSafe signNotes)
open VG.Proof.Ecdsa.Rfc6979.X86_64.Sha256 (pack sign_verified)

/-- The signature with the hash's compression function `c`, and P-256's
multiplication with BMI2 and ADX (`adx`, `_adx`, calling `vg_ecdsa_p256_sign_adx`)
or not. -/
def withMul (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P256.curve) (c : Proof.Sha256.X86_64.Compress)
    (adx : Bool) :
    Artifact :=
  { Spec.Ecdsa.Rfc6979.P256Sha256.signApi with
    name := Spec.Ecdsa.Rfc6979.P256Sha256.signApi.name ++ c.suffix ++ (if adx then "_adx" else "")
    target := X86_64.target
    doc := Spec.Ecdsa.Rfc6979.P256Sha256.signApi.doc
      (notes := [signNotes (cfgOf (pack adx h.law (Proof.P256.combOk7 h.law) h.inv c)).H 32
        (Spec.Ecdsa.P256.signApi.name ++ (if adx then "_adx" else ""))])
    code := (cfgOf (pack adx h.law (Proof.P256.combOk7 h.law) h.inv c)).sign
    consts := Impl.Ecdsa.X86_64.p256.combConsts
    contract := Spec.Ecdsa.Rfc6979.P256Sha256.inst.signContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p256.combConsts) 240
    stack := 240
    verified := sign_verified adx h.law (Proof.P256.combOk7 h.law) h.inv c
    spSafe := sign_spSafe (pack adx h.law (Proof.P256.combOk7 h.law) h.inv c)
    features := c.features ++ (if adx then ["bmi2", "adx"] else []).filter (!c.features.contains ·) }

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P256.curve) :
    List Artifact :=
  match v.sha256 with
  | none => []
  | some c => [withMul h c false, withMul h c true]

end VG.Generic.MdHash.P256.X86_64.EcdsaP256Sha256
