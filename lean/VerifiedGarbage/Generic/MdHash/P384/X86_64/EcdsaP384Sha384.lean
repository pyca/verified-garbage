import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P384Sha384

/-!
# Deterministic ECDSA (RFC 6979) over P-384 with HMAC-SHA-384 on x86-64

A generic file (see `TCB/Emit.lean`): `vg_ecdsa_p384_sha384_sign`, calling
HMAC-SHA-384's `init` and `finalize` and SHA-512's streaming `update` made
with the variant's SHA-512 compression function, and `vg_ecdsa_p384_sign`,
is emitted for every SHA-384 variant carried by `MdHash.sha384`, named with
its suffix (e.g. `vg_ecdsa_p384_sha384_sign_avx2`), and needs its CPU
features. Other hash functions emit no artifact here.

The stack is 240 bytes: a 216-byte frame, and the 24 bytes below it that the
calls use (`vg_ecdsa_p384_sign` only its return address).

It reads the comb's tables of `vg_ecdsa_p384_sign`, the static `VG_P384_COMB`.
It is generic over P-384's group law and inversions `h` too, the variant
`Variants/P384/X86_64/Law.lean`; and is emitted for each multiplication of
`vg_ecdsa_p384_sign`: the baseline's, and BMI2's and ADX's
(`vg_ecdsa_p384_sign_adx`, which the instance with the suffix `_adx` calls).
-/

namespace VG.Generic.MdHash.P384.X86_64.EcdsaP384Sha384

open VG.Proof.Ecdsa.Rfc6979.X86_64 (cfgOf sign_spSafe signNotes)
open VG.Proof.Ecdsa.Rfc6979.X86_64.P384Sha384 (pack sign_verified)

/-- The signature with the hash's compression function `c`, and P-384's
multiplication with BMI2 and ADX (`adx`, `_adx`, calling
`vg_ecdsa_p384_sign_adx`) or not. -/
def withMul (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P384.curve) (c : Proof.Sha512.X86_64.Compress)
    (adx : Bool) : Artifact :=
  { Spec.Ecdsa.Rfc6979.P384Sha384.signApi with
    name := Spec.Ecdsa.Rfc6979.P384Sha384.signApi.name ++ c.suffix ++ (if adx then "_adx" else "")
    target := X86_64.target
    doc := Spec.Ecdsa.Rfc6979.P384Sha384.signApi.doc
      (notes := [signNotes (cfgOf (pack adx h.law (Proof.P384.combOk7 h.law) h.inv c)).H 48
        (Spec.Ecdsa.P384.signApi.name ++ (if adx then "_adx" else ""))])
    code := (cfgOf (pack adx h.law (Proof.P384.combOk7 h.law) h.inv c)).sign
    consts := Impl.Ecdsa.X86_64.p384.combConsts
    contract := Spec.Ecdsa.Rfc6979.P384Sha384.inst.signContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p384.combConsts) 240
    stack := 240
    verified := sign_verified adx h.law (Proof.P384.combOk7 h.law) h.inv c
    spSafe := sign_spSafe (pack adx h.law (Proof.P384.combOk7 h.law) h.inv c)
    features := c.features ++ (if adx then ["bmi2", "adx", "avx", "avx2"] else []).filter (!c.features.contains ·) }

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P384.curve) :
    List Artifact :=
  match v.sha384 with
  | none => []
  | some c => [withMul h c false, withMul h c true]

end VG.Generic.MdHash.P384.X86_64.EcdsaP384Sha384
