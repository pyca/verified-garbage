module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.P256.Comb7
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Sha384
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified

/-! # Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-384 on x86-64 -/

@[expose] public section

namespace VG.Generic.MdHash.P256.X86_64.EcdsaP256Sha384

open VG.Proof.Ecdsa.Rfc6979.X86_64 (cfgOf sign_spSafe)
open VG.Proof.Ecdsa.Rfc6979.X86_64.Sha384 (pack sign_verified)

/-- The signature with the hash's compression function `c`, and P-256's
multiplication with BMI2 and ADX (`adx`, `_adx`, calling `vg_ecdsa_p256_sign_adx`)
or not. -/
def withMul (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P256.curve) (c : Proof.Sha512.X86_64.Compress)
    (adx : Bool) :
    Artifact :=
  Spec.Ecdsa.Rfc6979.P256Sha384.signApi.artifact X86_64.target {
    suffix := c.suffix ++ (if adx then "_adx" else "")
    code := (cfgOf (pack adx h.law (Proof.P256.combOk7 h.law) h.inv c)).sign
    consts := Impl.Ecdsa.X86_64.p256.combConsts
    stack := 240
    verified := sign_verified adx h.law (Proof.P256.combOk7 h.law) h.inv c
    spSafe := sign_spSafe (pack adx h.law (Proof.P256.combOk7 h.law) h.inv c)
    features := c.features ++ (if adx then ["bmi2", "adx", "avx", "avx2"] else []).filter (!c.features.contains ·) }

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P256.curve) :
    List Artifact :=
  match v.sha384 with
  | none => []
  | some c => [withMul h c false, withMul h c true]

end VG.Generic.MdHash.P256.X86_64.EcdsaP256Sha384
