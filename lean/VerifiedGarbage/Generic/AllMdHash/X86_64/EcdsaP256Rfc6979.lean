module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.P256.Comb7
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P256Adx
public import VerifiedGarbage.TCB.X86_64.Print
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.P256.X86_64.Law

/-! # Deterministic ECDSA (RFC 6979) over P-256 on x86-64, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.AllMdHash.X86_64.EcdsaP256Rfc6979

open VG.Proof.P256.X86_64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT stackT OK p256Of p256T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)

/-- The signature with P-256's multiplication with BMI2 and ADX (`adx`,
`_adx`, calling `vg_ecdsa_p256_sign_adx`) or not, and the tables of `vs`. -/
def withMul (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P256.curve) (vs : List Proof.Pbkdf2.Md.X86_64.MdHash)
    (hv : OK vs ∧ "VG_P256_COMB" ∉ names vs) (adx : Bool) : Artifact :=
  Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact X86_64.target {
    suffix := if adx then "_adx" else ""
    tables := [("hmac", tables vs)]
    code := signCodeT (p256Of adx h.law (Proof.P256.combOk7 h.law) h.inv) Spec.Ecdsa.Rfc6979.Curves.p256.tries vs
    stack := stackT
    verified := p256T_verified adx h.law (Proof.P256.combOk7 h.law) h.inv vs hv
    spSafe := signCode_sp _ _ _
    features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

def artifacts (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if hv : OK vs ∧ "VG_P256_COMB" ∉ names vs then [withMul hasLaw vs hv false, withMul hasLaw vs hv true] else []

end VG.Generic.AllMdHash.X86_64.EcdsaP256Rfc6979
