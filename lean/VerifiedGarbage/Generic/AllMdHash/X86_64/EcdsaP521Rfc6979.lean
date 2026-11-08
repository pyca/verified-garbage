module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P521Adx
public import VerifiedGarbage.Proof.P521.Comb7
public import VerifiedGarbage.TCB.X86_64.Print
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.P521.X86_64.Law

/-! # Deterministic ECDSA (RFC 6979) over P-521 on x86-64, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.AllMdHash.X86_64.EcdsaP521Rfc6979

open VG.Proof.P521.X86_64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT stackT OK p521Of p521T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)

/-- The signature with P-521's multiplication with BMI2 and ADX (`adx`,
`_adx`) or not, and the tables of `vs`. -/
def withMul (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P521.curve) (vs : List Proof.Pbkdf2.Md.X86_64.MdHash)
    (hv : OK vs ∧ "VG_P521_COMB" ∉ names vs) (adx : Bool) : Artifact :=
  Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact X86_64.target {
    suffix := if adx then "_adx" else ""
    tables := [("hmac", tables vs)]
    code := signCodeT (p521Of adx h.law (Proof.P521.combOk7 h.law) h.inv) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs
    stack := stackT
    verified := p521T_verified adx h.law (Proof.P521.combOk7 h.law) h.inv vs hv
    spSafe := signCode_sp _ _ _
    features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

def artifacts (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if hv : OK vs ∧ "VG_P521_COMB" ∉ names vs then [withMul hasLaw vs hv false, withMul hasLaw vs hv true] else []

end VG.Generic.AllMdHash.X86_64.EcdsaP521Rfc6979
