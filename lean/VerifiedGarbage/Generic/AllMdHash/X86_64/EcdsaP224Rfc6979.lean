module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P224
public import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.TCB.X86_64.Print
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.P224.X86_64.Law

/-! # Deterministic ECDSA (RFC 6979) over P-224 on x86-64, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.AllMdHash.X86_64.EcdsaP224Rfc6979

open VG.Proof.P224.X86_64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.X86_64 (signCodeT stackT OK p224 p224T_verified signCode_sp)
open VG.Proof.HmacTable.X86_64 (tables names)

def artifacts (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if hv : OK vs ∧ "VG_P224_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact X86_64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (p224 hasLaw.law (Proof.P224.combOk7 hasLaw.law) hasLaw.inv) Spec.Ecdsa.Rfc6979.Curves.p224.tries vs
      stack := stackT
      verified := p224T_verified hasLaw.law (Proof.P224.combOk7 hasLaw.law) hasLaw.inv vs hv
      spSafe := signCode_sp _ _ _
      features := [] }]
  else []

end VG.Generic.AllMdHash.X86_64.EcdsaP224Rfc6979
