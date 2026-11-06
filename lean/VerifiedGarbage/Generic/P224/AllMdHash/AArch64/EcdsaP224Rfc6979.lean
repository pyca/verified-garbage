module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P224
public import VerifiedGarbage.TCB.AArch64.Print
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-! # Deterministic ECDSA (RFC 6979) over P-224 on AArch64, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P224.AllMdHash.AArch64.EcdsaP224Rfc6979

open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCodeT stackT OK p224 p224T_verified)
open VG.Proof.HmacTable.AArch64 (tables names)

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve)
    (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if hv : OK vs ∧ "VG_P224_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact AArch64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (p224 h.law h.inv (Proof.P224.combOk7 h.law)) Spec.Ecdsa.Rfc6979.Curves.p224.tries vs
      stack := stackT
      verified := p224T_verified h.law h.inv (Proof.P224.combOk7 h.law) vs hv
      features := [] }]
  else []

end VG.Generic.P224.AllMdHash.AArch64.EcdsaP224Rfc6979
