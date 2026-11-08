module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P224
public import VerifiedGarbage.TCB.AArch64.Print
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.P224.AArch64.Law
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # Deterministic ECDSA (RFC 6979) over P-224 on AArch64, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaP224Rfc6979.AArch64

open VG.Proof.P224.AArch64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCodeT stackT OK p224 p224T_verified)
open VG.Proof.HmacTable.AArch64 (tables names)

def artifactsFor (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if hv : OK vs ∧ "VG_P224_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p224SignApi.artifact AArch64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (p224 hasLaw.law hasLaw.inv (Proof.P224.combOk7 hasLaw.law)) Spec.Ecdsa.Rfc6979.Curves.p224.tries vs
      stack := stackT
      verified := p224T_verified hasLaw.law hasLaw.inv (Proof.P224.combOk7 hasLaw.law) vs hv
      features := [] }]
  else []

def artifacts : List Artifact :=
  artifactsFor VG.Proof.Variants.MdHash.AArch64.variants

end VG.Artifacts.EcdsaP224Rfc6979.AArch64
