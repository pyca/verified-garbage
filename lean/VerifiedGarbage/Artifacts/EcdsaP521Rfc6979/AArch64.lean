module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P521.Comb7
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P521
public import VerifiedGarbage.TCB.AArch64.Print
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.P521.AArch64.Law
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # Deterministic ECDSA (RFC 6979) over P-521 on AArch64, with HMAC as a table -/

@[expose] public section

namespace VG.Artifacts.EcdsaP521Rfc6979.AArch64

open VG.Proof.P521.AArch64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCodeT stackT OK p521 p521T_verified)
open VG.Proof.HmacTable.AArch64 (tables names)

def artifactsFor (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if hv : OK vs ∧ "VG_P521_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p521SignApi.artifact AArch64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (p521 hasLaw.law hasLaw.inv (Proof.P521.combOk7 hasLaw.law)) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs
      stack := stackT
      verified := p521T_verified hasLaw.law hasLaw.inv (Proof.P521.combOk7 hasLaw.law) vs hv
      features := [] }]
  else []

def artifacts : List Artifact :=
  artifactsFor VG.Proof.Variants.MdHash.AArch64.variants

end VG.Artifacts.EcdsaP521Rfc6979.AArch64
