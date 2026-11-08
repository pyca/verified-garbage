module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P256.Comb7
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P256
public import VerifiedGarbage.TCB.AArch64.Print
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.P256.AArch64.Law

/-! # Deterministic ECDSA (RFC 6979) over P-256 on AArch64, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.AllMdHash.AArch64.EcdsaP256Rfc6979

open VG.Proof.P256.AArch64 (hasLaw)
open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCodeT stackT OK p256 p256T_verified)
open VG.Proof.HmacTable.AArch64 (tables names)

def artifacts (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if hv : OK vs ∧ "VG_P256_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact AArch64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (p256 hasLaw.law hasLaw.inv (Proof.P256.combOk7 hasLaw.law)) Spec.Ecdsa.Rfc6979.Curves.p256.tries vs
      stack := stackT
      verified := p256T_verified hasLaw.law hasLaw.inv (Proof.P256.combOk7 hasLaw.law) vs hv
      features := [] }]
  else []

end VG.Generic.AllMdHash.AArch64.EcdsaP256Rfc6979
