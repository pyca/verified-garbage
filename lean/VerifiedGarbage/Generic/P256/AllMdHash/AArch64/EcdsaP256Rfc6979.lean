module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P256.Comb7
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P256
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-! # Deterministic ECDSA (RFC 6979) over P-256 on AArch64, with HMAC as a table -/

@[expose] public section

namespace VG.Generic.P256.AllMdHash.AArch64.EcdsaP256Rfc6979

open VG.Proof.Ecdsa.Rfc6979.AArch64 (signCodeT stackT OK p256 p256T_verified)
open VG.Proof.HmacTable.AArch64 (tables names)

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvToMOrd Spec.P256.curve)
    (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if hv : OK vs ∧ "VG_P256_COMB" ∉ names vs then [
    Spec.Ecdsa.Rfc6979.Curves.p256SignApi.artifact AArch64.target {
      suffix := ""
      tables := [("hmac", tables vs)]
      code := signCodeT (p256 h.law h.inv (Proof.P256.combOk7 h.law)) Spec.Ecdsa.Rfc6979.Curves.p256.tries vs
      consts := Impl.Ecdsa.AArch64.p256.combConsts
      stack := stackT
      verified := p256T_verified h.law h.inv (Proof.P256.combOk7 h.law) vs hv
      features := [] }]
  else []

end VG.Generic.P256.AllMdHash.AArch64.EcdsaP256Rfc6979
