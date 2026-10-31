module

public import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P224Sha224
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-224 with HMAC-SHA-224 on AArch64 -/

@[expose] public section

namespace VG.Generic.MdHash.P224.AArch64.EcdsaP224Sha224

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.AArch64.P224Sha224 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve) :
    List Artifact :=
  match v.sha224 with
  | none => []
  | some c => [
    Spec.Ecdsa.Rfc6979.P224Sha224.signApi.artifact AArch64.target {
      suffix := c.suffix
      code := (cfgOf (pack h.law h.inv (Proof.P224.combOk7 h.law) c)).sign
      consts := Impl.Ecdsa.AArch64.p224.combConsts
      stack := 256
      verified := sign_verified h.law h.inv (Proof.P224.combOk7 h.law) c
      features := c.features }]

end VG.Generic.MdHash.P224.AArch64.EcdsaP224Sha224
