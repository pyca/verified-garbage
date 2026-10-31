module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P521.Comb7
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P521Sha512
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-521 with HMAC-SHA-512 on AArch64 -/

@[expose] public section

namespace VG.Generic.MdHash.P521.AArch64.EcdsaP521Sha512

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.AArch64.P521Sha512 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P521.curve) :
    List Artifact :=
  match v.sha512 with
  | none => []
  | some c => [
    Spec.Ecdsa.Rfc6979.P521Sha512.signApi.artifact AArch64.target {
      suffix := c.suffix
      code := (cfgOf (pack h.law h.inv (Proof.P521.combOk7 h.law) c)).sign
      consts := Impl.Ecdsa.AArch64.p521.combConsts
      stack := 400
      verified := sign_verified h.law h.inv (Proof.P521.combOk7 h.law) c
      features := c.features }]

end VG.Generic.MdHash.P521.AArch64.EcdsaP521Sha512
