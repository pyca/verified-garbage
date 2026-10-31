module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
public import VerifiedGarbage.Proof.P256.Comb7
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Sha384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-384 on AArch64 -/

@[expose] public section

namespace VG.Generic.MdHash.P256.AArch64.EcdsaP256Sha384

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.AArch64.Sha384 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (h : Proof.Weierstrass.AArch64.HasLawInvToMOrd Spec.P256.curve) :
    List Artifact :=
  match v.sha384 with
  | none => []
  | some c => [
    Spec.Ecdsa.Rfc6979.P256Sha384.signApi.artifact AArch64.target {
      suffix := c.suffix
      code := (cfgOf (pack h.law h.inv (Proof.P256.combOk7 h.law) c)).sign
      consts := Impl.Ecdsa.AArch64.p256.combConsts
      stack := 256
      verified := sign_verified h.law h.inv (Proof.P256.combOk7 h.law) c
      features := c.features }]

end VG.Generic.MdHash.P256.AArch64.EcdsaP256Sha384
