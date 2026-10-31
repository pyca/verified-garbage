module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP384r1Sha384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP384r1 with HMAC-SHA-384 on AArch64 -/

@[expose] public section

namespace VG.Generic.MdHash.BrainpoolP384r1.AArch64.EcdsaBrainpoolP384r1Sha384

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP384r1Sha384 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP384r1.curve) :
    List Artifact :=
  match v.sha384 with
  | none => []
  | some c => [
    Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.signApi.artifact AArch64.target {
      suffix := c.suffix
      code := (cfgOf (pack h.law h.inv c)).sign
      stack := 256
      verified := sign_verified h.law h.inv c
      features := c.features }]

end VG.Generic.MdHash.BrainpoolP384r1.AArch64.EcdsaBrainpoolP384r1Sha384
