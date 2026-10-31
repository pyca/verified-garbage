module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP512r1Sha512
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP512r1 with HMAC-SHA-512 on AArch64 -/

@[expose] public section

namespace VG.Generic.MdHash.BrainpoolP512r1.AArch64.EcdsaBrainpoolP512r1Sha512

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP512r1Sha512 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP512r1.curve) :
    List Artifact :=
  match v.sha512 with
  | none => []
  | some c => [
    Spec.Ecdsa.Rfc6979.BrainpoolP512r1Sha512.signApi.artifact AArch64.target {
      suffix := c.suffix
      code := (cfgOf (pack h.law h.inv c)).sign
      stack := 320
      verified := sign_verified h.law h.inv c
      features := c.features }]

end VG.Generic.MdHash.BrainpoolP512r1.AArch64.EcdsaBrainpoolP512r1Sha512
