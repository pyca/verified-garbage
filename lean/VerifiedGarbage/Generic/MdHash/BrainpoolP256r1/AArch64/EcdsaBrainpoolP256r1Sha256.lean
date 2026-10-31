module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP256r1Sha256
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over brainpoolP256r1 with HMAC-SHA-256 on AArch64 -/

@[expose] public section

namespace VG.Generic.MdHash.BrainpoolP256r1.AArch64.EcdsaBrainpoolP256r1Sha256

open VG.Proof.Ecdsa.Rfc6979.AArch64 (cfgOf)
open VG.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP256r1Sha256 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP256r1.curve) :
    List Artifact :=
  match v.sha256 with
  | none => []
  | some c => [
    Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.signApi.artifact AArch64.target {
      suffix := c.suffix
      code := (cfgOf (pack h.law h.inv c)).sign
      consts := Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg.combConsts
      stack := 256
      verified := sign_verified h.law h.inv c
      features := c.features }]

end VG.Generic.MdHash.BrainpoolP256r1.AArch64.EcdsaBrainpoolP256r1Sha256
