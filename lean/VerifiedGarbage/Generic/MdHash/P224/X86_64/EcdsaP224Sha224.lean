module

public import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P224Sha224
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified

/-! # Deterministic ECDSA (RFC 6979) over P-224 with HMAC-SHA-224 on x86-64 -/

@[expose] public section

namespace VG.Generic.MdHash.P224.X86_64.EcdsaP224Sha224

open VG.Proof.Ecdsa.Rfc6979.X86_64 (cfgOf sign_spSafe)
open VG.Proof.Ecdsa.Rfc6979.X86_64.P224Sha224 (pack sign_verified)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) :
    List Artifact :=
  match v.sha224 with
  | none => []
  | some c => [
    Spec.Ecdsa.Rfc6979.P224Sha224.signApi.artifact X86_64.target {
      suffix := c.suffix
      code := (cfgOf (pack h.law (Proof.P224.combOk7 h.law) h.inv c)).sign
      consts := Impl.Ecdsa.X86_64.p224.combConsts
      stack := 240
      verified := sign_verified h.law (Proof.P224.combOk7 h.law) h.inv c
      spSafe := sign_spSafe (pack h.law (Proof.P224.combOk7 h.law) h.inv c)
      features := c.features }]

end VG.Generic.MdHash.P224.X86_64.EcdsaP224Sha224
