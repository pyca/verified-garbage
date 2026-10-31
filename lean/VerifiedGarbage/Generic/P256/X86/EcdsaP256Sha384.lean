module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Sha384
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Deterministic ECDSA (RFC 6979) over P-256 with HMAC-SHA-384 on x86 (32-bit) -/

@[expose] public section

namespace VG.Generic.P256.X86.EcdsaP256Sha384

open VG.Proof.Ecdsa.Rfc6979.X86 (cfgOf sign_spSafe)
open VG.Proof.Ecdsa.Rfc6979.X86.Sha384 (pack sign_verified)

def artifacts (h : Proof.Weierstrass.X86.Inv.HasLawInvOrd Spec.P256.curve) : List Artifact := [
  Spec.Ecdsa.Rfc6979.P256Sha384.signApi.artifact X86.target {
    code := (cfgOf (pack h.law h.inv)).sign
    consts := Impl.Ecdsa.X86.p256Comb.combConsts
    stack := 272
    verified := sign_verified h.law h.inv
    spSafe := sign_spSafe (pack h.law h.inv) }]

end VG.Generic.P256.X86.EcdsaP256Sha384
