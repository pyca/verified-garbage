module

public import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Verified
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! Whole-message Ed25519 verification follows every SHA-512 backend carried
by MdHash. The signature and contract come from the reviewed Ed25519 API. -/

@[expose] public section

namespace VG.Generic.MdHash.AArch64.Ed25519VerifyMessage

def artifacts (h : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  match h.sha512 with
  | none => []
  | some v => [
    Spec.Ed25519.verifyApi.artifact AArch64.target {
      suffix := v.suffix
      consts := Impl.Ed25519.AArch64.bConsts
      code := Impl.Ed25519.AArch64.VerifyMessage.code v.code v.suffix
      stack := 352
      verified := Proof.Ed25519.AArch64.VerifyMessage.verifyMessage_verified v
      features := v.features }]

end VG.Generic.MdHash.AArch64.Ed25519VerifyMessage
