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
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64

/-! # Ed25519 whole-message verification on AArch64, for each SHA-512 implementation -/

@[expose] public section

namespace VG.Artifacts.Ed25519VerifyMessage.AArch64

def artifactsFor (h : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  match h.sha512 with
  | none => []
  | some v => [
    Spec.Ed25519.verifyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Ed25519.AArch64.VerifyMessage.code v.code v.suffix
      stack := 352
      verified := Proof.Ed25519.AArch64.VerifyMessage.verifyMessage_verified v
      features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MdHash.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed25519VerifyMessage.AArch64
