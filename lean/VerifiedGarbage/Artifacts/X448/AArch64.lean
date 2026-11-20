module

public import VerifiedGarbage.Impl.X448.AArch64.Fn
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Verified
public import VerifiedGarbage.Proof.X448.AArch64.Base.Verified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.X448.AArch64.Exchange
public import VerifiedGarbage.Proof.X448.AArch64.ExchangeResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.X448.AArch64.BaseScrub
public import VerifiedGarbage.TCB.AArch64.Print

/-! # X448 (RFC 7748) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.X448.AArch64

def artifacts : List Artifact := [
  Spec.X448.exchangeApi.artifact AArch64.target {
    code := Impl.X448.AArch64.Fn.exchange
    verified := .scrubbed Proof.X448.AArch64.ExchangeResidue.exchangeCode_scrubbed },
  Spec.X448.x448BaseApi.artifact AArch64.target {
    code := Impl.X448.AArch64.Base.Fn.x448Base
    verified := .scrubbed Proof.X448.AArch64.BaseScrub.x448Base }]

end VG.Artifacts.X448.AArch64
