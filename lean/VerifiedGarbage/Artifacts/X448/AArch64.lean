module

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
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # X448 (RFC 7748) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.X448.AArch64

def artifacts : List Artifact := [
  Spec.X448.exchangeApi.artifact AArch64.target {
    code := Impl.Xdh.AArch64.exchange "vg_x448" Impl.X448.AArch64.Fast.x448 56
    stack := 16
    verified := Proof.X448.AArch64.Exchange.exchange_verified },
  Spec.X448.x448BaseApi.artifact AArch64.target {
    consts := Impl.X448.AArch64.Base.combConsts
    code := Impl.X448.AArch64.Base.x448Base
    verified := Proof.X448.AArch64.Base.x448Base_verified }]

end VG.Artifacts.X448.AArch64
