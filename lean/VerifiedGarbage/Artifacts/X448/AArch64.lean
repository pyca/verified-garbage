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
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X448 (RFC 7748) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.X448.AArch64

def artifacts : List Artifact := [
  Spec.X448.x448Api.artifact AArch64.target {
    code := Impl.X448.AArch64.Fast.x448
    verified := Proof.X448.AArch64.Fast.x448_verified },
  Spec.X448.x448BaseApi.artifact AArch64.target {
    consts := Impl.X448.AArch64.Base.combConsts
    code := Impl.X448.AArch64.Base.x448Base
    verified := Proof.X448.AArch64.Base.x448Base_verified }]

end VG.Artifacts.X448.AArch64
