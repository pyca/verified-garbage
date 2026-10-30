module

public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Verified
public import VerifiedGarbage.Proof.Ed448.AArch64.CombBase
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448's point addition and doubling and its fixed-base comb, in radix `2^56`, on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Ed448R56.AArch64

open VG.Spec.Ed448.Point56 VG.Impl.Ed448.AArch64.Point56 VG.Proof.Ed448.AArch64.Point56

def artifacts : List Artifact := [
  addApi.artifact AArch64.target {
    code := addFn
    verified := addFn_verified
    stack := 0 },
  doubleApi.artifact AArch64.target {
    code := doubleFn
    verified := doubleFn_verified
    stack := 0 },
  Spec.Ed448.Comb56.combBaseApi.artifact AArch64.target {
    consts := VG.Impl.X448.AArch64.Base.combConsts
    code := VG.Impl.Ed448.AArch64.CombBase.combBaseFn
    verified := VG.Proof.Ed448.AArch64.CombBase.combBaseFn_verified
    stack := 0 }]

end VG.Artifacts.Ed448R56.AArch64
