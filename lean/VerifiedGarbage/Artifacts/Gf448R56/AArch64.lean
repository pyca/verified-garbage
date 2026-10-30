module

public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Verified
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.MulVerified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! # A power and the product in curve448's field, in radix `2^56`, on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Gf448R56.AArch64

open VG.Spec.X448.Field56 VG.Impl.Ed448.AArch64.Point56 VG.Proof.Ed448.AArch64.Point56

def artifacts : List Artifact := [
  powApi.artifact AArch64.target {
    code := powFn
    verified := powFn_verified
    stack := 0 },
  mulApi.artifact AArch64.target {
    code := mulFn
    verified := mulFn_verified
    stack := 0 }]

end VG.Artifacts.Gf448R56.AArch64
