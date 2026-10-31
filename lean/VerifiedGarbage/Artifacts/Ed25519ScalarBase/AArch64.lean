module

public import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Complete unsigned scalar multiplication by the Ed25519 base point -/

@[expose] public section

namespace VG.Artifacts.Ed25519ScalarBase.AArch64

def artifacts : List Artifact := [
  Spec.Ed25519.scalarBaseApi.artifact AArch64.target {
    consts := Impl.Ed25519.AArch64.combConsts
    code := Impl.Ed25519.AArch64.scalarBase
    verified := Proof.Ed25519.AArch64.scalarBase_verified }]

end VG.Artifacts.Ed25519ScalarBase.AArch64
