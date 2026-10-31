module

public import VerifiedGarbage.Proof.Ed448.X86.BaseVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed448.X86.BaseLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 base-point multiplication on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Ed448ScalarBase.X86

def artifacts : List Artifact := [
  Spec.Ed448.scalarBaseApi.artifact X86.target {
    code := Impl.Ed448.X86.scalarBase
    stack := 20
    verified := Proof.Ed448.X86.scalarBase_verified Proof.Ed448.baseLadder_ok }]

end VG.Artifacts.Ed448ScalarBase.X86
