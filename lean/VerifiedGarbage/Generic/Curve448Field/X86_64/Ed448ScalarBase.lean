module

public import VerifiedGarbage.Proof.Ed448.X86_64.VariantVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 base-point multiplication on x86-64 -/

@[expose] public section

namespace VG.Generic.Curve448Field.X86_64.Ed448ScalarBase

def artifacts (v : Impl.Ed448.X86_64.FieldVariant) : List Artifact := [
  Spec.Ed448.scalarBaseApi.artifact X86_64.target {
    suffix := v.suffix
    features := v.features
    code := Impl.Ed448.X86_64.scalarBaseFor v
    stack := 8
    verified := Proof.Ed448.X86_64.scalarBaseFor_verified v Proof.Ed448.baseLadder_ok }]

end VG.Generic.Curve448Field.X86_64.Ed448ScalarBase
