module

public import VerifiedGarbage.Proof.Ed448.AArch64.BaseVerified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 base-point multiplication on AArch64

The signature and documentation come from the reviewed Ed448 API.
-/

@[expose] public section

namespace VG.Artifacts.Ed448ScalarBase.AArch64

def artifacts : List Artifact := [
  Spec.Ed448.scalarBaseApi.artifact AArch64.target {
    consts := Impl.X448.AArch64.Base.combConsts
    code := Impl.Ed448.AArch64.scalarBase
    verified := Proof.Ed448.AArch64.scalarBase_verified }]

end VG.Artifacts.Ed448ScalarBase.AArch64
