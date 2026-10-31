module

public import VerifiedGarbage.Proof.Ed448.X86.VerifyVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 verification's equation on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Ed448VerifyEquation.X86

def artifacts : List Artifact := [
  Spec.Ed448.verifyEquationApi.artifact X86.target {
    code := Impl.Ed448.X86.verifyEquation
    stack := 20
    verified := Proof.Ed448.X86.verifyEquation_verified Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok }]

end VG.Artifacts.Ed448VerifyEquation.X86
