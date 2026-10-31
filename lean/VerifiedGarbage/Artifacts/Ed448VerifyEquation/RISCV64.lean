module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed448.RISCV64.VVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 verification's equation on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed448VerifyEquation.RISCV64

def artifacts : List Artifact := [
  Spec.Ed448.verifyEquationApi.artifact RISCV64.target {
    code := Impl.Ed448.RISCV64.verifyEquation
    verified := Proof.Ed448.RISCV64.verifyEquation_verified Proof.Ed448.recover_ok Proof.Ed448.verifyEq4_ok }]

end VG.Artifacts.Ed448VerifyEquation.RISCV64
