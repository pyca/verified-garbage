module

import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Verified
import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
public import Init.Core
public import VerifiedGarbage.Impl.Mont.X86.StaticSquare
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Time
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint

/-! # The run-time Montgomery contract, using symmetric squares when inputs alias -/

@[expose] public section
namespace VG.Proof.Mont.X86.Rt
open VG VG.X86 VG.Impl.Mont.X86

theorem rt_correct (s : State) (h : (Spec.Rsa.MontMul.mulContract abi 0).pre s) :
    ∃ tr t, Exec isa Rt.body s tr t ∧ abiPreserved s t ∧ (Spec.Rsa.MontMul.mulContract abi 0).post s t := by
  simpa only [Rt.body] using StaticSquare.correct s h

theorem rt_constantTime :
    ConstantTime isa (Spec.Rsa.MontMul.mulContract abi 0).pre (Spec.Rsa.MontMul.mulContract abi 0).pub Rt.body := by
  simpa only [Rt.body] using StaticSquare.constantTime

theorem rt_verified : Verified target Rt.body (Spec.Rsa.MontMul.mulContract abi 0) :=
  ⟨rt_correct,rt_constantTime,rt_satisfiable⟩

end VG.Proof.Mont.X86.Rt
