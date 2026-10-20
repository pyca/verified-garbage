module

public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Impl.Rsa.X86.Div
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The division schedule is independent of all array contents -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.Impl.Rsa.X86.Div VG.Proof.Mont.X86.Dynamic

def divisionTaint : VG.X86.Taint.T := workspaceTaint false

def divisionHint : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint divisionTaint (Code.erase (code 1 0 0 0 0))

theorem division_check (n quotient rem divisor tmp : Nat) :
    (VG.Taint.check taint divisionTaint (code n quotient rem divisor tmp) divisionHint).isSome = true := by
  rw [check_of_erase_eq (code n quotient rem divisor tmp) (code 1 0 0 0 0)
    divisionTaint divisionHint rfl rfl rfl]
  rfl

theorem code_constantTime (n quotient rem divisor tmp : Nat) :
    ConstantTime isa (fun _ => True) (VG.X86.Taint.Agree divisionTaint)
      (code n quotient rem divisor tmp) := by
  exact VG.Taint.constantTime (A := taint) divisionTaint (fun _ _ _ _ h => h)
    (hc := divisionHint) (division_check n quotient rem divisor tmp)
end VG.Proof.Rsa.X86.Div
