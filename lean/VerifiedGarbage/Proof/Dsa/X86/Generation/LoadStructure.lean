module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Dsa.X86.Bytes
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! # Component loads preserve the stack pointer used by the search frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86 VG.Impl.Mont.X86.Dynamic

theorem loadComponent_noSp (len n out : Nat) : NoSp (loadComponent len n out) := by
  apply NoSp.of_all
  unfold loadComponent zeroPad
  split
  · have cases : 2 * n - len / 4 = 0 ∨ 2 * n - len / 4 = 1 ∨ 2 * n - len / 4 = 2 ∨
        2 * n - len / 4 = 3 ∨ 2 * n - len / 4 = 4 := by omega
    rcases cases with h | h | h | h | h <;> rw [h] <;> rfl
  · rfl
end VG.Proof.Dsa.X86.Generation
