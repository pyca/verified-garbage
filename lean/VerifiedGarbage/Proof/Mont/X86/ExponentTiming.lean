module
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

import VerifiedGarbage.Proof.Mont.X86.ExponentTimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Secret-independent branches and addresses for modular exponentiation -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

theorem exponent_check_seq {M : ISA} (A : VG.Taint M) {τ mid u v : A.T}
    {a b : Prog M} {ha hb : VG.Taint.Hint A.T}
    (h₁ : VG.Taint.check A τ a ha = some u) (hl : A.le mid u = true)
    (h₂ : VG.Taint.check A mid b hb = some v) :
    VG.Taint.check A τ (.seq a b) (.seq mid ha hb) = some v := by
  change (VG.Taint.check A τ a ha).bind _ = _
  rw [h₁, Option.bind_some, hl, ite_eq_left rfl, h₂]

def shiftDownHint : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (shiftDown 2 0))

/-- After the shift: the loop's pointer, and the zero shifted into the top word. -/
def shiftDownTaint : VG.X86.Taint.T := { regs := .ofList [.edi, .ebp, .eax, .esi], flags := false }

theorem shiftDown_check (k out : Nat) :
    VG.Taint.check taint (workspaceTaint true) (shiftDown k out) shiftDownHint = some shiftDownTaint :=
  (check_of_erase_eq (shiftDown k out) (shiftDown 2 0) (workspaceTaint true) shiftDownHint
    rfl rfl rfl).trans rfl

def counterEndTaint : VG.X86.Taint.T := { regs := .ofList [.edi, .esi], flags := true }

end VG.Proof.Mont.X86.Dynamic
