module
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

import VerifiedGarbage.Proof.Dsa.X86.CoreSetupTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreStoreTiming
import VerifiedGarbage.Proof.Dsa.X86.ValidationBlocksTiming

/-! # Constant-time formation of the fixed public modulus decrements -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem validateMinus_relCT (len amount output : Nat) (modulus : Field) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input modulus) = pointerValue base t (.input modulus))
      (Validate.minus len modulus amount output) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold Validate.minus
  dsimp only
  apply RelCT.seq (coreSetup_relCT len modulus base size hz)
  exact RelCT.seq (modulusMinus_relCT _ amount) (coreStore_workspace_relCT len output)

end VG.Proof.Dsa.X86
