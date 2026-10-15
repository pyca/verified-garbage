module

public import VerifiedGarbage.Proof.Dsa.X86.PointerTiming

/-! # Constant-time modulus loading and context initialization -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem contextSetup_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (contextSetup n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  have pref : taint.checkBlock (workspaceTaint false)
      (setupInverse (slot n 0) 0 ++ one n (slot n 3)) = some (zeroTaint false) := by
    rw [exponent_check_append taint (workspaceTaint false), setupInverse_taint false]
    exact one_taint false n (slot n 3)
  exact checkedProgramChange (σ := workspaceTaint false) (τ' := counterEndTaint)
    (hint := .seq (workspaceTaint false) (.block []) powerHint)
    (exponent_check_seq taint pref (show taint.le (workspaceTaint false) (zeroTaint false) = true from rfl)
      (powerTwo_check (contextMod n) (slot n 2) (slot n 4) (128 * n))) rfl

theorem coreSetup_relCT (len : Nat) (modulus : Field) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      pointerValue base s (.input modulus) = pointerValue base t (.input modulus))
      (Core.setup len modulus) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Core.setup
  refine RelCT.seq (coreLoad_relCT _ _ _ _ base size hz) ?_
  exact (contextSetup_relCT _).mono
    (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
    (fun _ _ h => h)

end VG.Proof.Dsa.X86
