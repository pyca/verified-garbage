module

public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreStoreTiming
import VerifiedGarbage.Proof.Dsa.X86.ValidationBlocksTiming
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Dsa.X86.StageMinus

/-! ### `Dsa.X86.MinusTiming`, which only this module used -/

section

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
  refine RelCT.seq (coreLoad_relCT _ _ _ _ base size hz) ?_
  exact (RelCT.seq (modulusMinus_relCT _ amount) (coreStore_workspace_relCT len output)).mono
    (fun _ _ h => taint.le_sound
      (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
    (fun _ _ h => h)

end VG.Proof.Dsa.X86

end

end


/-! # Public modulus decrements retain the call layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callMinusP_relCT (L : CallLayout) (output : Nat) (P : CallOperand L (.input .p) L.pLen)
    (ho : r ≤ output) (hb : output + L.pLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Validate.minus L.pLen .p 1 output) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · exact (validateMinus_relCT L.pLen 1 output .p L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.1.moduli.scr, H.2.moduli.scr, H.pointer P⟩) (fun _ _ h => h)
  · intro s R
    exact WP.mono (stageMinusP_ok R.moduli (by have := R.moduli.pLarge; omega_using [this]) ho hb)
      fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

theorem callMinusQ_relCT (L : CallLayout) (output : Nat) (Q : CallOperand L (.input .q) L.qLen)
    (ho : r ≤ output) (hb : output + L.qLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Validate.minus L.qLen .q 2 output) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · exact (validateMinus_relCT L.qLen 2 output .q L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.1.moduli.scr, H.2.moduli.scr, H.pointer Q⟩) (fun _ _ h => h)
  · intro s R
    exact WP.mono (stageMinusQ_ok R.moduli (by have := R.moduli.qLarge; omega_using [this]) ho hb)
      fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

end VG.Proof.Dsa.X86
