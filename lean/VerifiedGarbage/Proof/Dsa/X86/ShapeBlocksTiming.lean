module

import VerifiedGarbage.Proof.Dsa.X86.ValidationBlocksTiming
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
public import VerifiedGarbage.Impl.Dsa.X86.Shape
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Fixed-address shape masks and digest clamping -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem widthMask_relCT (n a tmp bits : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (widthMask n a tmp bits)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold widthMask
  refine RelCT.seq (lessThanConstant_relCT n a tmp _) ?_
  refine RelCT.seq (checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl) ?_
  split
  · exact RelCT.seq (lessThanConstant_relCT n a tmp _) (checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl)
  · exact checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl

theorem optionalWidth_relCT (n a tmp bits : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (optionalWidth n a tmp bits)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold optionalWidth
  split
  · exact widthMask_relCT n a tmp bits
  · exact checkedBlockInvariant (τ' := { workspaceTaint false with regs := .ofList [.edi, .edx] }) rfl rfl

theorem saveWidth_relCT (n bits output : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (Shape.saveWidth n bits output)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Shape.saveWidth
  refine RelCT.seq (optionalWidth_relCT n _ _ bits) (checkedBlockInvariant (τ' := workspaceTaint false) ?_ rfl)
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  change taint.checkBlock (workspaceTaint false) [.store (sc 0) .edx] = _
  rfl

theorem threeWidths_relCT (n a b c output : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (Shape.threeWidths n a b c output)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (saveWidth_relCT n a output) (RelCT.seq (saveWidth_relCT n b (output + 4))
    (saveWidth_relCT n c (output + 8)))

theorem loadWidths_relCT (len a b c output : Nat) (modulus : VG.Impl.Dsa.Layout.Field) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => VG.Proof.Mont.X86.Scr s base size ∧ VG.Proof.Mont.X86.Scr t base size ∧
      pointerValue base s (.input modulus) = pointerValue base t (.input modulus))
      (Shape.loadWidths len modulus a b c output) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Shape.loadWidths
  exact RelCT.seq (coreLoad_relCT _ len _ (.input modulus) base size hz)
    ((threeWidths_relCT _ a b c output).mono (fun _ _ h => taint.le_sound
      (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h) (fun _ _ h => h))

theorem saveParity_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block (Shape.saveParity n))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply checkedBlockInvariant (τ' := workspaceTaint false) ?_ rfl
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  change taint.checkBlock (workspaceTaint false) [.mov .eax (.mem (sc 0)), .store (sc 0) .eax] = _
  rfl

theorem parity_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block (Shape.parity n))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply checkedBlockInvariant (τ' := workspaceTaint false) ?_ rfl
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
  change taint.checkBlock (workspaceTaint false)
    [.mov .edx (.mem (sc 0)), .alu .and .edx (.mem (sc 0)), .alu .and .edx (.imm 0),
      .mov .eax (.imm 0), .alu .sub .eax (.reg .edx), .store (sc 0) .eax] = _
  rfl

theorem combine_relCT :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block Shape.combine)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl

theorem digestPrefix_relCT :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) Shape.digestPrefix
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  checkedBlockInvariant (τ' := workspaceTaint false) rfl rfl

end VG.Proof.Dsa.X86
