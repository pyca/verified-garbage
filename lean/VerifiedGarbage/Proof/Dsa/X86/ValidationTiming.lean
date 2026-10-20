module
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

import VerifiedGarbage.Proof.Dsa.X86.RawInputsTiming
import VerifiedGarbage.Proof.Dsa.X86.ValidationBlocksTiming
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.ChecksTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Component validation does not branch or address memory on secret values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem forget_counter {s t : State} (H : VG.X86.Taint.Agree (workspaceTaint true) s t) :
    VG.X86.Taint.Agree (workspaceTaint false) s t := taint.le_sound (by rfl) H

theorem validateRange_relCT (len : Nat) (modulus : Field) (input : Pointer) (aboveOne : Bool)
    (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      OperandReady s base ((len + 7) / 8) (.input modulus) len ∧
      OperandReady t base ((len + 7) / 8) (.input modulus) len ∧
      pointerValue base s (.input modulus) = pointerValue base t (.input modulus) ∧
      pointerValue base s input = pointerValue base t input)
      (Validate.range len modulus input aboveOne) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Validate.range
  dsimp only
  apply RelCT.assoc
  apply RelCT.seq (rawInputs_relCT _ len len 0 5 (.input modulus) input base size hz (by omega) (by decide) h4
    (by omega) hw4)
  exact (rangeMask_relCT _ aboveOne).mono (fun _ _ h => forget_counter h) (fun _ _ h => h)

theorem validateEqual_relCT (len : Nat) (a b : Pointer) (base : Addr) (size : Nat)
    (hz : Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      OperandReady s base ((len + 7) / 8) a len ∧ OperandReady t base ((len + 7) / 8) a len ∧
      pointerValue base s a = pointerValue base t a ∧ pointerValue base s b = pointerValue base t b)
      (Validate.equalValues len a b) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Validate.equalValues
  dsimp only
  apply RelCT.assoc
  apply RelCT.seq (rawInputs_relCT _ len len 5 8 a b base size hz (by omega) (by decide) h4 (by omega) hw4)
  exact (equalMask_relCT _ _ _).mono (fun _ _ h => forget_counter h) (fun _ _ h => h)

theorem validateOne_relCT (len : Nat) (input : Pointer) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ pointerValue base s input = pointerValue base t input)
      (Validate.isOne len input) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Validate.isOne
  dsimp only
  apply RelCT.seq (coreLoad_relCT _ len _ input base size hz)
  have Tail := RelCT.seq (setConst_relCT (2 * ((len + 7) / 8)) (slot ((len + 7) / 8) 8) 1)
    (equalMask_relCT ((len + 7) / 8) (slot ((len + 7) / 8) 5) (slot ((len + 7) / 8) 8))
  exact Tail.mono (fun _ _ h => forget_counter h) (fun _ _ h => h)

theorem validateZero_relCT (len : Nat) (input : Pointer) (wantNonzero : Bool) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ pointerValue base s input = pointerValue base t input)
      (Validate.zero len input wantNonzero) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Validate.zero
  dsimp only
  apply RelCT.seq (coreLoad_relCT _ len _ input base size hz)
  exact (checkZero_relCT true _ _ _ wantNonzero).mono (fun _ _ h => h) (fun _ _ h => forget_counter h)

end VG.Proof.Dsa.X86
