module

public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Dsa.X86.Validate
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.RawInputsTiming
import VerifiedGarbage.Proof.Dsa.X86.ValidationBlocksTiming
import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
import VerifiedGarbage.Proof.Dsa.X86.ChecksTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.StageChecks

/-! ### `Dsa.X86.ValidationTiming`, which only this module used -/

section

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
  apply RelCT.seq (rawInputs_relCT _ len len 0 5 (.input modulus) input base size hz (by omega_using [hmax]) (by decide) h4
    (by omega_using []) hw4)
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
  apply RelCT.seq (rawInputs_relCT _ len len 5 8 a b base size hz (by omega_using [hmax]) (by decide) h4 (by omega_using []) hw4)
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

end

end


/-! # Validation stages retain the public call layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callRange_relCT (L : CallLayout) (len : Nat) (modulus : Field) (input : Pointer) (aboveOne : Bool)
    (M : CallOperand L (.input modulus) len) (I : CallOperand L input len) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (CallPair L) (Validate.range len modulus input aboveOne) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_
  · apply (validateRange_relCT len modulus input aboveOne L.base L.size L.saved h4 hmax hw4).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨H.1.moduli.scr, H.2.moduli.scr, H.1.operand M (by omega_using [h4]) (by omega_using [hmax]),
      H.2.operand M (by omega_using [h4]) (by omega_using [hmax]), H.pointer M, H.pointer I⟩
  · intro s R
    exact WP.mono (stageRange_ok R.moduli h4 hmax hw4 (R.operand M (by omega_using [h4]) (by omega_using [hmax]))
      (R.operand I (by omega_using [h4]) (by omega_using [hmax])) aboveOne) fun _ H => H.2.2.execution (.inr ⟨rfl, rfl⟩)

theorem callEqual_relCT (L : CallLayout) (len : Nat) (a b : Pointer)
    (A : CallOperand L a len) (B : CallOperand L b len) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (CallPair L) (Validate.equalValues len a b) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_
  · apply (validateEqual_relCT len a b L.base L.size L.saved h4 hmax hw4).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨H.1.moduli.scr, H.2.moduli.scr, H.1.operand A (by omega_using [h4]) (by omega_using [hmax]),
      H.2.operand A (by omega_using [h4]) (by omega_using [hmax]), H.pointer A, H.pointer B⟩
  · intro s R
    exact WP.mono (stageEqual_ok R.moduli h4 hmax hw4 (R.operand A (by omega_using [h4]) (by omega_using [hmax]))
      (R.operand B (by omega_using [h4]) (by omega_using [hmax]))) fun _ H => H.2.2.execution (.inr ⟨rfl, rfl⟩)

theorem callOne_relCT (L : CallLayout) (len : Nat) (input : Pointer)
    (I : CallOperand L input len) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (CallPair L) (Validate.isOne len input) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_
  · exact (validateOne_relCT len input L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.1.moduli.scr, H.2.moduli.scr, H.pointer I⟩) (fun _ _ h => h)
  · intro s R
    exact WP.mono (stageOne_ok R.moduli h4 hmax hw4 (R.operand I (by omega_using [h4]) (by omega_using [hmax])))
      fun _ H => H.2.2.execution (.inr ⟨rfl, rfl⟩)

theorem callZero_relCT (L : CallLayout) (len : Nat) (input : Pointer) (wantNonzero : Bool)
    (I : CallOperand L input len) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0) :
    RelCT isa (CallPair L) (Validate.zero len input wantNonzero) (CallPair L) := by
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint false)) ?_ ?_
  · exact (validateZero_relCT len input wantNonzero L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.1.moduli.scr, H.2.moduli.scr, H.pointer I⟩) (fun _ _ h => h)
  · intro s R
    exact WP.mono (stageZero_ok R.moduli h4 hmax hw4 (R.operand I (by omega_using [h4]) (by omega_using [hmax])) wantNonzero)
      fun _ H => H.2.2.execution (.inr ⟨rfl, rfl⟩)

end VG.Proof.Dsa.X86
