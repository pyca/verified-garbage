module

public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
public import VerifiedGarbage.Proof.Dsa.X86.ArithmeticHead
import VerifiedGarbage.Proof.Dsa.X86.CorePowerTiming
import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # Exponentiation stages preserve a public call layout -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem CallReady.arithmeticP {L : CallLayout} {s : State} {a b : Pointer} {bl : Nat}
    (R : CallReady L s) (A : CallOperand L a L.pLen) (B : CallOperand L b bl) (hb : 0 < bl) :
    ArithmeticPre L.base L.size L.pLen bl .p a b s := by
  have W := L.lengths
  refine ⟨R.moduli.scr, R.moduli.pReady, R.operand A (by omega) (by omega), R.operand B hb (by omega), ?_, ?_⟩
  · change 1 < operandValue s L.base (.input .p) L.pLen
    rw [R.moduli.pValue]; exact R.moduli.pLarge
  · change operandValue s L.base (.input .p) L.pLen % 2 = 1
    rw [R.moduli.pValue]; exact R.moduli.pOdd

theorem CallReady.arithmeticQ {L : CallLayout} {s : State} {a b : Pointer}
    (R : CallReady L s) (A : CallOperand L a L.qLen) (B : CallOperand L b L.qLen) :
    ArithmeticPre L.base L.size L.qLen L.qLen .q a b s := by
  have W := L.lengths
  refine ⟨R.moduli.scr, R.moduli.qReady, R.operand A (by omega) (by omega), R.operand B (by omega) (by omega), ?_, ?_⟩
  · change 1 < operandValue s L.base (.input .q) L.qLen
    rw [R.moduli.qValue]; have := R.moduli.qLarge; omega
  · change operandValue s L.base (.input .q) L.qLen % 2 = 1
    rw [R.moduli.qValue]; exact R.moduli.qOdd

theorem callPowerP_relCT (L : CallLayout) (a b : Pointer) (output : Nat)
    (P : CallOperand L (.input .p) L.pLen) (A : CallOperand L a L.pLen) (B : CallOperand L b L.qLen)
    (ho : r ≤ output) (hb : output + L.pLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Core.power L.pLen L.qLen .p a b output) (CallPair L) := by
  have W := L.lengths
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · apply (corePower_relCT L.base L.size L.pLen L.qLen output .p a b L.saved L.extent
    (by omega) (by omega) L.aligned.1 (by omega) (by omega) L.aligned.2).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨⟨H.1.arithmeticP A B (by omega), H.2.arithmeticP A B (by omega), H.pointer P, H.pointer A, H.pointer B⟩,
      H.1.moduli.room, H.2.moduli.room, H.1.sp.trans H.2.sp.symm⟩
  · intro s R
    exact WP.mono (stagePowerP_ok R.moduli (R.operand A (by omega) (by omega))
      (R.operand B (by omega) (by omega)) ho hb) fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

theorem callPowerQ_relCT (L : CallLayout) (a b : Pointer) (output : Nat)
    (Q : CallOperand L (.input .q) L.qLen) (A : CallOperand L a L.qLen) (B : CallOperand L b L.qLen)
    (ho : r ≤ output) (hb : output + L.qLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Core.power L.qLen L.qLen .q a b output) (CallPair L) := by
  have W := L.lengths
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · apply (corePower_relCT L.base L.size L.qLen L.qLen output .q a b L.saved L.extent
    (by omega) (by omega) L.aligned.2 (by omega) (by omega) L.aligned.2).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨⟨H.1.arithmeticQ A B, H.2.arithmeticQ A B, H.pointer Q, H.pointer A, H.pointer B⟩,
      H.1.moduli.room, H.2.moduli.room, H.1.sp.trans H.2.sp.symm⟩
  · intro s R
    exact WP.mono (stagePowerQ_ok R.moduli (R.operand A (by omega) (by omega))
      (R.operand B (by omega) (by omega)) ho hb) fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

end VG.Proof.Dsa.X86
