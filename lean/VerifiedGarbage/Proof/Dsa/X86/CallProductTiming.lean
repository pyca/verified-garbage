module
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming

import VerifiedGarbage.Proof.Dsa.X86.CallPowerTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreProductTiming
import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # Product stages retain public layout and caller operands -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem callProductP_relCT (L : CallLayout) (a b : Pointer) (output : Nat)
    (P : CallOperand L (.input .p) L.pLen) (A : CallOperand L a L.pLen) (B : CallOperand L b L.pLen)
    (ho : r ≤ output) (hb : output + L.pLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Core.productMod L.pLen .p a b output) (CallPair L) := by
  have W := L.lengths
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · apply (coreProductMod_relCT L.base L.size L.pLen output .p a b L.saved L.extent (by omega) (by omega)
      L.aligned.1).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨⟨H.1.arithmeticP A B (by omega), H.2.arithmeticP A B (by omega), H.pointer P, H.pointer A, H.pointer B⟩,
      H.1.moduli.room, H.2.moduli.room, H.1.sp.trans H.2.sp.symm⟩
  · intro s R
    exact WP.mono (stageProductP_ok R.moduli (R.operand A (by omega) (by omega))
      (R.operand B (by omega) (by omega)) ho hb) fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

theorem callProductQ_relCT (L : CallLayout) (a b : Pointer) (output : Nat)
    (Q : CallOperand L (.input .q) L.qLen) (A : CallOperand L a L.qLen) (B : CallOperand L b L.qLen)
    (ho : r ≤ output) (hb : output + L.qLen ≤ usedBytes) :
    RelCT isa (CallPair L) (Core.product L.qLen a b output) (CallPair L) := by
  have W := L.lengths
  refine call_stage (Q := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · apply (coreProductMod_relCT L.base L.size L.qLen output .q a b L.saved L.extent (by omega) (by omega)
      L.aligned.2).mono ?_ (fun _ _ h => h)
    intro s t H
    exact ⟨⟨H.1.arithmeticQ A B, H.2.arithmeticQ A B, H.pointer Q, H.pointer A, H.pointer B⟩,
      H.1.moduli.room, H.2.moduli.room, H.1.sp.trans H.2.sp.symm⟩
  · intro s R
    exact WP.mono (stageProduct_ok R.moduli (R.operand A (by omega) (by omega))
      (R.operand B (by omega) (by omega)) ho hb) fun _ H => H.2.toStageFrame.execution (.inl ⟨ho, hb⟩)

end VG.Proof.Dsa.X86
