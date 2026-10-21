module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.CorePowerTiming
public import VerifiedGarbage.Proof.Dsa.X86.ScheduleFrame
public import VerifiedGarbage.Proof.Dsa.X86.CallTiming
import VerifiedGarbage.Proof.Dsa.X86.CallPowerTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.StagePower
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! Comb stages retain the common public caller layout. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem keepSchedule {L : CallLayout} {s t : State} (R : CallReady L s)
    (E : ScheduleFrame L.base L.size s t) : CallReady L t := by
  refine ⟨(E.keeps.1 .esp (by decide)).trans R.sp, E.moduli R.moduli, ?_, ?_, ?_⟩
  · intro input hi; exact E.buffer (R.buffers input hi) (L.stable input hi)
  · intro input hi; exact (E.pointer (L.stable input hi)).trans (R.pointers input hi)
  · exact (E.pointer (p := .input .digestPrefixLen) (by decide)).trans R.prefixLen

def StageAgree (prepare : Bool) (L : CallLayout) (a b : Pointer) (s t : State) : Prop :=
  CallPair L s t ∧
  (prepare=true → operandValue s L.base a L.pLen=operandValue t L.base a L.pLen ∧
    operandValue s L.base b L.qLen=operandValue t L.base b L.qLen) ∧
  (prepare=false → canonical ((L.pLen+7)/8) ((L.qLen+3)/4) L.p
    (operandValue s L.base a L.pLen) L.base s.mem ∧
    canonical ((L.pLen+7)/8) ((L.qLen+3)/4) L.p
      (operandValue t L.base a L.pLen) L.base t.mem)

theorem stagePower_relCT (prepare : Bool) (L : CallLayout) (a b : Pointer) (output : Nat)
    (P : CallOperand L (.input .p) L.pLen) (A : CallOperand L a L.pLen) (B : CallOperand L b L.qLen)
    (ho : output∈Layout.wideValues)
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (StageAgree prepare L a b) (power prepare L.pLen L.qLen .p a b output) (CallPair L) := by
  have W := L.lengths
  intro s t tr ur sf tf H E F
  have Pair := H.1
  have CT := corePower_relCT prepare L.base L.size L.pLen L.qLen output .p a b
    (supported_widths L.widths) L.saved L.extent (by omega) (by omega) L.aligned.1
    (by omega) (by omega) L.aligned.2 fits
  have M := Pair.1.moduli.pValue.trans Pair.2.moduli.pValue.symm
  have Trace := (CT _ _ _ _ _ _ ⟨⟨⟨Pair.1.arithmeticP A B (by omega),
    Pair.2.arithmeticP A B (by omega),Pair.pointer P,Pair.pointer A,Pair.pointer B⟩,
    Pair.1.moduli.room,Pair.2.moduli.room,Pair.1.sp.trans Pair.2.sp.symm⟩,
    fun eq => ⟨M,H.2.1 eq⟩,fun eq => by
      rw [Pair.1.moduli.pValue,Pair.2.moduli.pValue]; exact H.2.2 eq⟩ E F).1
  have S := wp_result (stagePower_ok prepare Pair.1.moduli
    (Pair.1.operand A (by omega) (by omega)) (Pair.1.operand B (by omega) (by omega)) ho fits
    (fun eq => (H.2.2 eq).1)) E
  have T := wp_result (stagePower_ok prepare Pair.2.moduli
    (Pair.2.operand A (by omega) (by omega)) (Pair.2.operand B (by omega) (by omega)) ho fits
    (fun eq => (H.2.2 eq).2)) F
  exact ⟨Trace,keepSchedule Pair.1 S.2.2.2.2.1,keepSchedule Pair.2 T.2.2.2.2.1⟩

end VG.Proof.Dsa.X86.Comb
